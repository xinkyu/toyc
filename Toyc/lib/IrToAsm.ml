open Ir
open RegAlloc
open Liveness

module StringMap = Map.Make(String)

type func_context = {
  alloc_map: (string, allocation_location) Hashtbl.t;
  var_offsets: (string, int) Hashtbl.t;
  live_out_map: StringSet.t StringMap.t;
  inst_map: ir_inst IntMap.t;
  mutable current_inst_id: int;
}

let temp_regs = ["t5"; "t6"]
let caller_saved_regs = Array.to_list (Array.init 7 (fun i -> "t" ^ string_of_int i)) @ Array.to_list (Array.init 8 (fun i -> "a" ^ string_of_int i))

let load_operand (ctx: func_context) (op: operand) (target_reg: string) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" target_reg i
  | Reg r | Var r ->
      (match Hashtbl.find_opt ctx.alloc_map r with
      | Some (InReg reg) ->
          if reg <> target_reg then Printf.sprintf "\tmv %s, %s\n" target_reg reg else ""
      | Some (Spilled _) ->
          let offset = Hashtbl.find ctx.var_offsets r in
          Printf.sprintf "\tlw %s, %d(sp)\n" target_reg offset
      | None -> ""
      )

let store_operand (ctx: func_context) (dst: operand) (source_reg: string) : string =
  match dst with
  | Reg r | Var r ->
      (match Hashtbl.find_opt ctx.alloc_map r with
      | Some (InReg reg) ->
          if reg <> source_reg then Printf.sprintf "\tmv %s, %s\n" reg source_reg else ""
      | Some (Spilled _) ->
          let offset = Hashtbl.find ctx.var_offsets r in
          Printf.sprintf "\tsw %s, %d(sp)\n" source_reg offset
      | None -> ""
      )
  | _ -> failwith "Destination of an operation must be a variable or register"

let com_inst (ctx: func_context) (inst: ir_inst) : string =
  ctx.current_inst_id <- ctx.current_inst_id + 2;
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let t1, t2 = List.hd temp_regs, List.nth temp_regs 1 in
      let code1 = load_operand ctx lhs t1 in
      let code2 = load_operand ctx rhs t2 in
      let op_code = match op with
        | "+" -> Printf.sprintf "\tadd %s, %s, %s\n" t1 t1 t2 | "-" -> Printf.sprintf "\tsub %s, %s, %s\n" t1 t1 t2
        | "*" -> Printf.sprintf "\tmul %s, %s, %s\n" t1 t1 t2 | "/" -> Printf.sprintf "\tdiv %s, %s, %s\n" t1 t1 t2
        | "%" -> Printf.sprintf "\trem %s, %s, %s\n" t1 t1 t2 | "==" -> Printf.sprintf "\tsub %s, %s, %s\n\tseqz %s, %s\n" t1 t1 t2 t1 t1
        | "!=" -> Printf.sprintf "\tsub %s, %s, %s\n\tsnez %s, %s\n" t1 t1 t2 t1 t1 | "<=" -> Printf.sprintf "\tsgt %s, %s, %s\n\txori %s, %s, 1\n" t1 t1 t2 t1 t1
        | ">=" -> Printf.sprintf "\tslt %s, %s, %s\n\txori %s, %s, 1\n" t1 t1 t2 t1 t1 | "<" -> Printf.sprintf "\tslt %s, %s, %s\n" t1 t1 t2
        | ">" -> Printf.sprintf "\tsgt %s, %s, %s\n" t1 t1 t2 | _ -> failwith ("Unknown binop: " ^ op)
      in
      let store_code = store_operand ctx dst t1 in
      code1 ^ code2 ^ op_code ^ store_code
  | Unop (op, dst, src) ->
      let t1 = List.hd temp_regs in
      let load_code = load_operand ctx src t1 in
      let op_code = match op with
        | "-" -> Printf.sprintf "\tneg %s, %s\n" t1 t1 | "!" -> Printf.sprintf "\tseqz %s, %s\n" t1 t1
        | "+" -> "" | _ -> failwith ("Unknown unop: " ^ op)
      in
      let store_code = store_operand ctx dst t1 in
      load_code ^ op_code ^ store_code
  | Assign (dst, src) ->
      let t1 = List.hd temp_regs in
      let load_code = load_operand ctx src t1 in
      let store_code = store_operand ctx dst t1 in
      load_code ^ store_code
  | Call (dst, fname, args) ->
      (* FIX: Implement correct caller-save/restore logic *)
      let live_after_call = try StringMap.find (string_of_int (ctx.current_inst_id + 2)) ctx.live_out_map with Not_found -> StringSet.empty in
      let regs_to_save = Hashtbl.fold (fun var loc acc ->
        if StringSet.mem var live_after_call then
          match loc with
          | InReg reg when List.mem reg caller_saved_regs -> (reg, var) :: acc
          | _ -> acc
        else acc
      ) ctx.alloc_map [] in
      let save_code = List.map (fun (reg, var) ->
        let offset = Hashtbl.find ctx.var_offsets var in
        Printf.sprintf "\tsw %s, %d(sp)\n" reg offset
      ) regs_to_save |> String.concat "" in
      let restore_code = List.map (fun (reg, var) ->
        let offset = Hashtbl.find ctx.var_offsets var in
        Printf.sprintf "\tlw %s, %d(sp)\n" reg offset
      ) regs_to_save |> String.concat "" in
      let args_code = List.mapi (fun i arg ->
          if i < 8 then load_operand ctx arg ("a" ^ string_of_int i) else ""
        ) args |> String.concat "" in
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      let ret_code = store_operand ctx dst "a0" in
      save_code ^ args_code ^ call_code ^ restore_code ^ ret_code
  | Ret (Some op) -> load_operand ctx op "a0"
  | Ret None -> ""
  | Label label -> Printf.sprintf "%s:\n" label
  | _ -> ""

let com_func_o (f: ir_func_o) : string =
  let live_in, live_out = Liveness.analyze f in
  let intervals = build_intervals f live_in live_out in
  let alloc_map = linear_scan_allocate intervals in
  let inst_map, _ = number_instructions f in
  let spill_vars = Hashtbl.fold (fun var loc acc -> match loc with Spilled _ -> var :: acc | _ -> acc) alloc_map [] in
  let spill_count = List.length spill_vars in
  let frame_size = 4 * (spill_count + 1) in
  let frame_size = if frame_size mod 16 <> 0 then frame_size + (16 - frame_size mod 16) else frame_size in
  let var_offsets = Hashtbl.create 100 in
  let ra_offset = frame_size - 4 in
  List.iteri (fun i var -> Hashtbl.add var_offsets var (frame_size - 4 * (i + 2))) (List.sort String.compare spill_vars);
  let live_out_at_inst =
    IntMap.fold (fun id inst acc ->
      let live_after = try StringMap.find (string_of_int (id + 2)) live_out with Not_found -> StringSet.empty in
      StringMap.add (string_of_int id) live_after acc
    ) inst_map StringMap.empty
  in
  let ctx = { alloc_map; var_offsets; live_out_map = live_out_at_inst; inst_map; current_inst_id = -2 } in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, %d\n\tsw ra, %d(sp)\n" f.name (-frame_size) ra_offset in
  let args_setup = List.mapi (fun i arg_name -> store_operand ctx (Var arg_name) ("a" ^ string_of_int i)) f.args |> String.concat "" in
  let body_code = List.map (fun (b: ir_block) ->
    ctx.current_inst_id <- (let start, _ = RegAlloc.number_instructions {f with blocks=[b]} |> snd |> Hashtbl.find b.label in start) - 2;
    let insts_code = List.map (com_inst ctx) b.insts |> String.concat "" in
    let term_code = match b.terminator with
      | TermGoto l -> Printf.sprintf "\tj %s\n" l
      | TermIf (cond, l1, l2) ->
          let t1 = List.hd temp_regs in
          let cond_code = load_operand ctx cond t1 in
          cond_code ^ Printf.sprintf "\tbnez %s, %s\n\tj %s\n" t1 l1 l2
      | TermRet op ->
          let ret_load = match op with Some o -> load_operand ctx o "a0" | None -> "" in
          ret_load ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, %d\n\tret\n" ra_offset frame_size
      | _ -> ""
    in
    (Printf.sprintf "%s:\n" b.label) ^ insts_code ^ term_code
  ) f.blocks |> String.concat "" in
  prologue ^ args_setup ^ body_code

let com_pro (prog: ir_program) : string =
  let prologue = ".text\n.global main\n" in
  let body_asm = match prog with
    | Ir_funcs_o funcs_o -> List.map com_func_o funcs_o |> String.concat "\n"
    | Ir_funcs _ -> failwith "Non-optimized path not supported"
  in
  prologue ^ body_asm
