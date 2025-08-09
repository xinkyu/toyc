open Ir
open RegAlloc

(*
 * IrToAsm.ml: 重构后的代码生成器
 *
 * 这个模块利用寄存器分配的结果，将优化后的 IR 翻译成高效的 RISC-V 汇编代码。
 * 这是性能提升的最终实现步骤。
 *)

(* 辅助数据结构 *)
module StringMap = Map.Make(String)

(* 保存当前函数的上下文信息 *)
type func_context = {
  alloc_map: (string, allocation_location) Hashtbl.t; (* 寄存器分配结果 *)
  var_offsets: (string, int) Hashtbl.t; (* 变量到栈偏移的映射 *)
}

(* RISC-V 临时寄存器，用于指令生成时的中间计算 *)
let temp_regs = ["t5"; "t6"]

(*
 * load_operand: 将一个 IR 操作数加载到一个物理寄存器中
 * 如果操作数是立即数，使用 `li`
 * 如果是已分配寄存器的变量，使用 `mv`
 * 如果是溢出的变量，从栈上 `lw` 到指定的物理寄存器
 *)
let load_operand (ctx: func_context) (op: operand) (target_reg: string) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" target_reg i
  | Reg r | Var r ->
      (match Hashtbl.find_opt ctx.alloc_map r with
      | Some (InReg reg) ->
          if reg <> target_reg then Printf.sprintf "\tmv %s, %s\n" target_reg reg
          else "" (* Avoid mv a, a *)
      | Some (Spilled _) ->
          let offset = Hashtbl.find ctx.var_offsets r in
          Printf.sprintf "\tlw %s, %d(sp)\n" target_reg offset
      | None -> "" (* Should not happen for function arguments or non-live vars *)
      )

(*
 * store_operand: 将一个物理寄存器中的值存回目标操作数
 * 如果目标在寄存器中，使用 `mv`
 * 如果目标被溢出，使用 `sw` 存回栈
 *)
let store_operand (ctx: func_context) (dst: operand) (source_reg: string) : string =
  match dst with
  | Reg r | Var r ->
      (match Hashtbl.find_opt ctx.alloc_map r with
      | Some (InReg reg) ->
          if reg <> source_reg then Printf.sprintf "\tmv %s, %s\n" reg source_reg
          else "" (* Avoid mv a, a *)
      | Some (Spilled _) ->
          let offset = Hashtbl.find ctx.var_offsets r in
          Printf.sprintf "\tsw %s, %d(sp)\n" source_reg offset
      | None -> ""
      )
  | _ -> failwith "Destination of an operation must be a variable or register"

(* 生成单条指令的汇编 *)
let com_inst (ctx: func_context) (inst: ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let t1, t2 = List.hd temp_regs, List.nth temp_regs 1 in
      let code1 = load_operand ctx lhs t1 in
      let code2 = load_operand ctx rhs t2 in
      let op_code =
        match op with
        | "+" -> Printf.sprintf "\tadd %s, %s, %s\n" t1 t1 t2
        | "-" -> Printf.sprintf "\tsub %s, %s, %s\n" t1 t1 t2
        | "*" -> Printf.sprintf "\tmul %s, %s, %s\n" t1 t1 t2
        | "/" -> Printf.sprintf "\tdiv %s, %s, %s\n" t1 t1 t2
        | "%" -> Printf.sprintf "\trem %s, %s, %s\n" t1 t1 t2
        | "==" -> Printf.sprintf "\tsub %s, %s, %s\n\tseqz %s, %s\n" t1 t1 t2 t1 t1
        | "!=" -> Printf.sprintf "\tsub %s, %s, %s\n\tsnez %s, %s\n" t1 t1 t2 t1 t1
        | "<=" -> Printf.sprintf "\tsgt %s, %s, %s\n\txori %s, %s, 1\n" t1 t1 t2 t1 t1
        | ">=" -> Printf.sprintf "\tslt %s, %s, %s\n\txori %s, %s, 1\n" t1 t1 t2 t1 t1
        | "<" -> Printf.sprintf "\tslt %s, %s, %s\n" t1 t1 t2
        | ">" -> Printf.sprintf "\tsgt %s, %s, %s\n" t1 t1 t2
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      let store_code = store_operand ctx dst t1 in
      code1 ^ code2 ^ op_code ^ store_code
  | Unop (op, dst, src) ->
      let t1 = List.hd temp_regs in
      let load_code = load_operand ctx src t1 in
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg %s, %s\n" t1 t1
        | "!" -> Printf.sprintf "\tseqz %s, %s\n" t1 t1
        | "+" -> "" (* mv is handled by load_operand *)
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      let store_code = store_operand ctx dst t1 in
      load_code ^ op_code ^ store_code
  | Assign (dst, src) ->
      let t1 = List.hd temp_regs in
      let load_code = load_operand ctx src t1 in
      let store_code = store_operand ctx dst t1 in
      load_code ^ store_code
  | Call (dst, fname, args) ->
      (* Note: This simplified version doesn't handle saving caller-saved registers *)
      let args_code =
        List.mapi (fun i arg ->
          if i < 8 then
            load_operand ctx arg ("a" ^ string_of_int i)
          else
            (* Stack-passed arguments need more complex handling *)
            ""
        ) args |> String.concat ""
      in
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      let ret_code = store_operand ctx dst "a0" in
      args_code ^ call_code ^ ret_code
  | Ret (Some op) ->
      load_operand ctx op "a0"
  | Ret None -> ""
  | Goto label -> Printf.sprintf "\tj %s\n" label
  | IfGoto (cond, label) ->
      let t1 = List.hd temp_regs in
      let cond_code = load_operand ctx cond t1 in
      cond_code ^ Printf.sprintf "\tbnez %s, %s\n" t1 label
  | Label label -> Printf.sprintf "%s:\n" label
  | _ -> "" (* Other instructions like Load/Store might need specific handling if used *)

(* 生成单个函数的汇编 *)
let com_func_o (f: ir_func_o) : string =
  (* 1. 执行分析和分配 *)
  let live_in, live_out = Liveness.analyze f in
  let intervals = build_intervals f live_in live_out in
  let alloc_map = linear_scan_allocate intervals in

  (* 2. 计算栈帧大小和变量偏移 *)
  let spill_count = Hashtbl.fold (fun _ loc acc -> match loc with Spilled _ -> acc + 1 | _ -> acc) alloc_map 0 in
  let frame_size = 4 * (spill_count + 1) in (* +1 for 'ra' *)
  let frame_size = if frame_size mod 16 <> 0 then frame_size + (16 - frame_size mod 16) else frame_size in

  let var_offsets = Hashtbl.create 100 in
  let ra_offset = frame_size - 4 in
  Hashtbl.iter (fun var loc ->
    match loc with
    | Spilled spill_index ->
        (* spill_index 0 is the first spilled var. It goes after ra. *)
        let offset = frame_size - 4 * (spill_index + 2) in
        Hashtbl.add var_offsets var offset
    | _ -> ()
  ) alloc_map;

  let ctx = {
    alloc_map = alloc_map;
    var_offsets = var_offsets;
  } in

  (* 3. 函数序言 *)
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, %d\n\tsw ra, %d(sp)\n" f.name (-frame_size) ra_offset in

  (* 4. 处理函数参数 *)
  let args_setup = List.mapi (fun i arg_name ->
    store_operand ctx (Var arg_name) ("a" ^ string_of_int i)
  ) f.args |> String.concat "" in

  (* 5. 生成函数体代码 *)
  let body_code = List.map (fun (b: ir_block) ->
    let insts_code = List.map (com_inst ctx) b.insts |> String.concat "" in
    let term_code =
      match b.terminator with
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

(* 编译整个程序 *)
let com_pro (prog: ir_program) : string =
  let prologue = ".text\n.global main\n" in
  let body_asm =
    match prog with
    | Ir_funcs_o funcs_o -> List.map com_func_o funcs_o |> String.concat "\n"
    | Ir_funcs _ -> failwith "Code generation for non-optimized IR is not supported in this path."
  in
  prologue ^ body_asm
