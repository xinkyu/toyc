(* IrToAsm.ml *)
open Ir
open LinearScan

(*******************************************************************)
(* Optimized Code Generation (with Register Allocation) *)
(*******************************************************************)

(* Helper to align stack size to 16 bytes *)
let align_stack size =
  if size mod 16 == 0 then size
  else size + (16 - (size mod 16))

let load_operand allocation_map spill_base_offset target_reg op =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" target_reg i
  | Reg r | Var r ->
      match Hashtbl.find_opt allocation_map r with
      | Some (PhysicalRegister phys_reg) ->
          if phys_reg <> target_reg then
            Printf.sprintf "\tmv %s, %s\n" target_reg phys_reg
          else
            ""
      | Some (StackSlot offset) ->
          Printf.sprintf "\tlw %s, %d(sp)\n" target_reg (spill_base_offset + offset)
      | None -> "" (* Unused variable *)

let ensure_in_reg allocation_map spill_base_offset temp_reg op =
  match op with
  | Imm i -> (Printf.sprintf "\tli %s, %d\n" temp_reg i, temp_reg)
  | Reg r | Var r ->
      match Hashtbl.find_opt allocation_map r with
      | Some (PhysicalRegister phys_reg) -> ("", phys_reg)
      | Some (StackSlot offset) ->
          (Printf.sprintf "\tlw %s, %d(sp)\n" temp_reg (spill_base_offset + offset), temp_reg)
      | None -> ("", temp_reg)

let store_operand allocation_map spill_base_offset source_reg dst =
  match dst with
  | Imm _ -> failwith "Cannot assign to an immediate"
  | Reg r | Var r ->
      match Hashtbl.find_opt allocation_map r with
      | Some (PhysicalRegister phys_reg) ->
          if phys_reg <> source_reg then
            Printf.sprintf "\tmv %s, %s\n" phys_reg source_reg
          else
            ""
      | Some (StackSlot offset) ->
          Printf.sprintf "\tsw %s, %d(sp)\n" source_reg (spill_base_offset + offset)
      | None -> ""

let com_inst_o (inst : ir_inst) allocation_map spill_base_offset caller_save_base epilogue_label : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let code1, reg1 = ensure_in_reg allocation_map spill_base_offset "t5" lhs in
      let code2, reg2 = ensure_in_reg allocation_map spill_base_offset "t6" rhs in
      let op_code =
        match op with
        | "+" -> Printf.sprintf "\tadd t5, %s, %s\n" reg1 reg2
        | "-" -> Printf.sprintf "\tsub t5, %s, %s\n" reg1 reg2
        | "*" -> Printf.sprintf "\tmul t5, %s, %s\n" reg1 reg2
        | "/" -> Printf.sprintf "\tdiv t5, %s, %s\n" reg1 reg2
        | "%" -> Printf.sprintf "\trem t5, %s, %s\n" reg1 reg2
        | "==" -> Printf.sprintf "\tsub t5, %s, %s\n\tseqz t5, t5\n" reg1 reg2
        | "!=" -> Printf.sprintf "\tsub t5, %s, %s\n\tsnez t5, t5\n" reg1 reg2
        | "<=" -> Printf.sprintf "\tsgt t5, %s, %s\n\txori t5, t5, 1\n" reg1 reg2
        | ">=" -> Printf.sprintf "\tslt t5, %s, %s\n\txori t5, t5, 1\n" reg1 reg2
        | "<" -> Printf.sprintf "\tslt t5, %s, %s\n" reg1 reg2
        | ">" -> Printf.sprintf "\tsgt t5, %s, %s\n" reg1 reg2
        | "&&" -> Printf.sprintf "\tand t5, %s, %s\n" reg1 reg2
        | "||" -> Printf.sprintf "\tor t5, %s, %s\n" reg1 reg2
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      let store_code = store_operand allocation_map spill_base_offset "t5" dst in
      code1 ^ code2 ^ op_code ^ store_code
  | Unop (op, dst, src) ->
      let code1, reg1 = ensure_in_reg allocation_map spill_base_offset "t5" src in
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg t5, %s\n" reg1
        | "!" -> Printf.sprintf "\tseqz t5, %s\n" reg1
        | "+" -> ""
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      let effective_reg = if op = "+" then reg1 else "t5" in
      let store_code = store_operand allocation_map spill_base_offset effective_reg dst in
      code1 ^ op_code ^ store_code
  | Assign (dst, src) ->
      let code1, reg1 = ensure_in_reg allocation_map spill_base_offset "t5" src in
      let store_code = store_operand allocation_map spill_base_offset reg1 dst in
      code1 ^ store_code
   | Call (dst, fname, args) ->
      (* 添加t5,t6到必须保存的寄存器列表 *)
      let active_phys_regs =
        Hashtbl.fold (fun _ alloc acc ->
          match alloc with
          | PhysicalRegister r -> if List.mem r available_registers then r :: acc else acc
          | StackSlot _ -> acc
        ) allocation_map []
        |> List.append ["t5"; "t6"]  (* 关键修复 *)
        |> List.sort_uniq compare
      in
      
      (* 2. Save these active registers to the caller-save area *)
      let save_callers =
        List.mapi (fun i r -> Printf.sprintf "\tsw %s, %d(sp)\n" r (caller_save_base + i*4))
        active_phys_regs
        |> String.concat ""
      in

      (* 3. Set up arguments for the call *)
      let args_code =
        List.mapi (fun i arg ->
          if i < 8 then
            load_operand allocation_map spill_base_offset (Printf.sprintf "a%d" i) arg
          else
            let arg_code, reg = ensure_in_reg allocation_map spill_base_offset "t5" arg in
            arg_code ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg ((i-8)*4)
        ) args
        |> String.concat ""
      in

      (* 4. Restore the active registers after the call returns *)
      let restore_callers =
        List.mapi (fun i r -> Printf.sprintf "\tlw %s, %d(sp)\n" r (caller_save_base + i*4))
        active_phys_regs
        |> String.concat ""
      in

      (* 5. Store the result from a0 into its final destination *)
      let store_result = store_operand allocation_map spill_base_offset "a0" dst in

      save_callers ^ args_code ^ Printf.sprintf "\tcall %s\n" fname ^ restore_callers ^ store_result
  | Ret (Some op) ->
      let load_code = load_operand allocation_map spill_base_offset "a0" op in
      load_code ^ Printf.sprintf "\tj %s\n" epilogue_label
  | Ret None -> Printf.sprintf "\tj %s\n" epilogue_label
  | Goto label -> Printf.sprintf "\tj %s\n" label
  | IfGoto (cond, label) ->
      let cond_code, reg = ensure_in_reg allocation_map spill_base_offset "t5" cond in
      cond_code ^ Printf.sprintf "\tbne %s, x0, %s\n" reg label
  | Label label -> Printf.sprintf "%s:\n" label
  | Load _ | Store _ -> failwith "Load/Store IR instructions not supported"

let com_block_o (blk : ir_block) allocation_map spill_base_offset caller_save_base epilogue_label : string =
  (blk.label |> Printf.sprintf "%s:\n") ^
  (blk.insts |> List.map (fun i -> com_inst_o i allocation_map spill_base_offset caller_save_base epilogue_label) |> String.concat "")

let com_func_o (f : ir_func_o) : string =
  let intervals = LinearScan.build_intervals f in
  let allocation_map, num_spills = LinearScan.allocate intervals in

  (* Pre-scan for max outgoing stack arguments to reserve space *)
  let max_outgoing_stack_args = List.fold_left (fun current_max block ->
    List.fold_left (fun m inst ->
      match inst with
      | Call (_, _, args) -> max m (List.length args - 8)
      | _ -> m
    ) current_max block.insts
  ) 0 f.blocks
  in

  let outgoing_args_area = max 0 max_outgoing_stack_args * 4 in
  let caller_save_area = List.length available_registers * 4 in
  let spill_area = num_spills in
  let ra_area = 4 in
  let stack_size = align_stack (outgoing_args_area + caller_save_area + spill_area + ra_area) in
  
  (* Define base offsets for different areas relative to SP *)
  let _outgoing_args_base = 0 in
  let caller_save_base = outgoing_args_area in
  let ra_base = outgoing_args_area + caller_save_area in
  let spill_base_offset = outgoing_args_area + caller_save_area + ra_area in

  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -%d\n\tsw ra, %d(sp)\n"
    f.name stack_size ra_base
  in
  let args_code =
    List.mapi (fun i arg_name ->
      if i < 8 then
        (* Argument is in a register, store it to its assigned location (reg or spill slot) *)
        store_operand allocation_map spill_base_offset (Printf.sprintf "a%d" i) (Var arg_name)
      else
        (* Argument is on the stack. Load it into a temp reg, then store it. *)
        let arg_offset_on_stack = stack_size + ((i - 8) * 4) in
        let load_code = Printf.sprintf "\tlw t5, %d(sp)\n" arg_offset_on_stack in
        load_code ^ (store_operand allocation_map spill_base_offset "t5" (Var arg_name))
    ) f.args
    |> String.concat ""
  in
  let epilogue_label = f.name ^ "_epilogue" in

  let epilogue =
    Printf.sprintf "%s:\n\tlw ra, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
      epilogue_label ra_base stack_size
  in

  let body_code = f.blocks
    (* Pass the epilogue label down to the instruction compiler *)
    |> List.map (fun blk -> com_block_o blk allocation_map spill_base_offset caller_save_base epilogue_label)
    |> String.concat ""
  in

  prologue ^ args_code ^ body_code ^ epilogue

(*******************************************************************)
(* Original Non-Optimized Code Generation (Spill-Everything) *)
(*******************************************************************)

let com_func_non_opt (f : ir_func) : string =
  let v_env = Hashtbl.create 1600 in
  let stack_offset = ref 0 in
  let get_sto var = try Hashtbl.find v_env var with Not_found -> failwith ("Unknown variable: " ^ var) in
  
  let all_st var =
    try get_sto var
    with _ ->
      stack_offset := !stack_offset + 4;
      Hashtbl.add v_env var !stack_offset;
      !stack_offset
  in
  let l_operand reg op =
    match op with
    | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
    | Reg r | Var r -> Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto r)
  in
  let com_inst_non_opt (inst : ir_inst) : string =
    match inst with
    | Binop (op, dst, lhs, rhs) ->
        let dst_off = all_st (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
        let lhs_code = l_operand "t1" lhs in
        let rhs_code = l_operand "t2" rhs in
        let op_code =
          match op with
          | "+" -> "\tadd t0, t1, t2\n"
          | "-" -> "\tsub t0, t1, t2\n"
          | "*" -> "\tmul t0, t1, t2\n"
          | "/" -> "\tdiv t0, t1, t2\n"
          | "%" -> "\trem t0, t1, t2\n"
          | "==" -> "\tsub t0, t1, t2\n\tseqz t0, t0\n"
          | "!=" -> "\tsub t0, t1, t2\n\tsnez t0, t0\n"
          | "<=" -> "\tsgt t0, t1, t2\n\txori t0, t0, 1\n"
          | ">=" -> "\tslt t0, t1, t2\n\txori t0, t0, 1\n"
          | "<" -> "\tslt t0, t1, t2\n"
          | ">" -> "\tsgt t0, t1, t2\n"
          | "&&" -> "\tand t0, t1, t2\n"
          | "||" -> "\tor t0, t1, t2\n"
          | _ -> failwith ("Unknown binop: " ^ op)
        in
        lhs_code ^ rhs_code ^ op_code ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
    | Unop (op, dst, src) ->
        let dst_off = all_st (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
        let load_src = l_operand "t1" src in
        let op_code =
          match op with
          | "-" -> "\tneg t0, t1\n"
          | "!" -> "\tseqz t0, t1\n"
          | "+" -> "\tmv t0, t1\n"
          | _ -> failwith ("Unknown unop: " ^ op)
        in
        load_src ^ op_code ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
    | Assign (dst, src) ->
        let dst_off = all_st (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
        let load_src = l_operand "t0" src in
        load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
    | Call (dst, fname, args) ->
        let dst_off = all_st (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
        let args_code =
          List.mapi
            (fun i arg ->
              if i < 8 then l_operand (Printf.sprintf "a%d" i) arg
              else
                let offset = 4 * (i - 8) in
                l_operand "t0" arg ^ Printf.sprintf "\tsw t0, %d(sp)\n" (-1600 - offset))
            args
          |> String.concat ""
        in
        args_code ^ Printf.sprintf "\tcall %s\n\tsw a0, %d(sp)\n" fname dst_off
    | Ret None -> Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 1600\n\tret\n" (get_sto "ra")
    | Ret (Some op) ->
        let load_code = l_operand "a0" op in
        load_code ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 1600\n\tret\n" (get_sto "ra")
    | Goto label -> Printf.sprintf "\tj %s\n" label
    | IfGoto (cond, label) ->
        let cond_code = l_operand "t0" cond in
        cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" label
    | Label label -> Printf.sprintf "%s:\n" label
    | Load _ | Store _ -> failwith "Load/Store IR instructions not supported"
  in
  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
        else
          Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n" (-4 * (i - 8)) off)
      f.args
    |> String.concat ""
  in
  let pae_set = pae_set ^ Printf.sprintf "\tsw ra, %d(sp)\n" (all_st "ra") in
  let body_code = f.body |> List.map com_inst_non_opt |> String.concat "" in
  let body_code = 
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 1600\n\tret\n" (get_sto "ra")
    else body_code
  in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" f.name in
  prologue ^ pae_set ^ body_code

(*******************************************************************)
(* Program Entry Point *) 
(*******************************************************************)

let com_pro (prog : ir_program) : string =
  let prologue = ".text\n.global main\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map com_func_non_opt funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o -> List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm