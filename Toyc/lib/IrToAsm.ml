open Ir
open Regalloc  (* 集成寄存器分配模块 *)

let stack_offset = ref 0
let v_env = Hashtbl.create 1600

let get_sto var =
  try Hashtbl.find v_env var
  with Not_found -> failwith ("Unknown variable: " ^ var)

(* 变量是否已经在符号表里面了, 存在则直接返回偏移, 否则分配新偏移 *)
let all_st var =
  try get_sto var
  with _ ->
    stack_offset := !stack_offset + 4;
    Hashtbl.add v_env var !stack_offset;
    !stack_offset

let operand_str = function
  | Reg r | Var r -> Printf.sprintf "%d(sp)" (get_sto r)
  | Imm i -> Printf.sprintf "%d" i

let l_operand (reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r -> 
      (* 使用is_register_allocatable函数判断是否为可分配寄存器的变量 *)
      if is_register_allocatable r then
        match get_register r with
        | Some allocated_reg -> 
            (* 已经在寄存器中，只需移动到目标寄存器 *)
            if allocated_reg.name = reg then 
              "" (* 已经在正确的寄存器中，无需操作 *)
            else
              Printf.sprintf "\tmv %s, %s\n" reg allocated_reg.name
        | None -> 
            (* 不在寄存器中，从栈加载 *)
            Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto r)
      else
        (* 用户变量总是在栈上 *)
        Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto r)

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_off = all_st dst_name in
      
      (* 尝试为目标分配寄存器，使用is_register_allocatable判断 *)
      let dst_reg_opt = 
        if is_register_allocatable dst_name then
          allocate_register dst_name 
        else None
      in
      
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
      
      let store_code = 
        match dst_reg_opt with
        | Some reg -> 
            (* 如果成功分配寄存器，则将结果移动到寄存器，并同时写回栈 *)
            Printf.sprintf "\tmv %s, t0\n\tsw t0, %d(sp)\n" reg.name dst_off
        | None ->
            (* 否则只写回栈 *)
            Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
      in
      
      lhs_code ^ rhs_code ^ op_code ^ store_code
  | Unop (op, dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_off = all_st dst_name in
      
      (* 尝试为目标分配寄存器，使用is_register_allocatable判断 *)
      let dst_reg_opt = 
        if is_register_allocatable dst_name then
          allocate_register dst_name 
        else None
      in
      
      let load_src = l_operand "t1" src in
      let op_code =
        match op with
        | "-" -> "\tneg t0, t1\n"
        | "!" -> "\tseqz t0, t1\n"
        | "+" -> "\tmv t0, t1\n"
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      
      let store_code = 
        match dst_reg_opt with
        | Some reg -> 
            (* 如果成功分配寄存器，则将结果移动到寄存器，并同时写回栈 *)
            Printf.sprintf "\tmv %s, t0\n\tsw t0, %d(sp)\n" reg.name dst_off
        | None ->
            (* 否则只写回栈 *)
            Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
      in
      
      load_src ^ op_code ^ store_code
  | Assign (dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_off = all_st dst_name in
      
      (* 尝试为目标分配寄存器，使用is_register_allocatable判断 *)
      let dst_reg_opt = 
        if is_register_allocatable dst_name then
          allocate_register dst_name 
        else None
      in
      
      let load_src = l_operand "t0" src in
      
      let store_code = 
        match dst_reg_opt with
        | Some reg -> 
            (* 如果成功分配寄存器，则将结果移动到寄存器，并同时写回栈 *)
            Printf.sprintf "\tmv %s, t0\n\tsw t0, %d(sp)\n" reg.name dst_off
        | None ->
            (* 否则只写回栈 *)
            Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
      in
      
      load_src ^ store_code
  (* Not used *)
  | Load (dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_off = all_st dst_name in
      
      (* 尝试为目标分配寄存器，使用is_register_allocatable判断 *)
      let dst_reg_opt = 
        if is_register_allocatable dst_name then
          allocate_register dst_name 
        else None
      in
      
      let src_code = l_operand "t1" src in
      
      let store_code = 
        match dst_reg_opt with
        | Some reg -> 
            (* 如果成功分配寄存器，先加载到t0，然后移动到目标寄存器，并写回栈 *)
            Printf.sprintf "\tlw t0, 0(t1)\n\tmv %s, t0\n\tsw t0, %d(sp)\n" reg.name dst_off
        | None ->
            (* 否则直接加载和写回 *)
            Printf.sprintf "\tlw t0, 0(t1)\n\tsw t0, %d(sp)\n" dst_off
      in
      
      src_code ^ store_code
  (* Not used *)
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
  | Call (dst, fname, args) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_off = all_st dst_name in
      
      (* 函数调用前保存所有分配的寄存器，函数调用会破坏临时寄存器 *)
      (* 这里采用一个简单策略，直接释放所有寄存器 *)
      free_all_registers();
      
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
      
      (* 尝试为返回值分配寄存器，使用is_register_allocatable判断 *)
      let dst_reg_opt = 
        if is_register_allocatable dst_name then
          allocate_register dst_name 
        else None
      in
      
      let store_code = 
        match dst_reg_opt with
        | Some reg -> 
            (* 函数返回值在a0，如果有寄存器，移动到寄存器并写回栈 *)
            Printf.sprintf "\tcall %s\n\tmv %s, a0\n\tsw a0, %d(sp)\n" fname reg.name dst_off
        | None ->
            (* 否则只写回栈 *)
            Printf.sprintf "\tcall %s\n\tsw a0, %d(sp)\n" fname dst_off
      in
      
      args_code ^ store_code
  | Ret None ->
      let ra_offset = get_sto "ra" in
      (* 释放所有寄存器 *)
      free_all_registers();
      Printf.sprintf
        "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
        ra_offset
  | Ret (Some op) ->
      let load_code = l_operand "a0" op in
      let ra_offset = get_sto "ra" in
      (* 释放所有寄存器 *)
      free_all_registers();
      load_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          ra_offset
  | Goto label -> 
      (* 基本块边界应确保寄存器状态一致，为安全起见释放所有寄存器 *)
      free_all_registers();
      Printf.sprintf "\tj %s\n" label
  | IfGoto (cond, label) ->
      let cond_code = l_operand "t0" cond in
      (* 条件跳转之后，可能进入新的基本块，释放所有寄存器 *)
      free_all_registers();
      cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" label
  | Label label -> 
      (* 标签处是基本块的开始，确保寄存器状态一致 *)
      free_all_registers();
      Printf.sprintf "%s:\n" label

let com_block (blk : ir_block) : string =
  blk.insts |> List.map com_inst |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* 清空寄存器分配状态 *)
  free_all_registers();

  (* 参数入栈 *)
  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
        else
          Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
            (* offset 为 call 语句将第 i 个参数压入的偏移 *)
            (-4 * (i - 8))
            off)
      f.args
    |> String.concat ""
  in

  (* ra 入栈 *)
  let pae_set =
    pae_set ^ Printf.sprintf "\tsw ra, %d(sp)\n" (all_st "ra")
  in

  let body_code = f.body |> List.map com_inst |> String.concat "" in

  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then begin
      (* 函数结束前释放所有寄存器 *)
      free_all_registers();
      body_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    end else body_code
  in
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  prologue ^ pae_set ^ body_code

let com_func_o (f : ir_func_o) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* 清空寄存器分配状态 *)
  free_all_registers();

  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
        else
          Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
            (* offset 为 call 语句将第 i 个参数压入的偏移 *)
            (-4 * (i - 8))
            off)
      f.args
    |> String.concat ""
  in

  (* ra 入栈 *)
  let pae_set =
    pae_set ^ Printf.sprintf "\tsw ra, %d(sp)\n" (all_st "ra")
  in

  let body_code = f.blocks |> List.map com_block |> String.concat "" in

  (* 检查 body_code 是否以 ret 结束; 没有默认添加 "\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n" 语句; 其实可以前移到 IR 阶段 *)
  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then begin
      (* 函数结束前释放所有寄存器 *)
      free_all_registers();
      body_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    end else body_code
  in

  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  prologue ^ pae_set ^ body_code

let com_pro (prog : ir_program) : string =
  let prologue = ".text\n .global main\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map com_func funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o ->
        List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm
