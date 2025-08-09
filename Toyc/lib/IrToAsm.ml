open Ir

(* 寄存器分配相关 *)
type storage =
  | Stack of int       (* 栈上存储的位置 *)
  | Register of string (* 分配的寄存器 *)

(* 定义可用于分配的寄存器 *)
let available_regs = [
  "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6";  (* 临时寄存器 *)
  "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11" (* 保存寄存器 *)
]

let reg_pool = ref available_regs
let stack_offset = ref 0
let v_env = Hashtbl.create 1600
let is_temp_var name = String.starts_with ~prefix:"t" name && String.length name > 1

(* 为变量分配存储 *)
let alloc_storage var =
  (* 对临时变量优先分配寄存器 *)
  if is_temp_var var && List.length !reg_pool > 0 then
    let reg = List.hd !reg_pool in
    reg_pool := List.tl !reg_pool;
    Register reg
  else
    (* 其他变量或寄存器用完时，分配栈空间 *)
    let offset = !stack_offset + 4 in
    stack_offset := offset;
    Stack offset

(* 释放存储 *)
let free_storage var storage =
  match storage with
  | Register reg -> 
      (* 只回收临时变量的寄存器 *)
      if is_temp_var var then
        reg_pool := reg :: !reg_pool
  | Stack _ -> ()  (* 栈空间不回收 *)

let get_sto var =
  try Hashtbl.find v_env var
  with Not_found -> failwith ("Unknown variable: " ^ var)

(* 变量是否已经在符号表里面了, 存在则直接返回存储位置, 否则分配新存储 *)
let all_st var =
  try get_sto var
  with _ ->
    let storage = alloc_storage var in
    Hashtbl.add v_env var storage;
    storage

(* 将操作数转换为字符串表示 *)
let operand_str = function
  | Reg r | Var r -> 
      (match get_sto r with
       | Stack offset -> Printf.sprintf "%d(sp)" offset
       | Register reg -> reg)
  | Imm i -> Printf.sprintf "%d" i

(* 加载操作数到指定寄存器 *)
let l_operand (dest_reg : string) (op : operand) : string =
  match op with
  | Imm i -> 
      Printf.sprintf "\tli %s, %d\n" dest_reg i
  | Reg r | Var r -> 
      (match get_sto r with
       | Stack offset -> 
           Printf.sprintf "\tlw %s, %d(sp)\n" dest_reg offset
       | Register reg -> 
           if reg = dest_reg then
             "" (* 已经在目标寄存器中，无需加载 *)
           else
             Printf.sprintf "\tmv %s, %s\n" dest_reg reg)

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_storage = all_st dst_name in
      
      let lhs_code = l_operand "t1" lhs in
      let rhs_code = l_operand "t2" rhs in
      
      let result_reg = match dst_storage with
                       | Register reg -> reg
                       | _ -> "t0" in  (* 如果目标在栈上，用t0作为中间结果 *)
      
      let op_code =
        match op with
        | "+" -> Printf.sprintf "\tadd %s, t1, t2\n" result_reg
        | "-" -> Printf.sprintf "\tsub %s, t1, t2\n" result_reg
        | "*" -> Printf.sprintf "\tmul %s, t1, t2\n" result_reg
        | "/" -> Printf.sprintf "\tdiv %s, t1, t2\n" result_reg
        | "%" -> Printf.sprintf "\trem %s, t1, t2\n" result_reg
        | "==" -> Printf.sprintf "\tsub %s, t1, t2\n\tseqz %s, %s\n" result_reg result_reg result_reg
        | "!=" -> Printf.sprintf "\tsub %s, t1, t2\n\tsnez %s, %s\n" result_reg result_reg result_reg
        | "<=" -> Printf.sprintf "\tsgt %s, t1, t2\n\txori %s, %s, 1\n" result_reg result_reg result_reg
        | ">=" -> Printf.sprintf "\tslt %s, t1, t2\n\txori %s, %s, 1\n" result_reg result_reg result_reg
        | "<" -> Printf.sprintf "\tslt %s, t1, t2\n" result_reg
        | ">" -> Printf.sprintf "\tsgt %s, t1, t2\n" result_reg
        | "&&" -> Printf.sprintf "\tand %s, t1, t2\n" result_reg
        | "||" -> Printf.sprintf "\tor %s, t1, t2\n" result_reg
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      
      (* 如果结果不是直接在目标寄存器中，需要存储到目标位置 *)
      let store_code = match dst_storage with
                      | Register reg when reg = result_reg -> ""  (* 已经在正确的寄存器中 *)
                      | Register reg -> Printf.sprintf "\tmv %s, %s\n" reg result_reg
                      | Stack offset -> Printf.sprintf "\tsw %s, %d(sp)\n" result_reg offset
      in
      
      lhs_code ^ rhs_code ^ op_code ^ store_code
      
  | Unop (op, dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_storage = all_st dst_name in
      let load_src = l_operand "t1" src in
      
      let result_reg = match dst_storage with
                       | Register reg -> reg
                       | _ -> "t0" in
      
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg %s, t1\n" result_reg
        | "!" -> Printf.sprintf "\tseqz %s, t1\n" result_reg
        | "+" -> Printf.sprintf "\tmv %s, t1\n" result_reg
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      
      let store_code = match dst_storage with
                      | Register reg when reg = result_reg -> ""
                      | Register reg -> Printf.sprintf "\tmv %s, %s\n" reg result_reg
                      | Stack offset -> Printf.sprintf "\tsw %s, %d(sp)\n" result_reg offset
      in
      
      load_src ^ op_code ^ store_code
      
  | Assign (dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_storage = all_st dst_name in
      
      match (dst_storage, src) with
      | Register dst_reg, (Reg src_name | Var src_name) ->
          (match get_sto src_name with
           | Register src_reg -> Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
           | Stack offset -> Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg offset)
      | Register dst_reg, Imm i ->
          Printf.sprintf "\tli %s, %d\n" dst_reg i
      | Stack dst_offset, (Reg src_name | Var src_name) ->
          (match get_sto src_name with
           | Register src_reg -> Printf.sprintf "\tsw %s, %d(sp)\n" src_reg dst_offset
           | Stack src_offset ->
               if src_offset = dst_offset then ""  (* 相同位置，无需复制 *)
               else Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n" src_offset dst_offset)
      | Stack dst_offset, Imm i ->
          Printf.sprintf "\tli t0, %d\n\tsw t0, %d(sp)\n" i dst_offset
  (* Not used *)
  | Load (dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_storage = all_st dst_name in
      let src_code = l_operand "t1" src in
      
      let result_reg = match dst_storage with
                       | Register reg -> reg
                       | _ -> "t0" in
      
      let load_code = Printf.sprintf "\tlw %s, 0(t1)\n" result_reg in
      
      let store_code = match dst_storage with
                      | Register reg when reg = result_reg -> ""
                      | Register reg -> Printf.sprintf "\tmv %s, %s\n" reg result_reg
                      | Stack offset -> Printf.sprintf "\tsw %s, %d(sp)\n" result_reg offset
      in
      
      src_code ^ load_code ^ store_code
      
  (* Not used *)
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
      
  | Call (dst, fname, args) ->
      (* 保存所有正在使用的寄存器 *)
      let save_regs = 
        List.filter (fun reg -> not (List.mem reg !reg_pool)) available_regs
        |> List.mapi (fun i reg -> 
             Printf.sprintf "\tsw %s, %d(sp)\n" reg (!stack_offset + 4 + (i * 4)))
        |> String.concat ""
      in
      
      (* 函数调用前准备参数 *)
      let args_code =
        List.mapi
          (fun i arg ->
            if i < 8 then 
              (* 前8个参数通过寄存器传递 *)
              l_operand (Printf.sprintf "a%d" i) arg
            else
              (* 其余参数通过栈传递 *)
              let offset = 4 * (i - 8) in
              l_operand "t0" arg ^ 
              Printf.sprintf "\tsw t0, %d(sp)\n" (-1600 - offset))
          args
        |> String.concat ""
      in
      
      (* 函数调用 *)
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      
      (* 恢复寄存器 *)
      let restore_regs =
        List.filter (fun reg -> not (List.mem reg !reg_pool)) available_regs
        |> List.mapi (fun i reg -> 
             Printf.sprintf "\tlw %s, %d(sp)\n" reg (!stack_offset + 4 + (i * 4)))
        |> String.concat ""
      in
      
      (* 保存返回值 *)
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_storage = all_st dst_name in
      let save_result = match dst_storage with
                       | Register reg -> Printf.sprintf "\tmv %s, a0\n" reg
                       | Stack offset -> Printf.sprintf "\tsw a0, %d(sp)\n" offset
      in
      
      save_regs ^ args_code ^ call_code ^ restore_regs ^ save_result
      
  | Ret None ->
      let ra_storage = get_sto "ra" in
      let load_ra = match ra_storage with
                   | Register _ -> failwith "RA should be on stack"
                   | Stack offset -> Printf.sprintf "\tlw ra, %d(sp)\n" offset
      in
      
      (* 释放所有分配的寄存器 *)
      Hashtbl.iter (fun var storage -> free_storage var storage) v_env;
      
      load_ra ^ "\taddi sp, sp, 800\n\taddi sp, sp, 800\n\tret\n"
      
  | Ret (Some op) ->
      let load_code = l_operand "a0" op in
      let ra_storage = get_sto "ra" in
      let load_ra = match ra_storage with
                   | Register _ -> failwith "RA should be on stack"
                   | Stack offset -> Printf.sprintf "\tlw ra, %d(sp)\n" offset
      in
      
      (* 释放所有分配的寄存器 *)
      Hashtbl.iter (fun var storage -> free_storage var storage) v_env;
      
      load_code ^ load_ra ^ "\taddi sp, sp, 800\n\taddi sp, sp, 800\n\tret\n"
      
  | Goto label -> Printf.sprintf "\tj %s\n" label
  
  | IfGoto (cond, label) ->
      let cond_code = l_operand "t0" cond in
      cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" label
      
  | Label label -> Printf.sprintf "%s:\n" label

let com_block (blk : ir_block) : string =
  blk.insts |> List.map com_inst |> String.concat ""

let setup_function_args args =
  (* 重置寄存器池 *)
  reg_pool := available_regs;
  
  (* 保存RA到栈上 *)
  stack_offset := 4;  (* 预留第一个位置给ra *)
  Hashtbl.add v_env "ra" (Stack 4);
  
  (* 处理函数参数 *)
  List.mapi
    (fun i name ->
      (* 为参数分配存储 *)
      let storage = 
        if i < 8 then
          (* 参数已经在寄存器a0-a7中，我们可以直接使用或者移动到其他位置 *)
          let reg = Printf.sprintf "a%d" i in
          if is_temp_var name && List.length !reg_pool > 0 then
            (* 临时参数变量，分配一个寄存器 *)
            let target_reg = List.hd !reg_pool in
            reg_pool := List.tl !reg_pool;
            Hashtbl.add v_env name (Register target_reg);
            Printf.sprintf "\tmv %s, %s\n" target_reg reg
          else
            (* 常规参数变量，存储到栈上 *)
            stack_offset := !stack_offset + 4;
            Hashtbl.add v_env name (Stack !stack_offset);
            Printf.sprintf "\tsw %s, %d(sp)\n" reg !stack_offset
        else
          (* 超过8个的参数在调用者的栈上 *)
          stack_offset := !stack_offset + 4;
          let offset = !stack_offset in
          Hashtbl.add v_env name (Stack offset);
          Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
            (-4 * (i - 8))
            offset)
    args
  |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;

  (* 设置参数和返回地址 *)
  let pae_set = setup_function_args f.args in
  
  (* 保存ra *)
  let ra_save = "\tsw ra, 4(sp)\n" in
  
  let body_code = f.body |> List.map com_inst |> String.concat "" in

  (* 检查函数是否以ret结束，如果没有则添加默认返回 *)
  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code ^ "\tlw ra, 4(sp)\n\taddi sp, sp, 800\n\taddi sp, sp, 800\n\tret\n"
    else body_code
  in
  
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  prologue ^ ra_save ^ pae_set ^ body_code

let com_func_o (f : ir_func_o) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;

  (* 设置参数和返回地址 *)
  let pae_set = setup_function_args f.args in
  
  (* 保存ra *)
  let ra_save = "\tsw ra, 4(sp)\n" in
  
  let body_code = f.blocks |> List.map com_block |> String.concat "" in

  (* 检查函数是否以ret结束，如果没有则添加默认返回 *)
  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code ^ "\tlw ra, 4(sp)\n\taddi sp, sp, 800\n\taddi sp, sp, 800\n\tret\n"
    else body_code
  in
  
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  prologue ^ ra_save ^ pae_set ^ body_code

let com_pro (prog : ir_program) : string =
  let prologue = ".text\n .global main\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map com_func funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o ->
        List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm