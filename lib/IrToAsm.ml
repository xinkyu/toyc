(* IrToAsm.ml *)
open Ir

let v_env = Hashtbl.create 100
let stack_offset = ref 0

(* 分配栈空间 *)
let all_st name =
  match Hashtbl.find_opt v_env name with
  | Some off -> off
  | None ->
      let off = !stack_offset in
      stack_offset := !stack_offset + 4;
      Hashtbl.add v_env name off;
      off

(* 获取栈偏移 *)
let get_sto name =
  match Hashtbl.find_opt v_env name with
  | Some off -> off
  | None -> failwith ("Variable not found: " ^ name)

(* 加载操作数到寄存器 *)
let l_operand reg = function
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r ->
      let off = get_sto r in
      Printf.sprintf "\tlw %s, %d(sp)\n" reg off

(* 生成指令 *)
let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
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
      lhs_code ^ rhs_code ^ op_code ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | Unop (op, dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let load_src = l_operand "t1" src in
      let op_code =
        match op with
        | "-" -> "\tneg t0, t1\n"
        | "!" -> "\tseqz t0, t1\n"
        | "+" -> "\tmv t0, t1\n"
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      load_src ^ op_code ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | Call (dst, fname, args) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let save_args =
        List.mapi
          (fun i arg ->
            let load = l_operand "t0" arg in
            if i < 8 then load ^ Printf.sprintf "\tmv a%d, t0\n" i
            else
              load
              ^ Printf.sprintf "\tsw t0, %d(sp)\n" (-4 * (i - 8 + 1)))
          args
        |> String.concat ""
      in
      save_args ^ Printf.sprintf "\tcall %s\n" fname
      ^ Printf.sprintf "\tsw a0, %d(sp)\n" dst_off
  | Assign (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let load_src = l_operand "t0" src in
      load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | Load (dst, addr) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let load_addr = l_operand "t0" addr in
      load_addr ^ "\tlw t1, 0(t0)\n"
      ^ Printf.sprintf "\tsw t1, %d(sp)\n" dst_off
  | Store (addr, value) ->
      let load_addr = l_operand "t0" addr in
      let load_value = l_operand "t1" value in
      load_addr ^ load_value ^ "\tsw t1, 0(t0)\n"
  | Ret None -> "\tlw ra, %d(sp)\n\taddi sp, sp, 1600\n\tret\n"
  | Ret (Some op) ->
      let load = l_operand "a0" op in
      load ^ "\tlw ra, %d(sp)\n\taddi sp, sp, 1600\n\tret\n"
  | Label l -> Printf.sprintf "%s:\n" l
  | Goto l -> Printf.sprintf "\tj %s\n" l
  | IfGoto (cond, l) ->
      let load = l_operand "t0" cond in
      load ^ Printf.sprintf "\tbnez t0, %s\n" l

let com_block (blk : ir_block) : string =
  blk.insts |> List.map com_inst |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;

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
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    else body_code
  in
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  prologue ^ pae_set ^ body_code

let com_func_o (f : ir_func_o) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;

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
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    else body_code
  in

  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  prologue ^ pae_set ^ body_code

let com_pro (prog : ir_program) : string =
  let prologue = ".text\n .global main\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map com_func funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o -> List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm