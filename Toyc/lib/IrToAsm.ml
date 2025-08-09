open Ir

(* 寄存器分配相关 *)
type storage =
  | Stack of int (* 栈上存储的偏移量, 相对于fp *)
  | Register of string (* 分配的物理寄存器 *)

(* RISC-V 寄存器分类 *)
(* 可供分配的临时寄存器 *)
let temp_regs =
  [ "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6" ]
(* 调用者保存, 函数调用时需要我们自己保存 *)
let caller_saved_regs =
  temp_regs @ [ "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" ]
(* 被调用者保存, 函数调用时 callee 会保证其值不变 *)
let callee_saved_regs =
  [ "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11" ]

(*
  为每个函数维护一个上下文，取代之前的全局变量
  这使得函数间的编译过程完全独立
*)
type func_ctx = {
  mutable stack_size : int; (* 当前函数需要的栈大小 *)
  mutable v_env : (string, storage) Hashtbl.t; (* 变量名 -> 存储位置 *)
  mutable reg_pool : string list; (* 当前可用的临时寄存器池 *)
}

(* 初始化函数上下文 *)
let init_func_ctx () =
  {
    stack_size = 0; (* 从0开始，动态计算 *)
    v_env = Hashtbl.create 64;
    reg_pool = temp_regs;
  }

(* 在栈上为变量分配空间，返回的是相对于fp的偏移 *)
let alloc_on_stack ctx var_name =
  ctx.stack_size <- ctx.stack_size + 4;
  let offset = -ctx.stack_size in
  let storage = Stack offset in
  Hashtbl.add ctx.v_env var_name storage;
  storage

(* 获取变量的存储位置 *)
let get_sto ctx var =
  try Hashtbl.find ctx.v_env var
  with Not_found ->
    failwith ("Unknown variable in get_sto: " ^ var)

(*
  加载操作数到指定的物理寄存器 (dest_reg)
  这是代码生成的核心辅助函数之一
*)
let l_operand ctx dest_reg (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" dest_reg i
  | Reg r | Var r -> (
      match get_sto ctx r with
      | Stack offset -> Printf.sprintf "\tlw %s, %d(fp)\n" dest_reg offset
      | Register reg ->
          if reg <> dest_reg then Printf.sprintf "\tmv %s, %s\n" dest_reg reg
          else "" (* 已经在目标寄存器，无需移动 *))

(*
  将源寄存器 (src_reg) 的值存回操作数 (op) 的最终位置
*)
let s_operand ctx src_reg (op : operand) : string =
  match op with
  | Imm _ -> failwith "Cannot store to an immediate"
  | Reg r | Var r -> (
      match get_sto ctx r with
      | Stack offset -> Printf.sprintf "\tsw %s, %d(fp)\n" src_reg offset
      | Register reg ->
          if reg <> src_reg then Printf.sprintf "\tmv %s, %s\n" reg src_reg
          else "" (* 已经在目标寄存器，无需移动 *))

(*
  新版指令翻译函数
  - 使用 ctx 来管理状态
  - 动态获取和释放临时寄存器
*)
let com_inst (ctx : func_ctx) (inst : ir_inst) : string =
  let get_temp_reg () =
    match ctx.reg_pool with
    | [] -> failwith "Out of temporary registers"
    | reg :: rest ->
        ctx.reg_pool <- rest;
        reg
  in
  let free_temp_reg reg = ctx.reg_pool <- reg :: ctx.reg_pool in

  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let t1 = get_temp_reg () in
      let t2 = get_temp_reg () in
      let code_lhs = l_operand ctx t1 lhs in
      let code_rhs = l_operand ctx t2 rhs in

      let op_code =
        match op with
        | "+" -> Printf.sprintf "\tadd %s, %s, %s\n" t1 t1 t2
        | "-" -> Printf.sprintf "\tsub %s, %s, %s\n" t1 t1 t2
        | "*" -> Printf.sprintf "\tmul %s, %s, %s\n" t1 t1 t2
        | "/" -> Printf.sprintf "\tdiv %s, %s, %s\n" t1 t1 t2
        | "%" -> Printf.sprintf "\trem %s, %s, %s\n" t1 t1 t2
        | "==" -> Printf.sprintf "\tsub %s, %s, %s\n\tseqz %s, %s\n" t1 t1 t2 t1 t1
        | "!=" -> Printf.sprintf "\tsub %s, %s, %s\n\tsnez %s, %s\n" t1 t1 t2 t1 t1
        | "<" -> Printf.sprintf "\tslt %s, %s, %s\n" t1 t1 t2
        | "<=" -> Printf.sprintf "\tsgt %s, %s, %s\n\txori %s, %s, 1\n" t1 t2 t1 t1 t1
        | ">" -> Printf.sprintf "\tsgt %s, %s, %s\n" t1 t1 t2
        | ">=" -> Printf.sprintf "\tslt %s, %s, %s\n\txori %s, %s, 1\n" t1 t2 t1 t1 t1
        | "&&" -> Printf.sprintf "\tand %s, %s, %s\n" t1 t1 t2
        | "||" -> Printf.sprintf "\tor %s, %s, %s\n" t1 t1 t2
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      let store_code = s_operand ctx t1 dst in
      free_temp_reg t1;
      free_temp_reg t2;
      code_lhs ^ code_rhs ^ op_code ^ store_code

  | Unop (op, dst, src) ->
      let t1 = get_temp_reg () in
      let load_src = l_operand ctx t1 src in
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg %s, %s\n" t1 t1
        | "!" -> Printf.sprintf "\tseqz %s, %s\n" t1 t1
        | "+" -> "" (* +x is just x, no instruction needed *)
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      let store_code = s_operand ctx t1 dst in
      free_temp_reg t1;
      load_src ^ op_code ^ store_code

  | Assign (dst, src) ->
      let t1 = get_temp_reg () in
      let load_code = l_operand ctx t1 src in
      let store_code = s_operand ctx t1 dst in
      free_temp_reg t1;
      load_code ^ store_code

  | Call (dst, fname, args) ->
      (*
        在函数调用前，我们需要保存所有正在使用的 caller-saved 寄存器。
        但在我们这个更简单的模型中，我们分配的临时寄存器 (t0-t6) 都是 caller-saved。
        我们可以认为在 call 之前，所有 live 的值都已经在它们的主存位置（栈），
        临时寄存器可以安全地被覆盖。
        一个更完整的实现需要做活跃度分析来精确地保存/恢复。
        目前，我们假设临时寄存器池在调用前后是空的。
      *)
      
      (* 1. 将参数加载到 a0-a7 或栈上 *)
      let args_code =
        List.mapi
          (fun i arg ->
            if i < 8 then
              l_operand ctx (Printf.sprintf "a%d" i) arg
            else
              let t1 = get_temp_reg () in
              let offset = (i - 8) * 4 in
              let load_arg = l_operand ctx t1 arg in
              let store_arg = Printf.sprintf "\tsw %s, %d(sp)\n" t1 offset in
              free_temp_reg t1;
              load_arg ^ store_arg)
          args
        |> String.concat ""
      in

      (* 2. 函数调用 *)
      let call_code = Printf.sprintf "\tcall %s\n" fname in

      (* 3. 保存返回值 *)
      let save_result =
        match dst with
        | Reg r | Var r -> s_operand ctx "a0" dst
        | _ -> ""
      in
      args_code ^ call_code ^ save_result

  | Ret None -> "\tj .Lret_%s\n" (* 跳转到函数末尾的统一返回点 *)
  | Ret (Some op) ->
      let load_ret = l_operand ctx "a0" op in
      load_ret ^ "\tj .Lret_%s\n"

  | Goto label -> Printf.sprintf "\tj %s\n" label
  | IfGoto (cond, label) ->
      let t1 = get_temp_reg () in
      let load_cond = l_operand ctx t1 cond in
      let branch_code = Printf.sprintf "\tbnez %s, %s\n" t1 label in
      free_temp_reg t1;
      load_cond ^ branch_code
      
  | Label label -> Printf.sprintf "%s:\n" label
  | Load _ | Store _ -> " # Load/Store not implemented in this simplified version\n"


(* 编译一个基本块 *)
let com_block (ctx : func_ctx) (blk : ir_block) : string =
  let inst_codes = List.map (com_inst ctx) blk.insts |> String.concat "" in
  let term_code =
    match blk.terminator with
    | TermGoto l -> Printf.sprintf "\tj %s\n" l
    | TermIf (cond, l1, l2) ->
        let t1 = get_temp_reg () in
        let load_cond = l_operand ctx t1 cond in
        let branch_code = Printf.sprintf "\tbnez %s, %s\n" t1 l1 in
        free_temp_reg t1;
        load_cond ^ branch_code ^ Printf.sprintf "\tj %s\n" l2
    | TermRet None -> "\tj .Lret_%s\n" (* 跳转到统一返回点 *)
    | TermRet (Some op) ->
        let load_ret = l_operand ctx "a0" op in
        load_ret ^ "\tj .Lret_%s\n"
    | TermSeq l -> Printf.sprintf "\tj %s\n" l (* 顺序块，直接跳转 *)
  in
  Printf.sprintf "%s:\n" blk.label ^ inst_codes ^ term_code

(*
  新版函数编译流程
*)
let com_func_generic (f_name : string) (f_args : string list) (f_body : ir_inst list) (f_blocks : ir_block list) (is_optimized : bool) : string =
  let ctx = init_func_ctx () in

  (* --- 阶段一: 分析函数，确定栈布局 --- *)
  
  (* 1. 返回地址 (ra) 和旧的帧指针 (fp) 固定分配在栈顶 *)
  ctx.stack_size <- 8 (* ra 和 fp 各占 4 字节 *)

  (* 2. 为所有参数分配栈空间 *)
  List.iteri
    (fun i arg_name ->
      ignore (alloc_on_stack ctx arg_name))
    f_args;

  (* 3. 遍历所有指令，为所有出现的变量预分配栈空间 *)
  let analyze_operand op =
    match op with
    | Reg name | Var name ->
        if not (Hashtbl.mem ctx.v_env name) then
          ignore (alloc_on_stack ctx name)
    | Imm _ -> ()
  in
  let analyze_inst inst =
    match inst with
    | Binop (_, d, s1, s2) -> analyze_operand d; analyze_operand s1; analyze_operand s2
    | Unop (_, d, s) -> analyze_operand d; analyze_operand s
    | Assign (d, s) -> analyze_operand d; analyze_operand s
    | Call (d, _, args) -> analyze_operand d; List.iter analyze_operand args
    | Ret (Some op) -> analyze_operand op
    | IfGoto (cond, _) -> analyze_operand cond
    | _ -> ()
  in
  if is_optimized then
    List.iter (fun blk -> List.iter analyze_inst blk.insts) f_blocks
  else
    List.iter analyze_inst f_body;

  (* --- 阶段二: 生成汇编代码 --- *)
  
  (* 1. 函数头部 (Prologue) *)
  let prologue = Printf.sprintf "
.globl %s
%s:
\taddi sp, sp, %d
\tsw ra, %d(sp)
\tsw fp, %d(sp)
\taddi fp, sp, %d
"
    f_name
    f_name
    (-ctx.stack_size)
    (ctx.stack_size - 4)
    (ctx.stack_size - 8)
    ctx.stack_size
  in

  (* 2. 将传入的参数从 a0-a7 寄存器或调用者的栈中存入当前函数的栈帧 *)
  let setup_args =
    List.mapi
      (fun i arg_name ->
        let storage = get_sto ctx arg_name in
        match storage with
        | Stack offset ->
            if i < 8 then
              Printf.sprintf "\tsw a%d, %d(fp)\n" i offset
            else
              (* 参数在调用者的栈上传递, sp+x *)
              let caller_offset = (i - 8) * 4 in
              Printf.sprintf "\tlw t0, %d(fp)\n\tsw t0, %d(fp)\n" (ctx.stack_size + caller_offset) offset
        | Register _ -> failwith "Args should be on stack at start")
      f_args
    |> String.concat ""
  in

  (* 3. 编译函数体 *)
  let body_code =
    if is_optimized then
      List.map (com_block ctx) f_blocks
      |> String.concat ""
      |> Printf.sprintf_replace ~search:".Lret_%s" ~replace:(".Lret_" ^ f_name)
    else
      List.map (com_inst ctx) f_body
      |> String.concat ""
      |> Printf.sprintf_replace ~search:".Lret_%s" ~replace:(".Lret_" ^ f_name)
  in

  (* 4. 函数尾声 (Epilogue) *)
  let epilogue = Printf.sprintf "
.Lret_%s:
\tlw fp, %d(sp)
\tlw ra, %d(sp)
\taddi sp, sp, %d
\tret
"
    f_name
    (ctx.stack_size - 8)
    (ctx.stack_size - 4)
    ctx.stack_size
  in

  prologue ^ setup_args ^ body_code ^ epilogue

(* 编译未优化的IR *)
let com_func (f : ir_func) : string =
  com_func_generic f.name f.args f.body [] false

(* 编译优化的IR (基本块) *)
let com_func_o (f : ir_func_o) : string =
  com_func_generic f.name f.args [] f.blocks true

(* 编译整个程序 *)
let com_pro (prog : ir_program) : string =
  let prologue = ".text\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map com_func funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o -> List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm