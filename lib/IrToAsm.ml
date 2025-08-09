open Ir
open Reg_alloc  (* 引入寄存器分配模块 *)

let stack_offset = ref 0
let v_env = Hashtbl.create 1600
let reg_alloc_map = ref StringMap.empty

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

(* 检查是否是2的幂 *)
let is_power_of_2 n = n > 0 && (n land (n - 1)) = 0

(* 计算log2 *)
let log2 n =
  let rec aux i n =
    if n = 1 then i
    else aux (i + 1) (n asr 1)
  in
  aux 0 n

(* 优化的操作数加载 - 优先使用寄存器 *)
let l_operand (dest_reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" dest_reg i
  | Reg r | Var r -> 
      match get_register !reg_alloc_map r with
      | Some src_reg -> 
          if src_reg = dest_reg then ""  (* 相同寄存器不需要移动 *)
          else Printf.sprintf "\tmv %s, %s\n" dest_reg src_reg
      | None -> Printf.sprintf "\tlw %s, %d(sp)\n" dest_reg (get_sto r)

(* 优化的操作数存储 - 同时更新寄存器和栈 *)
let store_result (dst_name : string) (src_reg : string) (dst_off : int) : string =
  match get_register !reg_alloc_map dst_name with
  | Some dst_reg -> 
      if dst_reg = src_reg then
        Printf.sprintf "\tsw %s, %d(sp)\n" src_reg dst_off  (* 相同寄存器只需要存到栈上 *)
      else
        Printf.sprintf "\tmv %s, %s\n\tsw %s, %d(sp)\n" dst_reg src_reg dst_reg dst_off
  | None -> 
      Printf.sprintf "\tsw %s, %d(sp)\n" src_reg dst_off  (* 没有寄存器分配 *)

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_name, dst_off = 
        match dst with 
        | Reg r | Var r -> r, all_st r 
        | _ -> failwith "Bad dst" 
      in
      let lhs_code = l_operand "t1" lhs in
      
      (* 针对特定操作的优化 *)
      match op, rhs with
      | "*", Imm n when is_power_of_2 n ->
          (* 优化：乘以2的幂用移位代替 *)
          let shift = log2 n in
          lhs_code ^ 
          Printf.sprintf "\tli t2, %d\n\tsll t0, t1, t2\n" shift ^
          store_result dst_name "t0" dst_off
      | "/", Imm n when is_power_of_2 n ->
          (* 优化：除以2的幂用移位代替 *)
          let shift = log2 n in
          lhs_code ^ 
          Printf.sprintf "\tli t2, %d\n\tsra t0, t1, t2\n" shift ^
          store_result dst_name "t0" dst_off
      | _ ->
          (* 常规操作 *)
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
          lhs_code ^ rhs_code ^ op_code ^ store_result dst_name "t0" dst_off
      
  | Unop (op, dst, src) ->
      let dst_name, dst_off = 
        match dst with 
        | Reg r | Var r -> r, all_st r 
        | _ -> failwith "Bad dst" 
      in
      let load_src = l_operand "t1" src in
      let op_code =
        match op with
        | "-" -> "\tneg t0, t1\n"
        | "!" -> "\tseqz t0, t1\n"
        | "+" -> "\tmv t0, t1\n"
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      load_src ^ op_code ^ store_result dst_name "t0" dst_off
      
  | Assign (dst, src) ->
      let dst_name, dst_off = 
        match dst with 
        | Reg r | Var r -> r, all_st r 
        | _ -> failwith "Bad dst" 
      in
      
      (* 针对特定赋值模式的优化 *)
      match src with
      | Imm i ->
          (* 立即数赋值 *)
          (match get_register !reg_alloc_map dst_name with
           | Some reg -> 
               Printf.sprintf "\tli %s, %d\n\tsw %s, %d(sp)\n" reg i reg dst_off
           | None ->
               Printf.sprintf "\tli t0, %d\n\tsw t0, %d(sp)\n" i dst_off)
      | Reg src_name | Var src_name ->
          (* 变量间赋值 *)
          (match get_register !reg_alloc_map dst_name, get_register !reg_alloc_map src_name with
           | Some dst_reg, Some src_reg ->
               (* 两者都在寄存器中 *)
               Printf.sprintf "\tmv %s, %s\n\tsw %s, %d(sp)\n" dst_reg src_reg dst_reg dst_off
           | Some dst_reg, None ->
               (* 目标在寄存器，源在栈上 *)
               Printf.sprintf "\tlw %s, %d(sp)\n\tsw %s, %d(sp)\n" 
                 dst_reg (get_sto src_name) dst_reg dst_off
           | None, Some src_reg ->
               (* 目标在栈上，源在寄存器 *)
               Printf.sprintf "\tsw %s, %d(sp)\n" src_reg dst_off
           | None, None ->
               (* 两者都在栈上 *)
               Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n" 
                 (get_sto src_name) dst_off)
      | _ ->
          (* 普通情况 *)
          let load_src = l_operand "t0" src in
          load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
      
  | Load (dst, src) ->
      let dst_name, dst_off = 
        match dst with 
        | Reg r | Var r -> r, all_st r 
        | _ -> failwith "Bad dst" 
      in
      let src_code = l_operand "t1" src in
      src_code ^ "\tlw t0, 0(t1)\n" ^ store_result dst_name "t0" dst_off
      
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
      
  | Call (dst, fname, args) ->
      let dst_name, dst_off = 
        match dst with 
        | Reg r | Var r -> r, all_st r 
        | _ -> failwith "Bad dst" 
      in
      
      (* 保存寄存器 *)
      let save_regs = 
        available_registers |>
        List.map (fun reg -> 
          Printf.sprintf "\tsw %s, -%d(sp)\n" reg ((List.length available_registers) * 4)
        ) |>
        String.concat ""
      in
      
      (* 准备参数 *)
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
      
      (* 函数调用 *)
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      
      (* 恢复寄存器 *)
      let restore_regs = 
        available_registers |>
        List.map (fun reg -> 
          Printf.sprintf "\tlw %s, -%d(sp)\n" reg ((List.length available_registers) * 4)
        ) |>
        String.concat ""
      in
      
      (* 保存返回值 *)
      let save_result = store_result dst_name "a0" dst_off in
      
      save_regs ^ args_code ^ call_code ^ restore_regs ^ save_result
      
  | Ret None ->
      let ra_offset = get_sto "ra" in
      Printf.sprintf
        "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
        ra_offset
        
  | Ret (Some op) ->
      let load_code = l_operand "a0" op in
      let ra_offset = get_sto "ra" in
      load_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          ra_offset
          
  | Goto label -> Printf.sprintf "\tj %s\n" label
  
  | IfGoto (cond, label) ->
      let cond_code = l_operand "t0" cond in
      cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" label
      
  | Label label -> Printf.sprintf "%s:\n" label

(* 优化尾递归调用 *)
let rec optimize_tail_recursion (f : ir_func) : ir_func =
  (* 检查是否包含尾递归调用 *)
  let has_tail_call = ref false in
  
  (* 寻找并变换尾递归调用 *)
  let rec transform_body acc remaining =
    match remaining with
    | [] -> List.rev acc
    | [Call (dst, fname, args); Ret (Some ret_val)] 
      when fname = f.name && 
           (match dst, ret_val with
            | Reg d, Reg r when d = r -> true
            | Var d, Var r when d = r -> true
            | Reg d, Var r when d = r -> true
            | Var d, Reg r when d = r -> true
            | _ -> false) ->
        (* 找到尾递归调用 *)
        has_tail_call := true;
        
        (* 将尾递归调用转换为参数赋值和跳转到函数开始处 *)
        let param_assigns =
          List.mapi (fun i arg ->
            if i < List.length f.args then
              Assign (Var (List.nth f.args i), arg)
            else
              failwith "Too many arguments in tail call"
          ) args
        in
        transform_body (Goto "func_start" :: (List.rev param_assigns) @ acc) []
        
    | inst :: rest ->
        transform_body (inst :: acc) rest
  in
  
  let transformed_body = transform_body [] f.body in
  
  if !has_tail_call then
    { f with body = Label "func_start" :: transformed_body }
  else
    f

let com_block (blk : ir_block) : string =
  (* 为基本块分配寄存器 *)
  reg_alloc_map := allocate_block blk;
  
  blk.insts |> List.map com_inst |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* 为函数分配寄存器 *)
  reg_alloc_map := allocate_func f;
  
  (* 尾递归优化 *)
  let f = optimize_tail_recursion f in

  (* 参数入栈 *)
  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        match get_register !reg_alloc_map name with
        | Some reg ->
            (* 参数有寄存器分配 *)
            if i < 8 then 
              Printf.sprintf "\tmv %s, a%d\n\tsw a%d, %d(sp)\n" reg i i off
            else
              Printf.sprintf "\tlw %s, %d(sp)\n\tsw %s, %d(sp)\n" 
                reg (-4 * (i - 8)) reg off
        | None ->
            (* 参数没有寄存器分配 *)
            if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
            else
              Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
                (* offset 为 call 语句将第 i 个参数压入的偏移 *)
                (-4 * (i - 8))
                off
      )
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
    | Ir_funcs_o funcs_o ->
        List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm