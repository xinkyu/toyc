open Ir
open Reg_alloc

let stack_offset = ref 0
let v_env = Hashtbl.create 1600
let reg_map = ref StringMap.empty  (* 保存寄存器分配信息 *)

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

(* 获取变量的寄存器，如果有分配 *)
let get_var_reg var_name =
  match get_var_location !reg_map var_name with
  | `Reg reg -> Some reg
  | `Stack -> None

(* 优化的操作数加载函数 *)
let l_operand (reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r -> 
      match get_var_reg r with
      | Some src_reg -> Printf.sprintf "\tmv %s, %s\n" reg src_reg
      | None -> Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto r)

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let lhs_code = l_operand "t1" lhs in
      let rhs_code = l_operand "t2" rhs in
      
      (* 针对乘法和除法的优化 *)
      let op_code =
        match op, rhs with
        | "*", Imm n when is_power_of_2 n ->
            (* 优化：乘以2的幂用移位代替 *)
            let shift = log2 n in
            Printf.sprintf "\tli t2, %d\n\tsll t0, t1, t2\n" shift
        | "/", Imm n when is_power_of_2 n ->
            (* 优化：除以2的幂用移位代替 *)
            let shift = log2 n in
            Printf.sprintf "\tli t2, %d\n\tsra t0, t1, t2\n" shift  (* 算术右移 *)
        | "+", _ -> "\tadd t0, t1, t2\n"
        | "-", _ -> "\tsub t0, t1, t2\n"
        | "*", _ -> "\tmul t0, t1, t2\n"
        | "/", _ -> "\tdiv t0, t1, t2\n"
        | "%", _ -> "\trem t0, t1, t2\n"
        | "==", _ -> "\tsub t0, t1, t2\n\tseqz t0, t0\n"
        | "!=", _ -> "\tsub t0, t1, t2\n\tsnez t0, t0\n"
        | "<=", _ -> "\tsgt t0, t1, t2\n\txori t0, t0, 1\n"
        | ">=", _ -> "\tslt t0, t1, t2\n\txori t0, t0, 1\n"
        | "<", _ -> "\tslt t0, t1, t2\n"
        | ">", _ -> "\tsgt t0, t1, t2\n"
        | "&&", _ -> "\tand t0, t1, t2\n"
        | "||", _ -> "\tor t0, t1, t2\n"
        | _, _ -> failwith ("Unknown binop: " ^ op)
      in
      
      (* 看看目标是否分配了寄存器 *)
      let dst_str = 
        match dst with
        | Reg r | Var r ->
            (match get_var_reg r with
             | Some dst_reg -> Printf.sprintf "\tmv %s, t0\n" dst_reg
             | None -> Printf.sprintf "\tsw t0, %d(sp)\n" dst_off)
        | _ -> failwith "Invalid destination"
      in
      
      lhs_code ^ rhs_code ^ op_code ^ dst_str
      
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
      
      (* 看看目标是否分配了寄存器 *)
      let dst_str = 
        match dst with
        | Reg r | Var r ->
            (match get_var_reg r with
             | Some dst_reg -> Printf.sprintf "\tmv %s, t0\n" dst_reg
             | None -> Printf.sprintf "\tsw t0, %d(sp)\n" dst_off)
        | _ -> failwith "Invalid destination"
      in
      
      load_src ^ op_code ^ dst_str
      
  | Assign (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      
      (* 针对赋值操作的优化 *)
      match dst, src with
      | (Reg dst_name | Var dst_name), (Reg src_name | Var src_name) ->
          (match get_var_reg dst_name, get_var_reg src_name with
           | Some dst_reg, Some src_reg ->
               (* 两者都在寄存器中，直接寄存器间移动 *)
               Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
           | Some dst_reg, None ->
               (* 目标在寄存器，源在栈上 *)
               Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg (get_sto src_name)
           | None, Some src_reg ->
               (* 目标在栈上，源在寄存器 *)
               Printf.sprintf "\tsw %s, %d(sp)\n" src_reg dst_off
           | None, None ->
               (* 两者都在栈上，需要通过临时寄存器 *)
               Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n" (get_sto src_name) dst_off)
      | _, Imm i ->
          (match get_var_reg (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") with
           | Some dst_reg -> Printf.sprintf "\tli %s, %d\n" dst_reg i
           | None -> Printf.sprintf "\tli t0, %d\n\tsw t0, %d(sp)\n" i dst_off)
      | _, _ ->
          (* 其他情况使用标准方法 *)
          let load_src = l_operand "t0" src in
          load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
      
  | Load (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let src_code = l_operand "t1" src in
      let dst_code = 
        match dst with
        | Reg r | Var r ->
            (match get_var_reg r with
             | Some dst_reg -> Printf.sprintf "\tlw %s, 0(t1)\n" dst_reg
             | None -> Printf.sprintf "\tlw t0, 0(t1)\n\tsw t0, %d(sp)\n" dst_off)
        | _ -> failwith "Invalid destination"
      in
      src_code ^ dst_code
      
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
      
  | Call (dst, fname, args) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      
      (* 保存寄存器 *)
      let save_regs =
        StringMap.fold (fun var_name info acc ->
          match info.reg with
          | Some reg when info.spill -> 
              acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg (get_sto var_name)
          | _ -> acc
        ) !reg_map ""
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
        StringMap.fold (fun var_name info acc ->
          match info.reg with
          | Some reg when info.spill -> 
              acc ^ Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto var_name)
          | _ -> acc
        ) !reg_map ""
      in
      
      (* 保存返回值 *)
      let save_result = 
        match dst with
        | Reg r | Var r ->
            (match get_var_reg r with
             | Some dst_reg -> Printf.sprintf "\tmv %s, a0\n" dst_reg
             | None -> Printf.sprintf "\tsw a0, %d(sp)\n" dst_off)
        | _ -> failwith "Invalid destination"
      in
      
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

let com_block (blk : ir_block) : string =
  blk.insts |> List.map com_inst |> String.concat ""

(* 尾递归优化函数 *)
let optimize_tail_recursion (func : ir_func) : ir_func =
  (* 检查是否有尾递归 *)
  let is_tail_recursive = ref false in
  
  (* 查找并替换尾递归调用 *)
  let rec process_insts insts =
    match insts with
    | Call (dst, fname, args) :: Ret (Some ret_val) :: rest when 
        fname = func.name && 
        (match dst, ret_val with
         | Reg d, Reg r | Var d, Var r | Reg d, Var r | Var d, Reg r -> d = r
         | _ -> false) ->
        (* 是尾递归调用 *)
        is_tail_recursive := true;
        (* 用参数赋值代替 *)
        let assigns = List.mapi (fun i arg ->
            if i < List.length func.args then
              let param_name = List.nth func.args i in
              Assign (Var param_name, arg)
            else
              Assign (dst, arg) (* 保留原参数，不应该发生 *)
          ) args
        in
        (* 添加跳转到函数开始处 *)
        assigns @ [Goto "function_start"] @ process_insts rest
    | inst :: rest ->
        inst :: process_insts rest
    | [] -> []
  in
  
  let processed_body = process_insts func.body in
  
  if !is_tail_recursive then
    (* 添加函数起始标签 *)
    { func with body = Label "function_start" :: processed_body }
  else
    func

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* 尾递归优化 *)
  let f = optimize_tail_recursion f in
  
  (* 分析变量使用情况 *)
  let var_info_map = analyze_var_usage f.body in
  allocate_registers var_info_map;
  reg_map := var_info_map;
  
  (* 参数入栈 *)
  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        (* 检查参数是否有寄存器分配 *)
        match get_var_reg name with
        | Some reg ->
            if i < 8 then Printf.sprintf "\tmv %s, a%d\n" reg i
            else Printf.sprintf "\tlw %s, %d(sp)\n" reg (-4 * (i - 8))
        | None ->
            if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
            else
              Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
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

  (* 进行寄存器分配 *)
  let var_info_map = allocate_registers_for_func f in
  reg_map := var_info_map;

  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        (* 检查参数是否有寄存器分配 *)
        match get_var_reg name with
        | Some reg ->
            if i < 8 then Printf.sprintf "\tmv %s, a%d\n" reg i
            else Printf.sprintf "\tlw %s, %d(sp)\n" reg (-4 * (i - 8))
        | None ->
            if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
            else
              Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
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

  let body_code = f.blocks |> List.map com_block |> String.concat "" in

  (* 检查 body_code 是否以 ret 结束 *)
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