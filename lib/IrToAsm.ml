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
  | Reg r | Var r -> 
      (* 检查变量是否有寄存器分配 *)
      (match get_var_location !reg_map r with
       | `Reg reg -> reg
       | `Stack -> Printf.sprintf "%d(sp)" (get_sto r))
  | Imm i -> Printf.sprintf "%d" i

(* 优化的操作数加载函数 *)
let l_operand (reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r -> 
      (* 检查变量是否有寄存器分配 *)
      (match get_var_location !reg_map r with
       | `Reg src_reg -> Printf.sprintf "\tmv %s, %s\n" reg src_reg
       | `Stack -> Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto r))

(* 优化的操作数存储函数 *)
let s_operand (dst : operand) (src_reg : string) : string =
  match dst with
  | Reg r | Var r ->
      (* 检查目标是否有寄存器分配 *)
      (match get_var_location !reg_map r with
       | `Reg dst_reg -> Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
       | `Stack -> Printf.sprintf "\tsw %s, %d(sp)\n" src_reg (get_sto r))
  | _ -> failwith "Cannot store to immediate"

(* 检查是否是2的幂 *)
let is_power_of_2 n = n > 0 && (n land (n - 1)) = 0

(* 计算log2 *)
let log2 n =
  let rec aux i n =
    if n = 1 then i
    else aux (i + 1) (n asr 1)
  in
  aux 0 n

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let lhs_code = l_operand "t1" lhs in
      
      (* 针对乘法和除法的优化 *)
      let (rhs_code, op_code) = 
        match op with
        | "*" -> 
            (match rhs with
             | Imm n when is_power_of_2 n ->
                 (* 优化：乘以2的幂用移位代替 *)
                 let shift = log2 n in
                 (Printf.sprintf "\tli t2, %d\n" shift,
                  "\tsll t0, t1, t2\n")
             | _ -> (l_operand "t2" rhs, "\tmul t0, t1, t2\n"))
        | "/" -> 
            (match rhs with
             | Imm n when is_power_of_2 n ->
                 (* 优化：除以2的幂用移位代替 *)
                 let shift = log2 n in
                 (Printf.sprintf "\tli t2, %d\n" shift,
                  "\tsra t0, t1, t2\n")  (* 算术右移，保持符号 *)
             | _ -> (l_operand "t2" rhs, "\tdiv t0, t1, t2\n"))
        | "+" -> (l_operand "t2" rhs, "\tadd t0, t1, t2\n")
        | "-" -> (l_operand "t2" rhs, "\tsub t0, t1, t2\n")
        | "%" -> (l_operand "t2" rhs, "\trem t0, t1, t2\n")
        | "==" -> (l_operand "t2" rhs, "\tsub t0, t1, t2\n\tseqz t0, t0\n")
        | "!=" -> (l_operand "t2" rhs, "\tsub t0, t1, t2\n\tsnez t0, t0\n")
        | "<=" -> (l_operand "t2" rhs, "\tsgt t0, t1, t2\n\txori t0, t0, 1\n")
        | ">=" -> (l_operand "t2" rhs, "\tslt t0, t1, t2\n\txori t0, t0, 1\n")
        | "<" -> (l_operand "t2" rhs, "\tslt t0, t1, t2\n")
        | ">" -> (l_operand "t2" rhs, "\tsgt t0, t1, t2\n")
        | "&&" -> (l_operand "t2" rhs, "\tand t0, t1, t2\n")
        | "||" -> (l_operand "t2" rhs, "\tor t0, t1, t2\n")
        | _ -> (l_operand "t2" rhs, failwith ("Unknown binop: " ^ op))
      in
      
      (* 使用优化的存储函数 *)
      lhs_code ^ rhs_code ^ op_code ^ s_operand dst "t0"
      
  | Unop (op, dst, src) ->
      let load_src = l_operand "t1" src in
      let op_code =
        match op with
        | "-" -> "\tneg t0, t1\n"
        | "!" -> "\tseqz t0, t1\n"
        | "+" -> "\tmv t0, t1\n"
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      load_src ^ op_code ^ s_operand dst "t0"
      
  | Assign (dst, src) ->
      (* 针对赋值操作的优化 *)
      match dst, src with
      | (Reg dst_name | Var dst_name), (Reg src_name | Var src_name) ->
          (* 检查源和目标是否都在寄存器中 *)
          (match get_var_location !reg_map dst_name, get_var_location !reg_map src_name with
           | `Reg dst_reg, `Reg src_reg ->
               (* 两者都在寄存器中，直接寄存器间移动 *)
               Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
           | `Reg dst_reg, `Stack ->
               (* 目标在寄存器，源在栈上 *)
               Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg (get_sto src_name)
           | `Stack, `Reg src_reg ->
               (* 目标在栈上，源在寄存器 *)
               Printf.sprintf "\tsw %s, %d(sp)\n" src_reg (get_sto dst_name)
           | `Stack, `Stack ->
               (* 两者都在栈上，需要通过临时寄存器 *)
               let load_src = l_operand "t0" src in
               load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" (get_sto dst_name))
      | _, _ ->
          (* 其他情况使用标准方法 *)
          let load_src = l_operand "t0" src in
          load_src ^ s_operand dst "t0"
      
  (* Not used *)
  | Load (dst, src) ->
      let src_code = l_operand "t1" src in
      src_code ^ "\tlw t0, 0(t1)\n" ^ s_operand dst "t0"
      
  (* Not used *)
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
      
  | Call (dst, fname, args) ->
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
      let save_result = s_operand dst "a0" in
      
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

(* 处理尾递归优化 *)
let optimize_tail_recursion (f : ir_func) : ir_func =
  let is_self_call inst =
    match inst with
    | Call (_, fname, _) when fname = f.name -> true
    | _ -> false
  in
  
  (* 查找并优化尾递归 *)
  let optimize_inst inst next_insts =
    match inst, next_insts with
    | Call (dst, fname, args), [Ret (Some ret_val)] when 
        fname = f.name && 
        (match dst, ret_val with
         | Reg d, Reg r | Var d, Var r | Reg d, Var r | Var d, Reg r -> d = r
         | _ -> false) ->
        (* 找到尾递归调用，转换为参数赋值和跳转 *)
        let param_assigns = 
          List.mapi (fun i arg ->
            if i < f.args |> List.length then
              let param_name = List.nth f.args i in
              Assign (Var param_name, arg)
            else
              inst (* 不应该发生，保持原样 *)
          ) args
        in
        param_assigns @ [Goto "function_start"]
    | _ -> [inst]
  in
  
  (* 添加函数开始标签，并优化指令 *)
  let rec process_insts acc = function
    | [] -> List.rev acc
    | inst :: rest ->
        let optimized = optimize_inst inst rest in
        process_insts (List.rev optimized @ acc) rest
  in
  
  (* 只有当函数有尾递归调用时才添加标签 *)
  let has_tail_recursion = 
    List.exists is_self_call f.body
  in
  
  if has_tail_recursion then
    let body_with_label = Label "function_start" :: f.body in
    { f with body = process_insts [] body_with_label }
  else
    f

let com_block (blk : ir_block) : string =
  blk.insts |> List.map com_inst |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* 尾递归优化 *)
  let f = optimize_tail_recursion f in
  
  (* 分析变量使用情况 *)
  let var_info_map = analyze_var_usage f.body in
  allocate_registers var_info_map;
  reg_map := var_info_map;
  
  (* 保存需要使用的寄存器 *)
  let used_regs = ref [] in
  StringMap.iter (fun _ info ->
    match info.reg with
    | Some reg -> if not (List.mem reg !used_regs) then used_regs := reg :: !used_regs
    | None -> ()
  ) var_info_map;
  
  let save_regs = 
    List.map (fun reg ->
      Printf.sprintf "\tsw %s, -%d(sp)\n" reg ((List.length !used_regs) * 4)
    ) !used_regs
    |> String.concat ""
  in
  
  let restore_regs = 
    List.map (fun reg ->
      Printf.sprintf "\tlw %s, -%d(sp)\n" reg ((List.length !used_regs) * 4)
    ) !used_regs
    |> String.concat ""
  in

  (* 参数入栈 *)
  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        (* 检查参数是否有寄存器分配 *)
        match get_var_location var_info_map name with
        | `Reg reg ->
            if i < 8 then Printf.sprintf "\tmv %s, a%d\n" reg i
            else Printf.sprintf "\tlw %s, %d(sp)\n" reg (-4 * (i - 8))
        | `Stack ->
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
      ^ restore_regs
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    else body_code
  in
  
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label ^ save_regs in
  prologue ^ pae_set ^ body_code

let com_func_o (f : ir_func_o) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* 进行寄存器分配 *)
  let var_info_map = allocate_registers_for_func f in
  reg_map := var_info_map;
  
  (* 保存需要使用的寄存器 *)
  let used_regs = ref [] in
  StringMap.iter (fun _ info ->
    match info.reg with
    | Some reg -> if not (List.mem reg !used_regs) then used_regs := reg :: !used_regs
    | None -> ()
  ) var_info_map;
  
  let save_regs = 
    List.map (fun reg ->
      Printf.sprintf "\tsw %s, -%d(sp)\n" reg ((List.length !used_regs) * 4)
    ) !used_regs
    |> String.concat ""
  in
  
  let restore_regs = 
    List.map (fun reg ->
      Printf.sprintf "\tlw %s, -%d(sp)\n" reg ((List.length !used_regs) * 4)
    ) !used_regs
    |> String.concat ""
  in

  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        (* 检查参数是否有寄存器分配 *)
        match get_var_location var_info_map name with
        | `Reg reg ->
            if i < 8 then Printf.sprintf "\tmv %s, a%d\n" reg i
            else Printf.sprintf "\tlw %s, %d(sp)\n" reg (-4 * (i - 8))
        | `Stack ->
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
      ^ restore_regs
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    else body_code
  in

  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label ^ save_regs in
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