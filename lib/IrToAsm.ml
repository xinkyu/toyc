open Ir
open Reg_alloc

let stack_offset = ref 0
let v_env = Hashtbl.create 1600
let reg_var_map = ref StringMap.empty  (* 变量到寄存器的映射 *)

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

(* 获取变量的寄存器，如果已分配 *)
let get_var_reg var =
  match get_var_register !reg_var_map var with
  | Some reg -> Some reg
  | None -> None

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
      match get_var_reg r with
      | Some src_reg -> 
          if src_reg = dest_reg then ""  (* 相同寄存器不需要移动 *)
          else Printf.sprintf "\tmv %s, %s\n" dest_reg src_reg
      | None -> Printf.sprintf "\tlw %s, %d(sp)\n" dest_reg (get_sto r)

(* 优化的操作数存储 - 如果有寄存器，存储到寄存器 *)
let store_result (dst : operand) (src_reg : string) : string =
  match dst with
  | Reg r | Var r ->
      let dst_off = all_st r in
      match get_var_reg r with
      | Some dst_reg -> 
          if dst_reg = src_reg then ""  (* 相同寄存器不需要移动 *)
          else Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
      | None -> Printf.sprintf "\tsw %s, %d(sp)\n" src_reg dst_off
  | _ -> failwith "Invalid destination"

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let lhs_code = l_operand "t1" lhs in
      
      (* 优化乘除法 *)
      let (rhs_code, op_code) = 
        match op, rhs with
        | "*", Imm n when is_power_of_2 n ->
            (* 乘法优化为移位 *)
            let shift = log2 n in
            Printf.sprintf "\tli t2, %d\n" shift,
            "\tsll t0, t1, t2\n"
        | "/", Imm n when is_power_of_2 n ->
            (* 除法优化为移位 *)
            let shift = log2 n in
            Printf.sprintf "\tli t2, %d\n" shift,
            "\tsra t0, t1, t2\n"
        | "+", _ -> l_operand "t2" rhs, "\tadd t0, t1, t2\n"
        | "-", _ -> l_operand "t2" rhs, "\tsub t0, t1, t2\n"
        | "*", _ -> l_operand "t2" rhs, "\tmul t0, t1, t2\n"
        | "/", _ -> l_operand "t2" rhs, "\tdiv t0, t1, t2\n"
        | "%", _ -> l_operand "t2" rhs, "\trem t0, t1, t2\n"
        | "==", _ -> l_operand "t2" rhs, "\tsub t0, t1, t2\n\tseqz t0, t0\n"
        | "!=", _ -> l_operand "t2" rhs, "\tsub t0, t1, t2\n\tsnez t0, t0\n"
        | "<=", _ -> l_operand "t2" rhs, "\tsgt t0, t1, t2\n\txori t0, t0, 1\n"
        | ">=", _ -> l_operand "t2" rhs, "\tslt t0, t1, t2\n\txori t0, t0, 1\n"
        | "<", _ -> l_operand "t2" rhs, "\tslt t0, t1, t2\n"
        | ">", _ -> l_operand "t2" rhs, "\tsgt t0, t1, t2\n"
        | "&&", _ -> l_operand "t2" rhs, "\tand t0, t1, t2\n"
        | "||", _ -> l_operand "t2" rhs, "\tor t0, t1, t2\n"
        | _, _ -> l_operand "t2" rhs, failwith ("Unknown binop: " ^ op)
      in
      
      lhs_code ^ rhs_code ^ op_code ^ store_result dst "t0"
      
  | Unop (op, dst, src) ->
      let load_src = l_operand "t1" src in
      let op_code =
        match op with
        | "-" -> "\tneg t0, t1\n"
        | "!" -> "\tseqz t0, t1\n"
        | "+" -> "\tmv t0, t1\n"
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      load_src ^ op_code ^ store_result dst "t0"
      
  | Assign (dst, src) ->
      (* 直接从源到目标的优化赋值 *)
      match dst, src with
      | (Reg dst_name | Var dst_name), (Reg src_name | Var src_name) ->
          (* 两者都是变量 *)
          (match get_var_reg dst_name, get_var_reg src_name with
           | Some dst_reg, Some src_reg ->
               if dst_reg = src_reg then ""
               else Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
           | Some dst_reg, None ->
               Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg (get_sto src_name)
           | None, Some src_reg ->
               Printf.sprintf "\tsw %s, %d(sp)\n" src_reg (all_st dst_name)
           | None, None ->
               Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n" 
                 (get_sto src_name) (all_st dst_name))
      | (Reg dst_name | Var dst_name), Imm i ->
          (* 源是立即数 *)
          (match get_var_reg dst_name with
           | Some dst_reg -> Printf.sprintf "\tli %s, %d\n" dst_reg i
           | None -> Printf.sprintf "\tli t0, %d\n\tsw t0, %d(sp)\n" i (all_st dst_name))
      | _, _ ->
          (* 其他情况 *)
          let load_src = l_operand "t0" src in
          load_src ^ store_result dst "t0"
      
  | Load (dst, src) ->
      let src_code = l_operand "t1" src in
      let dst_code = 
        match dst with
        | Reg r | Var r ->
            (match get_var_reg r with
             | Some dst_reg -> Printf.sprintf "\tlw %s, 0(t1)\n" dst_reg
             | None -> Printf.sprintf "\tlw t0, 0(t1)\n\tsw t0, %d(sp)\n" (all_st r))
        | _ -> failwith "Invalid destination"
      in
      src_code ^ dst_code
      
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
      
  | Call (dst, fname, args) ->
      (* 调用函数时，需要保存和恢复寄存器 *)
      
      (* 保存寄存器到栈上 *)
      let saved_regs = StringMap.fold (fun var info acc ->
          match info.reg with
          | Some reg -> 
              Printf.sprintf "\tsw %s, %d(sp)\n" reg (all_st var) ^ acc
          | None -> acc
        ) !reg_var_map ""
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
      let restored_regs = StringMap.fold (fun var info acc ->
          match info.reg with
          | Some reg -> 
              acc ^ Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto var)
          | None -> acc
        ) !reg_var_map ""
      in
      
      (* 保存返回值 *)
      let result_code = store_result dst "a0" in
      
      saved_regs ^ args_code ^ call_code ^ restored_regs ^ result_code
      
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

(* 正确实现尾递归优化 *)
let optimize_tail_recursion (f : ir_func) : ir_func =
  (* 检查是否有自身递归调用 *)
  let has_self_call = List.exists (function
      | Call (_, name, _) when name = f.name -> true
      | _ -> false
    ) f.body
  in
  
  if not has_self_call then f else
  
  (* 将参数移动指令添加到函数开头 *)
  let param_moves = 
    List.mapi (fun i name ->
        (* a0-a7是参数寄存器 *)
        if i < 8 then
          match get_var_reg name with
          | Some reg -> [Assign (Var name, Reg ("a" ^ string_of_int i))]
          | None -> [Assign (Var name, Reg ("a" ^ string_of_int i))]
        else
          let stack_offset = -4 * (i - 8) in
          [Load (Var name, Imm stack_offset)]
      ) f.args
    |> List.flatten
  in
  
  (* 处理尾递归调用 *)
  let rec process_insts acc = function
    | [] -> List.rev acc
    | Call (dst, fname, args) :: Ret (Some ret_val) :: rest 
      when fname = f.name && 
           (match dst, ret_val with
            | Reg d, Reg r | Var d, Var r | Reg d, Var r | Var d, Reg r -> d = r
            | _ -> false) ->
        (* 找到尾递归调用 *)
        let setup_args = 
          List.mapi (fun i arg ->
              if i < 8 then
                (* 直接移动到参数寄存器 *)
                match arg with
                | Imm n -> Assign (Reg ("a" ^ string_of_int i), Imm n)
                | _ -> Assign (Reg ("a" ^ string_of_int i), arg)
              else
                (* 栈上参数 *)
                let stack_offset = -1600 - 4 * (i - 8) in
                match arg with
                | Imm n -> Store (Imm stack_offset, Imm n)
                | _ -> Assign (Var ("_temp"), arg) :: [Store (Imm stack_offset, Var "_temp")]
            ) args
          |> List.flatten
        in
        
        (* 跳转到函数开头 *)
        process_insts (List.rev (Goto "func_start" :: setup_args) @ acc) rest
        
    | inst :: rest ->
        process_insts (inst :: acc) rest
  in
  
  (* 添加函数入口标签和参数移动指令，然后处理尾递归 *)
  let optimized_body = 
    Label "func_start" :: param_moves @ process_insts [] f.body 
  in
  
  { f with body = optimized_body }

let com_block (blk : ir_block) : string =
  (* 分配寄存器 *)
  reg_var_map := allocate_block_regs blk;
  
  blk.insts |> List.map com_inst |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* 分配寄存器 *)
  reg_var_map := allocate_func_registers f;
  
  (* 尾递归优化 *)
  let f = optimize_tail_recursion f in

  (* 参数入栈 *)
  let pae_set =
    List.mapi
      (fun i name ->
        let off = all_st name in
        match get_var_reg name with
        | Some reg ->
            if i < 8 then Printf.sprintf "\tmv %s, a%d\n" reg i
            else Printf.sprintf "\tlw %s, %d(sp)\n" reg (-4 * (i - 8))
        | None ->
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