open Ir

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

(* 检查是否是2的幂 *)
let is_power_of_2 n = n > 0 && (n land (n - 1)) = 0

(* 计算log2 *)
let log2 n =
  let rec aux i n =
    if n = 1 then i
    else aux (i + 1) (n asr 1)
  in
  aux 0 n

let l_operand (reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r -> Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto r)

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let lhs_code = l_operand "t1" lhs in
      
      (* 根据操作符和右操作数生成代码 *)
      let (rhs_code, op_code) = 
        match op, rhs with
        | "*", Imm n when is_power_of_2 n ->
            (* 优化：乘以2的幂用移位代替 *)
            let shift = log2 n in
            Printf.sprintf "\tli t2, %d\n" shift,
            "\tsll t0, t1, t2\n"
        | "/", Imm n when is_power_of_2 n ->
            (* 优化：除以2的幂用移位代替 *)
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
      
  | Assign (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let load_src = l_operand "t0" src in
      load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
      
  | Load (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let src_code = l_operand "t1" src in
      src_code ^ "\tlw t0, 0(t1)\n" ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
      
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
      
  | Call (dst, fname, args) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
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
let optimize_tail_calls (func_name : string) (args : string list) (insts : ir_inst list) : ir_inst list =
  let rec process_insts acc = function
    | [] -> List.rev acc
    | Call (dst, fname, call_args) :: Ret (Some ret_val) :: rest 
      when fname = func_name && 
           (match dst, ret_val with
            | Reg d, Reg r | Var d, Var r | Reg d, Var r | Var d, Reg r -> d = r
            | _ -> false) ->
        (* 找到尾递归调用，转换为参数赋值和跳转 *)
        let param_assigns = 
          List.mapi (fun i arg ->
              if i < List.length args then
                let param_name = List.nth args i in
                Assign (Var param_name, arg)
              else
                Call (dst, fname, call_args) (* 保持原样，不应该发生 *)
            ) call_args
        in
        process_insts (List.rev (Goto "func_start" :: param_assigns) @ acc) rest
    | inst :: rest ->
        process_insts (inst :: acc) rest
  in
  
  (* 只有当函数内有尾递归调用时才添加标签 *)
  let has_tail_call = 
    List.exists (function
      | Call (_, fname, _) :: Ret _ :: _ when fname = func_name -> true
      | _ -> false
    ) (List.mapi (fun i inst -> 
         if i < List.length insts - 1 then [inst; List.nth insts (i+1)]
         else [inst]
       ) insts)
  in
  
  if has_tail_call then
    Label "func_start" :: process_insts [] insts
  else
    insts

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

  (* 优化尾递归调用 *)
  let optimized_body = optimize_tail_calls f.name f.args f.body in

  let body_code = optimized_body |> List.map com_inst |> String.concat "" in

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