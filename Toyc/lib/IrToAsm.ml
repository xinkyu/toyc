open Ir

let stack_offset = ref 0
let v_env = Hashtbl.create 1600
let reg_alloc = Hashtbl.create 100  (* 变量到寄存器的映射 *)

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

(* 检查变量是否已分配寄存器 *)
let get_reg var =
  try Some (Hashtbl.find reg_alloc var)
  with Not_found -> None

let operand_str = function
  | Reg r | Var r -> 
      (match get_reg r with
       | Some reg -> reg
       | None -> Printf.sprintf "%d(sp)" (get_sto r))
  | Imm i -> Printf.sprintf "%d" i

let l_operand (dest_reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" dest_reg i
  | Reg r | Var r -> 
      (match get_reg r with
       | Some reg -> 
           if reg = dest_reg then
             "" (* 已经在目标寄存器中，无需加载 *)
           else
             Printf.sprintf "\tmv %s, %s\n" dest_reg reg
       | None -> Printf.sprintf "\tlw %s, %d(sp)\n" dest_reg (get_sto r))

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_reg = match get_reg dst_name with Some r -> r | None -> "t0" in
      
      (* 根据操作数是否已在寄存器中选择合适的加载方式 *)
      let lhs_reg, lhs_code = 
        match lhs with
        | Imm _ -> "t1", l_operand "t1" lhs
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> reg, ""  (* 已在寄存器中 *)
            | None -> "t1", l_operand "t1" lhs
      in
      
      let rhs_reg, rhs_code = 
        match rhs with
        | Imm _ -> "t2", l_operand "t2" rhs
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> reg, ""  (* 已在寄存器中 *)
            | None -> "t2", l_operand "t2" rhs
      in
      
      (* 指令优化：如果操作数是立即数，尝试使用立即数指令 *)
      let op_code =
        match op, rhs with
        | "+", Imm i when i >= -2048 && i < 2048 -> Printf.sprintf "\taddi %s, %s, %d\n" dst_reg lhs_reg i
        | "-", Imm i when i >= -2048 && i < 2048 -> Printf.sprintf "\taddi %s, %s, %d\n" dst_reg lhs_reg (-i)
        | "*", Imm i when i = 2 -> Printf.sprintf "\tslli %s, %s, 1\n" dst_reg lhs_reg
        | "*", Imm i when i = 4 -> Printf.sprintf "\tslli %s, %s, 2\n" dst_reg lhs_reg
        | "*", Imm i when i = 8 -> Printf.sprintf "\tslli %s, %s, 3\n" dst_reg lhs_reg
        | "*", Imm i when i = 16 -> Printf.sprintf "\tslli %s, %s, 4\n" dst_reg lhs_reg
        | "/", Imm i when i = 2 -> Printf.sprintf "\tsrai %s, %s, 1\n" dst_reg lhs_reg
        | "/", Imm i when i = 4 -> Printf.sprintf "\tsrai %s, %s, 2\n" dst_reg lhs_reg
        | "/", Imm i when i = 8 -> Printf.sprintf "\tsrai %s, %s, 3\n" dst_reg lhs_reg
        | "/", Imm i when i = 16 -> Printf.sprintf "\tsrai %s, %s, 4\n" dst_reg lhs_reg
        | _ ->
            match op with
            | "+" -> Printf.sprintf "\tadd %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | "-" -> Printf.sprintf "\tsub %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | "*" -> Printf.sprintf "\tmul %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | "/" -> Printf.sprintf "\tdiv %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | "%" -> Printf.sprintf "\trem %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | "==" -> Printf.sprintf "\tsub %s, %s, %s\n\tseqz %s, %s\n" dst_reg lhs_reg rhs_reg dst_reg dst_reg
            | "!=" -> Printf.sprintf "\tsub %s, %s, %s\n\tsnez %s, %s\n" dst_reg lhs_reg rhs_reg dst_reg dst_reg
            | "<=" -> Printf.sprintf "\tsgt %s, %s, %s\n\txori %s, %s, 1\n" dst_reg lhs_reg rhs_reg dst_reg dst_reg
            | ">=" -> Printf.sprintf "\tslt %s, %s, %s\n\txori %s, %s, 1\n" dst_reg lhs_reg rhs_reg dst_reg dst_reg
            | "<" -> Printf.sprintf "\tslt %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | ">" -> Printf.sprintf "\tsgt %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | "&&" -> Printf.sprintf "\tand %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | "||" -> Printf.sprintf "\tor %s, %s, %s\n" dst_reg lhs_reg rhs_reg
            | _ -> failwith ("Unknown binop: " ^ op)
      in
      
      let store_code =
        match get_reg dst_name with
        | Some _ -> ""  (* 已分配寄存器，无需存储到栈 *)
        | None -> Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg (get_sto dst_name)
      in
      
      lhs_code ^ rhs_code ^ op_code ^ store_code
  | Unop (op, dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_reg = match get_reg dst_name with Some r -> r | None -> "t0" in
      
      let src_reg, load_src = 
        match src with
        | Imm _ -> "t1", l_operand "t1" src
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> reg, ""
            | None -> "t1", l_operand "t1" src
      in
      
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg %s, %s\n" dst_reg src_reg
        | "!" -> Printf.sprintf "\tseqz %s, %s\n" dst_reg src_reg
        | "+" -> 
            if src_reg = dst_reg then ""
            else Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      
      let store_code =
        match get_reg dst_name with
        | Some _ -> ""  (* 已分配寄存器，无需存储到栈 *)
        | None -> Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg (get_sto dst_name)
      in
      
      load_src ^ op_code ^ store_code
      
  | Assign (dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      
      (* 目标寄存器或栈位置 *)
      let dst_reg = match get_reg dst_name with Some r -> r | None -> "t0" in
      
      (* 源操作数 *)
      let src_code = match src with
        | Imm i -> Printf.sprintf "\tli %s, %d\n" dst_reg i
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> 
                if reg = dst_reg then ""  (* 源和目标是同一个寄存器 *)
                else Printf.sprintf "\tmv %s, %s\n" dst_reg reg
            | None -> Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg (get_sto r)
      in
      
      (* 如果目标没有分配寄存器，需要存储到栈 *)
      let store_code =
        match get_reg dst_name with
        | Some _ -> ""  (* 已分配寄存器，无需存储到栈 *)
        | None -> Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg (get_sto dst_name)
      in
      
      src_code ^ store_code
  (* Not used *)
  | Load (dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let dst_reg = match get_reg dst_name with Some r -> r | None -> "t0" in
      
      let src_reg, src_code = 
        match src with
        | Imm _ -> failwith "Cannot load from immediate"
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> reg, ""
            | None -> "t1", l_operand "t1" src
      in
      
      let load_code = Printf.sprintf "\tlw %s, 0(%s)\n" dst_reg src_reg in
      
      let store_code =
        match get_reg dst_name with
        | Some _ -> ""  (* 已分配寄存器，无需存储到栈 *)
        | None -> Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg (get_sto dst_name)
      in
      
      src_code ^ load_code ^ store_code
      
  (* Not used *)
  | Store (dst, src) ->
      let dst_reg, dst_code = 
        match dst with
        | Imm _ -> failwith "Cannot store to immediate"
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> reg, ""
            | None -> "t1", l_operand "t1" dst
      in
      
      let src_reg, src_code = 
        match src with
        | Imm i -> "t2", Printf.sprintf "\tli t2, %d\n" i
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> reg, ""
            | None -> "t2", l_operand "t2" src
      in
      
      dst_code ^ src_code ^ Printf.sprintf "\tsw %s, 0(%s)\n" src_reg dst_reg
      
  | Call (dst, fname, args) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      
      (* 保存寄存器 - 这里可以优化只保存活跃的寄存器 *)
      let save_regs_code = 
        Hashtbl.fold (fun var reg acc ->
          acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg (all_st var)
        ) reg_alloc ""
      in
      
      (* 参数传递 *)
      let args_code =
        List.mapi
          (fun i arg ->
            let target_reg = Printf.sprintf "a%d" i in
            if i < 8 then
              match arg with
              | Imm i -> Printf.sprintf "\tli %s, %d\n" target_reg i
              | Reg r | Var r ->
                  match get_reg r with
                  | Some reg -> 
                      if reg = target_reg then "" 
                      else Printf.sprintf "\tmv %s, %s\n" target_reg reg
                  | None -> Printf.sprintf "\tlw %s, %d(sp)\n" target_reg (get_sto r)
            else
              let offset = 4 * (i - 8) in
              match arg with
              | Imm i -> 
                  Printf.sprintf "\tli t0, %d\n\tsw t0, %d(sp)\n" i (-1600 - offset)
              | Reg r | Var r ->
                  match get_reg r with
                  | Some reg -> Printf.sprintf "\tsw %s, %d(sp)\n" reg (-1600 - offset)
                  | None -> Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n" (get_sto r) (-1600 - offset)
          ) args
        |> String.concat ""
      in
      
      (* 调用函数 *)
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      
      (* 恢复寄存器 - 同样可以优化只恢复活跃的寄存器 *)
      let restore_regs_code = 
        Hashtbl.fold (fun var reg acc ->
          acc ^ Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto var)
        ) reg_alloc ""
      in
      
      (* 保存返回值 *)
      let store_result =
        match get_reg dst_name with
        | Some reg -> 
            if reg = "a0" then ""
            else Printf.sprintf "\tmv %s, a0\n" reg
        | None -> Printf.sprintf "\tsw a0, %d(sp)\n" (get_sto dst_name)
      in
      
      save_regs_code ^ args_code ^ call_code ^ restore_regs_code ^ store_result
      
  | Ret None ->
      let ra_offset = get_sto "ra" in
      
      (* 恢复帧指针和返回地址 *)
      Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n" ra_offset
      
  | Ret (Some op) ->
      (* 将返回值加载到 a0 *)
      let load_code = match op with
        | Imm i -> Printf.sprintf "\tli a0, %d\n" i
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> 
                if reg = "a0" then ""
                else Printf.sprintf "\tmv a0, %s\n" reg
            | None -> Printf.sprintf "\tlw a0, %d(sp)\n" (get_sto r)
      in
      
      let ra_offset = get_sto "ra" in
      
      (* 恢复帧指针和返回地址 *)
      load_code ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n" ra_offset
      
  | Goto label -> Printf.sprintf "\tj %s\n" label
  
  | IfGoto (cond, label) ->
      let cond_reg, cond_code = match cond with
        | Imm i -> "t0", Printf.sprintf "\tli t0, %d\n" i
        | Reg r | Var r ->
            match get_reg r with
            | Some reg -> reg, ""
            | None -> "t0", l_operand "t0" cond
      in
      
      cond_code ^ Printf.sprintf "\tbne %s, x0, %s\n" cond_reg label
      
  | Label label -> Printf.sprintf "%s:\n" label

let com_block (blk : ir_block) : string =
  blk.insts |> List.map com_inst |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  Hashtbl.clear reg_alloc;
  stack_offset := 0;

  (* 执行寄存器分配 *)
  let reg_mapping = Regalloc.allocate_registers f in
  Hashtbl.iter (fun var reg -> Hashtbl.add reg_alloc var reg) reg_mapping;
  
  (* 为参数分配寄存器 *)
  List.iteri (fun i name ->
    if i < 8 && not (Hashtbl.mem reg_alloc name) then
      (* 优先使用参数寄存器 a0-a7 *)
      Hashtbl.add reg_alloc name (Printf.sprintf "a%d" i)
  ) f.args;

  (* 参数处理 *)
  let pae_set =
    List.mapi
      (fun i name ->
        match get_reg name with
        | Some reg ->
            if i < 8 then
              if reg = Printf.sprintf "a%d" i then ""
              else Printf.sprintf "\tmv %s, a%d\n" reg i
            else
              (* 超过8个参数的情况 *)
              Printf.sprintf "\tlw %s, %d(sp)\n" reg (-4 * (i - 8))
        | None ->
            (* 没有分配到寄存器的参数保存到栈上 *)
            let off = all_st name in
            if i < 8 then 
              Printf.sprintf "\tsw a%d, %d(sp)\n" i off
            else
              Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
                (-4 * (i - 8))
                off)
      f.args
    |> String.concat ""
  in

  (* ra 入栈 *)
  let pae_set =
    pae_set ^ Printf.sprintf "\tsw ra, %d(sp)\n" (all_st "ra")
  in

  (* 生成函数体代码 *)
  let body_code = f.body |> List.map com_inst |> String.concat "" in

  (* 检查是否需要添加默认返回语句 *)
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
  Hashtbl.clear reg_alloc;
  stack_offset := 0;

  (* 为优化后的基本块执行寄存器分配 - 这需要在 regalloc.ml 中添加专门的函数 *)
  (* 临时方案：将基本块展平为指令列表，然后执行寄存器分配 *)
  let flattened_insts = 
    List.fold_left (fun acc block -> acc @ block.insts) [] f.blocks 
  in
  
  (* 构造临时 ir_func 用于寄存器分配 *)
  let temp_func = { name = f.name; args = f.args; body = flattened_insts } in
  let reg_mapping = Regalloc.allocate_registers temp_func in
  Hashtbl.iter (fun var reg -> Hashtbl.add reg_alloc var reg) reg_mapping;
  
  (* 为参数分配寄存器 *)
  List.iteri (fun i name ->
    if i < 8 && not (Hashtbl.mem reg_alloc name) then
      (* 优先使用参数寄存器 a0-a7 *)
      Hashtbl.add reg_alloc name (Printf.sprintf "a%d" i)
  ) f.args;

  (* 参数处理 *)
  let pae_set =
    List.mapi
      (fun i name ->
        match get_reg name with
        | Some reg ->
            if i < 8 then
              if reg = Printf.sprintf "a%d" i then ""
              else Printf.sprintf "\tmv %s, a%d\n" reg i
            else
              (* 超过8个参数的情况 *)
              Printf.sprintf "\tlw %s, %d(sp)\n" reg (-4 * (i - 8))
        | None ->
            (* 没有分配到寄存器的参数保存到栈上 *)
            let off = all_st name in
            if i < 8 then 
              Printf.sprintf "\tsw a%d, %d(sp)\n" i off
            else
              Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
                (-4 * (i - 8))
                off)
      f.args
    |> String.concat ""
  in

  (* ra 入栈 *)
  let pae_set =
    pae_set ^ Printf.sprintf "\tsw ra, %d(sp)\n" (all_st "ra")
  in

  (* 生成基本块代码 *)
  let body_code = f.blocks |> List.map com_block |> String.concat "" in

  (* 检查是否需要添加默认返回语句 *)
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