open Ir
open Regalloc

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

(* 获取或创建变量的栈偏移 *)
let get_or_create_stack_offset var =
  try get_sto var
  with _ -> all_st var

let operand_str = function
  | Reg r | Var r -> 
      (* 检查变量是否在寄存器中 *)
      (match get_register r with
       | Some reg -> reg.name
       | None -> Printf.sprintf "%d(sp)" (get_sto r))
  | Imm i -> Printf.sprintf "%d" i

(* 加载操作数到指定寄存器 *)
let l_operand (target_reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" target_reg i
  | Reg r | Var r ->
      (* 检查变量是否在寄存器中 *)
      match get_register r with
      | Some reg -> 
          if reg.name = target_reg then
            "" (* 已经在目标寄存器中，无需移动 *)
          else
            Printf.sprintf "\tmv %s, %s\n" target_reg reg.name (* 从一个寄存器移动到另一个 *)
      | None ->
          (* 从栈中加载 *)
          Printf.sprintf "\tlw %s, %d(sp)\n" target_reg (get_sto r)

let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      
      (* 尝试为目标变量分配寄存器 *)
      (* 可能需要的溢出代码 *)
      let spill_code = ref "" in
      
      let dst_reg = match allocate_register dst_name with
        | Some reg -> reg
        | None -> 
            (* 如果没有可用寄存器，我们需要选择一个进行溢出 *)
            match select_register_to_spill () with
            | Some reg_to_spill ->
                (* 将寄存器中的变量溢出到栈上 *)
                (match reg_to_spill.var_name with
                | Some var ->
                    let stack_offset = get_or_create_stack_offset var in
                    spill_code := Printf.sprintf "\tsw %s, %d(sp)\n" reg_to_spill.name stack_offset;
                    free_register reg_to_spill
                | None -> ());
                
                (* 重新分配该寄存器 *)
                reg_to_spill.allocated := true;
                reg_to_spill.var_name <- Some dst_name;
                Hashtbl.add var_to_reg dst_name reg_to_spill;
                reg_to_spill
            | None -> 
                (* 理论上不应该发生，因为我们有足够的寄存器 *)
                failwith "No register available for allocation"
      in
      
      (* 获取目标寄存器名 *)
      let dst_reg_name = dst_reg.name in
      
      (* 加载左右操作数 *)
      let lhs_code = l_operand "t1" lhs in
      let rhs_code = l_operand "t2" rhs in
      
      (* 根据操作符生成汇编代码 *)
      let op_code =
        match op with
        | "+" -> Printf.sprintf "\tadd %s, t1, t2\n" dst_reg_name
        | "-" -> Printf.sprintf "\tsub %s, t1, t2\n" dst_reg_name
        | "*" -> Printf.sprintf "\tmul %s, t1, t2\n" dst_reg_name
        | "/" -> Printf.sprintf "\tdiv %s, t1, t2\n" dst_reg_name
        | "%" -> Printf.sprintf "\trem %s, t1, t2\n" dst_reg_name
        | "==" -> Printf.sprintf "\tsub %s, t1, t2\n\tseqz %s, %s\n" dst_reg_name dst_reg_name dst_reg_name
        | "!=" -> Printf.sprintf "\tsub %s, t1, t2\n\tsnez %s, %s\n" dst_reg_name dst_reg_name dst_reg_name
        | "<=" -> Printf.sprintf "\tsgt %s, t1, t2\n\txori %s, %s, 1\n" dst_reg_name dst_reg_name dst_reg_name
        | ">=" -> Printf.sprintf "\tslt %s, t1, t2\n\txori %s, %s, 1\n" dst_reg_name dst_reg_name dst_reg_name
        | "<" -> Printf.sprintf "\tslt %s, t1, t2\n" dst_reg_name
        | ">" -> Printf.sprintf "\tsgt %s, t1, t2\n" dst_reg_name
        | "&&" -> Printf.sprintf "\tand %s, t1, t2\n" dst_reg_name
        | "||" -> Printf.sprintf "\tor %s, t1, t2\n" dst_reg_name
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      
      (* 结果已在目标寄存器中，不需要额外保存 *)
      !spill_code ^ lhs_code ^ rhs_code ^ op_code
  | Unop (op, dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      
      (* 可能需要的溢出代码 *)
      let spill_code = ref "" in
      
      (* 尝试为目标变量分配寄存器 *)
      let dst_reg = match allocate_register dst_name with
        | Some reg -> reg
        | None -> 
            (* 处理寄存器溢出 *)
            match select_register_to_spill () with
            | Some reg_to_spill ->
                (* 溢出到栈上 *)
                (match reg_to_spill.var_name with
                | Some var ->
                    let stack_offset = get_or_create_stack_offset var in
                    spill_code := Printf.sprintf "\tsw %s, %d(sp)\n" reg_to_spill.name stack_offset;
                    free_register reg_to_spill
                | None -> ());
                
                (* 重新分配该寄存器 *)
                reg_to_spill.allocated := true;
                reg_to_spill.var_name <- Some dst_name;
                Hashtbl.add var_to_reg dst_name reg_to_spill;
                reg_to_spill
            | None -> failwith "No register available for allocation"
      in
      
      let dst_reg_name = dst_reg.name in
      let load_src = l_operand "t1" src in
      
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg %s, t1\n" dst_reg_name
        | "!" -> Printf.sprintf "\tseqz %s, t1\n" dst_reg_name
        | "+" -> Printf.sprintf "\tmv %s, t1\n" dst_reg_name
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      
      !spill_code ^ load_src ^ op_code
      
  | Assign (dst, src) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      
      (* 可能需要的溢出代码 *)
      let spill_code = ref "" in
      
      (* 尝试为目标变量分配寄存器 *)
      let dst_reg = match allocate_register dst_name with
        | Some reg -> reg
        | None -> 
            (* 处理寄存器溢出 *)
            match select_register_to_spill () with
            | Some reg_to_spill ->
                (* 溢出到栈上 *)
                (match reg_to_spill.var_name with
                | Some var ->
                    let stack_offset = get_or_create_stack_offset var in
                    spill_code := Printf.sprintf "\tsw %s, %d(sp)\n" reg_to_spill.name stack_offset;
                    free_register reg_to_spill
                | None -> ());
                
                (* 重新分配该寄存器 *)
                reg_to_spill.allocated := true;
                reg_to_spill.var_name <- Some dst_name;
                Hashtbl.add var_to_reg dst_name reg_to_spill;
                reg_to_spill
            | None -> failwith "No register available for allocation"
      in
      
      (* 直接加载源操作数到目标寄存器 *)
      let load_code = match src with
      | Imm i -> Printf.sprintf "\tli %s, %d\n" dst_reg.name i
      | Reg src_name | Var src_name ->
          match get_register src_name with
          | Some src_reg -> 
              if src_reg.name = dst_reg.name then
                "" (* 如果源和目标是同一个寄存器，无需操作 *)
              else
                Printf.sprintf "\tmv %s, %s\n" dst_reg.name src_reg.name
          | None ->
              (* 从栈中加载源变量 *)
              Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg.name (get_sto src_name)
      in
      
      !spill_code ^ load_code
  (* Not used *)
  | Load (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let src_code = l_operand "t1" src in
      src_code ^ "\tlw t0, 0(t1)\n" ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  (* Not used *)
  | Store (dst, src) ->
      let dst_code = l_operand "t1" dst in
      let src_code = l_operand "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
  | Call (dst, fname, args) ->
      let dst_name = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      
      (* 在函数调用前保存所有已分配的寄存器到栈上 *)
      let save_regs = List.fold_left (fun acc reg ->
        if !(reg.allocated) then
          match reg.var_name with
          | Some var_name ->
              let offset = get_or_create_stack_offset var_name in
              acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg.name offset
          | None -> acc
        else
          acc
      ) "" available_regs in
      
      (* 准备函数参数 *)
      let args_code =
        List.mapi
          (fun i arg ->
            if i < 8 then
              (* 直接加载到参数寄存器 *)
              l_operand (Printf.sprintf "a%d" i) arg
            else
              (* 超出寄存器数量的参数放到栈上 *)
              let offset = 4 * (i - 8) in
              l_operand "t0" arg ^ Printf.sprintf "\tsw t0, %d(sp)\n" (-1600 - offset))
          args
        |> String.concat ""
      in
      
      (* 函数调用会改变寄存器状态，调用后需要重置寄存器分配状态 *)
      free_all_registers ();
      
      (* 为返回值分配寄存器 *)
      let dst_reg = 
        (* 尝试使用a0作为返回值寄存器 *)
        match List.find_opt (fun r -> r.name = "a0") available_regs with
        | Some a0_reg ->
            a0_reg.allocated := true;
            a0_reg.var_name <- Some dst_name;
            Hashtbl.add var_to_reg dst_name a0_reg;
            a0_reg
        | None ->
            (* 如果没有a0寄存器(不应该发生)，使用第一个可用寄存器 *)
            match List.find_opt (fun r -> not !(r.allocated)) available_regs with
            | Some reg ->
                reg.allocated := true;
                reg.var_name <- Some dst_name;
                Hashtbl.add var_to_reg dst_name reg;
                reg
            | None ->
                failwith "No registers available for function return value"
      in
      
      (* 生成函数调用代码 *)
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      
      (* 从a0移动返回值到指定寄存器 *)
      let move_result = 
        if dst_reg.name = "a0" then
          "" (* 已经在a0中，不需要移动 *)
        else
          Printf.sprintf "\tmv %s, a0\n" dst_reg.name
      in
      
      save_regs ^ args_code ^ call_code ^ move_result
  | Ret None ->
      let ra_offset = get_sto "ra" in
      
      (* 在返回前保存所有分配的寄存器到栈上 *)
      let save_regs = List.fold_left (fun acc reg ->
        if !(reg.allocated) then
          match reg.var_name with
          | Some var_name ->
              let offset = get_or_create_stack_offset var_name in
              acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg.name offset
          | None -> acc
        else
          acc
      ) "" available_regs in
      
      (* 释放所有寄存器 *)
      free_all_registers ();
      
      save_regs ^ Printf.sprintf
        "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
        ra_offset
        
  | Ret (Some op) ->
      (* 将返回值加载到a0 *)
      let load_code = l_operand "a0" op in
      let ra_offset = get_sto "ra" in
      
      (* 保存所有其他分配的寄存器到栈上 *)
      let save_regs = List.fold_left (fun acc reg ->
        if !(reg.allocated) && reg.name <> "a0" then
          match reg.var_name with
          | Some var_name ->
              let offset = get_or_create_stack_offset var_name in
              acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg.name offset
          | None -> acc
        else
          acc
      ) "" available_regs in
      
      (* 释放所有寄存器 *)
      free_all_registers ();
      
      load_code ^ save_regs ^ Printf.sprintf
        "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
        ra_offset
        
  | Goto label -> 
      (* 对于跳转，我们可能需要保存当前的寄存器状态以确保跨基本块一致性 *)
      (* 在简单实现中，我们只生成跳转指令 *)
      Printf.sprintf "\tj %s\n" label
      
  | IfGoto (cond, label) ->
      (* 条件跳转，处理类似于常规跳转 *)
      let cond_reg_name = match cond with
        | Reg r | Var r ->
            (match get_register r with
             | Some reg -> reg.name
             | None ->
                 (* 如果条件不在寄存器中，从栈中加载 *)
                 let load_code = l_operand "t0" cond in
                 (* 返回加载指令和寄存器名称 *)
                 load_code ^ "t0")
        | Imm i ->
            Printf.sprintf "\tli t0, %d\n" i
      in
      
      (* 提取可能包含的加载指令 *)
      let load_part, reg_name = 
        if String.contains cond_reg_name '\n' then
          let parts = String.split_on_char '\n' cond_reg_name in
          let load = String.concat "\n" (List.filter (fun s -> s <> "") (List.init (List.length parts - 1) (fun i -> List.nth parts i))) in
          load ^ "\n", List.nth parts (List.length parts - 1)
        else
          "", cond_reg_name
      in
      
      load_part ^ Printf.sprintf "\tbne %s, x0, %s\n" reg_name label
      
  | Label label -> 
      (* 到达一个新的标签，可能需要调整寄存器状态 *)
      (* 在简单实现中，我们只生成标签 *)
      Printf.sprintf "%s:\n" label

let com_block (blk : ir_block) : string =
  (* 生成基本块的代码 *)
  let inst_code = blk.insts |> List.map com_inst |> String.concat "" in
  
  (* 处理基本块的终止指令 *)
  let term_code = match blk.terminator with
    | TermGoto label -> Printf.sprintf "\tj %s\n" label
    | TermIf (cond, then_label, else_label) ->
        (* 加载条件到寄存器并获取寄存器名 *)
        let load_code, cond_reg = match cond with
          | Reg r | Var r ->
              (match get_register r with
               | Some reg -> "", reg.name
               | None -> Printf.sprintf "\tlw t0, %d(sp)\n" (get_sto r), "t0")
          | Imm i -> Printf.sprintf "\tli t0, %d\n" i, "t0"
        in
        
        (* 生成条件跳转 *)
        load_code ^ Printf.sprintf "\tbne %s, x0, %s\n\tj %s\n" cond_reg then_label else_label
    | TermRet None -> 
        (* 返回前保存寄存器状态 *)
        let save_regs = List.fold_left (fun acc reg ->
          if !(reg.allocated) then
            match reg.var_name with
            | Some var_name ->
                let offset = get_or_create_stack_offset var_name in
                acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg.name offset
            | None -> acc
          else acc
        ) "" available_regs in
        save_regs ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n" (get_sto "ra")
    | TermRet (Some op) ->
        (* 加载返回值到a0 *)
        let load_ret = l_operand "a0" op in
        (* 保存其他寄存器 *)
        let save_regs = List.fold_left (fun acc reg ->
          if !(reg.allocated) && reg.name <> "a0" then
            match reg.var_name with
            | Some var_name ->
                let offset = get_or_create_stack_offset var_name in
                acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg.name offset
            | None -> acc
          else acc
        ) "" available_regs in
        load_ret ^ save_regs ^ 
        Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n" (get_sto "ra")
    | TermSeq _next -> 
        (* 如果下一个块紧跟着当前块，不需要额外跳转 *)
        ""
  in
  
  inst_code ^ term_code

let com_func (f : ir_func) : string =
  (* 清空符号表和寄存器分配状态 *)
  Hashtbl.clear v_env;
  stack_offset := 0;
  free_all_registers ();

  (* 参数处理: 前8个参数已在a0-a7寄存器中，我们可以直接为它们分配这些寄存器 *)
  let arg_setup =
    List.mapi
      (fun i name ->
        let off = all_st name in
        if i < 8 then begin
          (* 为前8个参数分配寄存器 - 保存到栈上同时尝试保留在寄存器中 *)
          let reg_info = List.find_opt (fun r -> r.name = "a" ^ string_of_int i) available_regs in
          match reg_info with
          | Some reg ->
              reg.allocated := true;
              reg.var_name <- Some name;
              Hashtbl.add var_to_reg name reg;
              Printf.sprintf "\tsw a%d, %d(sp)\n" i off
          | None ->
              (* 仅保存到栈上 *)
              Printf.sprintf "\tsw a%d, %d(sp)\n" i off
        end else
          (* 栈传递的参数加载到栈帧中的固定位置 *)
          Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
            (* 栈上参数的偏移 *)
            (-4 * (i - 8))
            off)
      f.args
    |> String.concat ""
  in

  (* 保存返回地址 *)
  let ra_setup = Printf.sprintf "\tsw ra, %d(sp)\n" (all_st "ra") in
  
  (* 编译函数体 *)
  let body_code = f.body |> List.map com_inst |> String.concat "" in

  (* 确保函数总是以返回指令结束 *)
  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      (* 在返回前保存所有寄存器内容到栈 *)
      let save_regs = List.fold_left (fun acc reg ->
        if !(reg.allocated) then
          match reg.var_name with
          | Some var_name ->
              let offset = get_or_create_stack_offset var_name in
              acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg.name offset
          | None -> acc
        else
          acc
      ) "" available_regs in
      
      body_code ^ save_regs
      ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    else 
      body_code
  in
  
  (* 函数序言 *)
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  
  prologue ^ ra_setup ^ arg_setup ^ body_code

let com_func_o (f : ir_func_o) : string =
  (* 清空符号表和寄存器分配状态 *)
  Hashtbl.clear v_env;
  stack_offset := 0;
  free_all_registers ();

  (* 参数处理 *)
  let arg_setup =
    List.mapi
      (fun i name ->
        let off = all_st name in
        if i < 8 then begin
          (* 为前8个参数分配寄存器 - 保存到栈上同时尝试保留在寄存器中 *)
          let reg_info = List.find_opt (fun r -> r.name = "a" ^ string_of_int i) available_regs in
          (match reg_info with
           | Some reg ->
               reg.allocated := true;
               reg.var_name <- Some name;
               Hashtbl.add var_to_reg name reg;
               Printf.sprintf "\tsw a%d, %d(sp)\n" i off
           | None ->
               (* 如果找不到对应的寄存器（不应该发生），只保存到栈上 *)
               Printf.sprintf "\tsw a%d, %d(sp)\n" i off)
        end else
          (* 栈传递的参数 *)
          Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
            (-4 * (i - 8))
            off)
      f.args
    |> String.concat ""
  in

  (* 保存返回地址 *)
  let ra_setup = Printf.sprintf "\tsw ra, %d(sp)\n" (all_st "ra") in
  
  (* 编译基本块 *)
  let body_code = f.blocks |> List.map com_block |> String.concat "" in

  (* 确保函数总是以返回指令结束 *)
  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      (* 在返回前保存所有寄存器内容到栈 *)
      let save_regs = List.fold_left (fun acc reg ->
        if !(reg.allocated) then
          match reg.var_name with
          | Some var_name ->
              let offset = get_or_create_stack_offset var_name in
              acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg.name offset
          | None -> acc
        else
          acc
      ) "" available_regs in
      
      body_code ^ save_regs
      ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          (get_sto "ra")
    else 
      body_code
  in
  
  (* 函数序言 *)
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  
  prologue ^ ra_setup ^ arg_setup ^ body_code

let com_pro (prog : ir_program) : string =
  let prologue = ".text\n .global main\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map com_func funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o ->
        List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm