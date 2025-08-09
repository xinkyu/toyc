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

(* Look up a variable's register or stack location *)
let lookup_var var reg_alloc =
  try
    let (_, reg_opt, spill_opt) = 
      List.find (fun (v, _, _) -> v = var) reg_alloc 
    in
    (reg_opt, spill_opt)
  with Not_found -> (None, None)

let operand_str = function
  | Reg r | Var r -> Printf.sprintf "%d(sp)" (get_sto r)
  | Imm i -> Printf.sprintf "%d" i

(* Load an operand into a register *)
let l_operand reg_alloc (reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r -> 
      let (reg_opt, spill_opt) = lookup_var r reg_alloc in
      match reg_opt with
      | Some assigned_reg -> 
          if assigned_reg = reg then ""
          else Printf.sprintf "\tmv %s, %s\n" reg assigned_reg
      | None -> 
          let offset = match spill_opt with
            | Some loc -> 400 + (loc * 4)
            | None -> get_sto r
          in
          Printf.sprintf "\tlw %s, %d(sp)\n" reg offset

(* Generate code for each instruction with register allocation *)
let com_inst reg_alloc (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_var = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let (dst_reg_opt, _) = lookup_var dst_var reg_alloc in
      
      let dst_reg = match dst_reg_opt with 
        | Some r -> r 
        | None -> "t0" 
      in
      
      let lhs_code = l_operand reg_alloc "t1" lhs in
      let rhs_code = l_operand reg_alloc "t2" rhs in
      
      let op_code =
        match op with
        | "+" -> Printf.sprintf "\tadd %s, t1, t2\n" dst_reg
        | "-" -> Printf.sprintf "\tsub %s, t1, t2\n" dst_reg
        | "*" -> Printf.sprintf "\tmul %s, t1, t2\n" dst_reg
        | "/" -> Printf.sprintf "\tdiv %s, t1, t2\n" dst_reg
        | "%" -> Printf.sprintf "\trem %s, t1, t2\n" dst_reg
        | "==" -> Printf.sprintf "\tsub %s, t1, t2\n\tseqz %s, %s\n" dst_reg dst_reg dst_reg
        | "!=" -> Printf.sprintf "\tsub %s, t1, t2\n\tsnez %s, %s\n" dst_reg dst_reg dst_reg
        | "<=" -> Printf.sprintf "\tsgt %s, t1, t2\n\txori %s, %s, 1\n" dst_reg dst_reg dst_reg
        | ">=" -> Printf.sprintf "\tslt %s, t1, t2\n\txori %s, %s, 1\n" dst_reg dst_reg dst_reg
        | "<" -> Printf.sprintf "\tslt %s, t1, t2\n" dst_reg
        | ">" -> Printf.sprintf "\tsgt %s, t1, t2\n" dst_reg
        | "&&" -> Printf.sprintf "\tand %s, t1, t2\n" dst_reg
        | "||" -> Printf.sprintf "\tor %s, t1, t2\n" dst_reg
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      
      (* For spilled variables, we need to store the result back to memory *)
      let store_code = 
        if dst_reg_opt = None then
          let offset = 
            try get_sto dst_var
            with _ -> 
              stack_offset := !stack_offset + 4;
              Hashtbl.add v_env dst_var !stack_offset;
              !stack_offset
          in
          Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg offset
        else ""
      in
      
      lhs_code ^ rhs_code ^ op_code ^ store_code
      
  | Unop (op, dst, src) ->
      let dst_var = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let (dst_reg_opt, _) = lookup_var dst_var reg_alloc in
      
      let dst_reg = match dst_reg_opt with 
        | Some r -> r 
        | None -> "t0" 
      in
      
      let load_src = l_operand reg_alloc "t1" src in
      
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg %s, t1\n" dst_reg
        | "!" -> Printf.sprintf "\tseqz %s, t1\n" dst_reg
        | "+" -> Printf.sprintf "\tmv %s, t1\n" dst_reg
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      
      let store_code = 
        if dst_reg_opt = None then
          let offset = 
            try get_sto dst_var
            with _ -> 
              stack_offset := !stack_offset + 4;
              Hashtbl.add v_env dst_var !stack_offset;
              !stack_offset
          in
          Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg offset
        else ""
      in
      
      load_src ^ op_code ^ store_code
      
  | Assign (dst, src) ->
      let dst_var = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let (dst_reg_opt, _) = lookup_var dst_var reg_alloc in
      
      match (dst_reg_opt, src) with
      | Some dst_reg, Reg src_var | Some dst_reg, Var src_var ->
          (* Register-to-register assignment *)
          let (src_reg_opt, _) = lookup_var src_var reg_alloc in
          (match src_reg_opt with
           | Some src_reg -> Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
           | None -> 
               let offset = get_sto src_var in
               Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg offset)
      
      | Some dst_reg, Imm i ->
          (* Immediate to register *)
          Printf.sprintf "\tli %s, %d\n" dst_reg i
      
      | None, _ ->
          (* Store to memory location *)
          let dst_offset = 
            try get_sto dst_var
            with _ -> 
              stack_offset := !stack_offset + 4;
              Hashtbl.add v_env dst_var !stack_offset;
              !stack_offset
          in
          let load_src = l_operand reg_alloc "t0" src in
          load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_offset
      
  | Call (dst, fname, args) ->
      let dst_var = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let (dst_reg_opt, _) = lookup_var dst_var reg_alloc in
      
      (* Save caller-saved registers if they contain live values *)
      let save_code = 
        List.fold_left (fun acc reg ->
          if List.exists (fun (_, r_opt, _) -> r_opt = Some reg) reg_alloc then
            acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg (get_sto (reg ^ "_save"))
          else acc
        ) "" caller_saved
      in
      
      (* Prepare arguments *)
      let args_code =
        List.mapi
          (fun i arg ->
            if i < 8 then l_operand reg_alloc (Printf.sprintf "a%d" i) arg
            else
              let offset = 4 * (i - 8) in
              l_operand reg_alloc "t0" arg ^ Printf.sprintf "\tsw t0, %d(sp)\n" (-1600 - offset))
          args
        |> String.concat ""
      in
      
      (* Call function *)
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      
      (* Handle return value *)
      let ret_code = match dst_reg_opt with
        | Some r -> if r <> "a0" then Printf.sprintf "\tmv %s, a0\n" r else ""
        | None -> 
            let offset = 
              try get_sto dst_var
              with _ -> 
                stack_offset := !stack_offset + 4;
                Hashtbl.add v_env dst_var !stack_offset;
                !stack_offset
            in
            Printf.sprintf "\tsw a0, %d(sp)\n" offset
      in
      
      (* Restore caller-saved registers *)
      let restore_code = 
        List.fold_left (fun acc reg ->
          if List.exists (fun (_, r_opt, _) -> r_opt = Some reg) reg_alloc then
            acc ^ Printf.sprintf "\tlw %s, %d(sp)\n" reg (get_sto (reg ^ "_save"))
          else acc
        ) "" caller_saved
      in
      
      save_code ^ args_code ^ call_code ^ ret_code ^ restore_code
      
  | Ret None ->
      let ra_offset = get_sto "ra" in
      Printf.sprintf
        "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
        ra_offset
        
  | Ret (Some op) ->
      let load_code = l_operand reg_alloc "a0" op in
      let ra_offset = get_sto "ra" in
      load_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          ra_offset
          
  | Goto label -> 
      Printf.sprintf "\tj %s\n" label
      
  | IfGoto (cond, label) ->
      let cond_code = l_operand reg_alloc "t0" cond in
      cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" label
      
  | Label label -> 
      Printf.sprintf "%s:\n" label
      
  | Load (dst, src) ->
      let dst_var = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
      let (dst_reg_opt, _) = lookup_var dst_var reg_alloc in
      
      let dst_reg = match dst_reg_opt with 
        | Some r -> r 
        | None -> "t0" 
      in
      
      let src_code = l_operand reg_alloc "t1" src in
      let load_code = Printf.sprintf "\tlw %s, 0(t1)\n" dst_reg in
      
      let store_code = 
        if dst_reg_opt = None then
          let offset = 
            try get_sto dst_var
            with _ -> 
              stack_offset := !stack_offset + 4;
              Hashtbl.add v_env dst_var !stack_offset;
              !stack_offset
          in
          Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg offset
        else ""
      in
      
      src_code ^ load_code ^ store_code
      
  | Store (dst, src) ->
      let dst_code = l_operand reg_alloc "t1" dst in
      let src_code = l_operand reg_alloc "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"

let com_block (blk : ir_block) : string =
  (* This is just a placeholder - need to implement with register allocation *)
  blk.insts |> List.map (com_inst []) |> String.concat ""

let com_func (f : ir_func) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* Get register allocation *)
  let reg_alloc = allocate_registers f in
  
  (* Reserve space for callee-saved registers *)
  List.iter (fun reg ->
    stack_offset := !stack_offset + 4;
    Hashtbl.add v_env (reg ^ "_save") !stack_offset;
  ) callee_saved;
  
  (* Reserve space for caller-saved registers that might need saving *)
  List.iter (fun reg ->
    stack_offset := !stack_offset + 4;
    Hashtbl.add v_env (reg ^ "_save") !stack_offset;
  ) caller_saved;
  
  (* Initialize argument locations *)
  List.iteri (fun i name ->
    if i < 8 then
      (* Function arguments are in a0-a7 *)
      ()  (* Will be handled in register allocation *)
    else begin
      (* Arguments beyond 8 are already on stack *)
      stack_offset := !stack_offset + 4;
      Hashtbl.add v_env name !stack_offset;
    end
  ) f.args;
  
  (* Save ra *)
  stack_offset := !stack_offset + 4;
  Hashtbl.add v_env "ra" !stack_offset;
  let ra_save = Printf.sprintf "\tsw ra, %d(sp)\n" !stack_offset in
  
  (* Save callee-saved registers that we'll use *)
  let callee_saves = 
    List.fold_left (fun acc reg ->
      if List.exists (fun (_, r_opt, _) -> r_opt = Some reg) reg_alloc then
        let offset = get_sto (reg ^ "_save") in
        acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg offset
      else acc
    ) "" callee_saved
  in
  
  (* Move arguments to their assigned registers or stack slots *)
  let arg_setup = 
    List.mapi (fun i name ->
      if i >= 8 then "" else  (* Skip stack args *)
      let (reg_opt, spill_opt) = lookup_var name reg_alloc in
      match (reg_opt, spill_opt) with
      | Some r, _ ->
          let arg_reg = Printf.sprintf "a%d" i in
          if r = arg_reg then ""
          else Printf.sprintf "\tmv %s, %s\n" r arg_reg
      | None, Some loc ->
          let offset = 400 + (loc * 4) in
          Printf.sprintf "\tsw a%d, %d(sp)\n" i offset
      | None, None ->
          let offset = 
            try get_sto name
            with _ -> 
              stack_offset := !stack_offset + 4;
              Hashtbl.add v_env name !stack_offset;
              !stack_offset
          in
          Printf.sprintf "\tsw a%d, %d(sp)\n" i offset
    ) f.args |> String.concat ""
  in
  
  (* Generate code for function body *)
  let body_code = f.body |> List.map (com_inst reg_alloc) |> String.concat "" in
  
  (* Generate function epilogue *)
  let epilogue =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      (* Restore callee-saved registers *)
      (List.fold_left (fun acc reg ->
        if List.exists (fun (_, r_opt, _) -> r_opt = Some reg) reg_alloc then
          let offset = get_sto (reg ^ "_save") in
          acc ^ Printf.sprintf "\tlw %s, %d(sp)\n" reg offset
        else acc
       ) "" callee_saved)
      ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n" (get_sto "ra")
    else ""
  in
  
  (* Generate function prologue *)
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" f.name in
  
  prologue ^ ra_save ^ callee_saves ^ arg_setup ^ body_code ^ epilogue

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