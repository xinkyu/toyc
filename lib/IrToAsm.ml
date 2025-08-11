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
  | Assign (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let load_src = l_operand "t0" src in
      load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  (* Not used in optimized path *)
  | Load (dst, src) ->
      let dst_off =
        all_st
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let src_code = l_operand "t1" src in
      src_code ^ "\tlw t0, 0(t1)\n" ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  (* Not used in optimized path *)
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
  (* These are now handled by com_terminator for optimized functions *)
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

(* 新增：翻译基本块终结符 *)
let com_terminator (term : ir_term) : string =
  match term with
  | TermGoto label -> Printf.sprintf "\tj %s\n" label
  | TermIf (cond, l_true, l_false) ->
      let cond_code = l_operand "t0" cond in
      cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" l_true
      ^ Printf.sprintf "\tj %s\n" l_false
  | TermRet None ->
      let ra_offset = get_sto "ra" in
      Printf.sprintf
        "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
        ra_offset
  | TermRet (Some op) ->
      let load_code = l_operand "a0" op in
      let ra_offset = get_sto "ra" in
      load_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n"
          ra_offset
  | TermSeq label ->
      (* 为确保正确性，总是生成跳转 *)
      Printf.sprintf "\tj %s\n" label

(* 修改：为基本块生成代码，包括标签、指令和终结符 *)
let com_block (blk : ir_block) : string =
  let label_code = Printf.sprintf "%s:\n" blk.label in
  let insts_code = blk.insts |> List.map com_inst |> String.concat "" in
  let terminator_code = com_terminator blk.terminator in
  label_code ^ insts_code ^ terminator_code

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
  
  (* 修改：现在 com_block 会生成完整的带控制流的代码 *)
  let body_code = f.blocks |> List.map com_block |> String.concat "" in

  (* 检查 body_code 是否以 ret 结束; 这个检查可能不再是必须的，因为终结符现在被正确处理, 但保留无害 *)
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