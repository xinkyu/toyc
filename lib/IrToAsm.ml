(* file: lib/IrToAsm.ml *)

open Ir

let callee_saved = ["s0";"s1";"s2";"s3";"s4";"s5";"s6";"s7";"s8";"s9";"s10";"s11"]

let com_func_alloc (f : allocated_func) : string =
  let alloc_map = f.alloc_map in
  let final_stack_size = ref f.stack_size in

  let used_callee_saved =
    List.filter (fun r ->
      StringMap.exists (fun _ alloc ->
        match alloc with InReg reg when reg = r -> true | _ -> false
      ) alloc_map
    ) callee_saved
  in
  final_stack_size := !final_stack_size + (List.length used_callee_saved * 4) + 4;

  if !final_stack_size mod 16 <> 0 then
    final_stack_size := !final_stack_size + (16 - (!final_stack_size mod 16));

  let load_operand target_reg op =
    match op with
    | Imm i -> Printf.sprintf "\tli %s, %d\n" target_reg i
    | Reg v | Var v ->
        (match StringMap.find_opt v alloc_map with
        | Some (InReg r) -> if r <> target_reg then Printf.sprintf "\tmv %s, %s\n" target_reg r else ""
        | Some (OnStack offset) -> Printf.sprintf "\tlw %s, %d(sp)\n" target_reg offset
        | None -> failwith (Printf.sprintf "FATAL: variable %s not found in allocation map" v))
  in

  let store_operand source_reg op =
    match op with
    | Imm _ -> failwith "Cannot store to an immediate"
    | Reg v | Var v ->
        (match StringMap.find_opt v alloc_map with
        | Some (InReg r) -> if r <> source_reg then Printf.sprintf "\tmv %s, %s\n" r source_reg else ""
        | Some (OnStack offset) -> Printf.sprintf "\tsw %s, %d(sp)\n" source_reg offset
        | None -> failwith (Printf.sprintf "FATAL: variable %s not found in allocation map" v))
  in

  let prologue =
    let stack_alloc = if !final_stack_size > 0 then Printf.sprintf "\taddi sp, sp, -%d\n" !final_stack_size else "" in
    let ra_offset = !final_stack_size - 4 in
    let save_ra = if !final_stack_size > 0 then Printf.sprintf "\tsw ra, %d(sp)\n" ra_offset else "" in
    let save_callee =
      List.mapi (fun i r ->
        let offset = ra_offset - 4 * (i + 1) in
        Printf.sprintf "\tsw %s, %d(sp)\n" r offset
      ) used_callee_saved |> String.concat ""
    in
    Printf.sprintf "%s:\n" f.name ^ stack_alloc ^ save_ra ^ save_callee
  in

  let body =
    let insts_asm =
      List.map (fun (b: ir_block) ->
        let block_label = Printf.sprintf "%s:\n" b.label in
        let insts_code =
          List.map (fun inst ->
            match inst with
            | Binop (op, dst, lhs, rhs) ->
                let code = load_operand "t1" lhs ^ load_operand "t2" rhs in
                let result =
                  match op with
                  | "+" -> "\tadd t0, t1, t2\n"
                  | "-" -> "\tsub t0, t1, t2\n"
                  | "*" -> "\tmul t0, t1, t2\n"
                  | "/" -> "\tdiv t0, t1, t2\n"
                  | "%" -> "\trem t0, t1, t2\n"
                  | "<" -> "\tslt t0, t1, t2\n"
                  | ">" -> "\tsgt t0, t1, t2\n"
                  | "==" -> "\tsub t0, t1, t2\n\tseqz t0, t0\n"
                  | "!=" -> "\tsub t0, t1, t2\n\tsnez t0, t0\n"
                  | "<=" -> "\tsgt t0, t1, t2\n\txori t0, t0, 1\n"
                  | ">=" -> "\tslt t0, t1, t2\n\txori t0, t0, 1\n"
                  | _ -> failwith ("Unsupported binop: " ^ op)
                in
                code ^ result ^ store_operand "t0" dst
            | Unop (op, dst, src) ->
                let op_str = match op with "-" -> "neg" | "!" -> "seqz" | "+" -> "mv" | _ -> failwith op in
                load_operand "t1" src ^ Printf.sprintf "\t%s t0, t1\n" op_str ^ store_operand "t0" dst
            | Assign (dst, src) -> load_operand "t0" src ^ store_operand "t0" dst
            | Call (dst, fname, args) ->
                let args_setup =
                  List.mapi (fun i arg ->
                    if i < 8 then load_operand (Printf.sprintf "a%d" i) arg
                    else failwith "stack arguments not implemented yet"
                  ) args |> String.concat ""
                in
                args_setup ^ Printf.sprintf "\tcall %s\n" fname ^ store_operand "a0" dst
            | Goto l -> Printf.sprintf "\tj %s\n" l
            | IfGoto (cond, l) -> load_operand "t0" cond ^ Printf.sprintf "\tbnez t0, %s\n" l
            | Label _ -> ""
            | Ret (Some op) -> load_operand "a0" op
            | Ret None -> ""
            | Load _ | Store _ -> "## Load/Store not fully implemented for allocated backend ##\n"
          ) b.insts |> String.concat ""
        in
        let term_code = match b.terminator with
          | TermGoto l -> Printf.sprintf "\tj %s\n" l
          | TermIf (cond, l1, l2) -> load_operand "t0" cond ^ Printf.sprintf "\tbnez t0, %s\n\tj %s\n" l1 l2
          | TermRet _ -> ""
          | TermSeq _ -> ""
        in
        block_label ^ insts_code ^ term_code
      ) f.blocks |> String.concat ""
    in
    prologue ^ insts_asm
  in

  let epilogue =
    if !final_stack_size > 0 then
      let ra_offset = !final_stack_size - 4 in
      let restore_ra = Printf.sprintf "\tlw ra, %d(sp)\n" ra_offset in
      let restore_callee =
        List.mapi (fun i r ->
          let offset = ra_offset - 4 * (i + 1) in
          Printf.sprintf "\tlw %s, %d(sp)\n" r offset
        ) used_callee_saved |> String.concat ""
      in
      let stack_dealloc = Printf.sprintf "\taddi sp, sp, %d\n" !final_stack_size in
      restore_callee ^ restore_ra ^ stack_dealloc ^ "\tret\n"
    else
      "\tret\n"
  in
  body ^ epilogue

let com_pro (prog : ir_program) : string =
  let header = ".text\n.global main\n" in
  let funcs_asm = match prog with
    | Ir_funcs_alloc funcs -> List.map com_func_alloc funcs |> String.concat "\n"
    | _ -> failwith "Cannot generate assembly for non-allocated IR"
  in
  header ^ funcs_asm