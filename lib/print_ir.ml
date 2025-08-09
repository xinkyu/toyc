(* file: lib/print_ir.ml *)

open Ir

let string_of_operand = function
  | Reg name -> name
  | Imm i -> string_of_int i
  | Var name -> name

let string_of_operands ops = String.concat ", " (List.map string_of_operand ops)

let string_of_ir_inst = function
  | Binop (op, dst, lhs, rhs) ->
      Printf.sprintf "%s = %s %s %s" (string_of_operand dst)
        (string_of_operand lhs) op (string_of_operand rhs)
  | Unop (op, dst, src) ->
      Printf.sprintf "%s = %s%s" (string_of_operand dst) op
        (string_of_operand src)
  | Load (dst, src) ->
      Printf.sprintf "%s = *%s" (string_of_operand dst) (string_of_operand src)
  | Store (dst, src) ->
      Printf.sprintf "*%s = %s" (string_of_operand dst) (string_of_operand src)
  | Goto label -> Printf.sprintf "goto %s" label
  | IfGoto (cond, label) ->
      Printf.sprintf "if %s goto %s" (string_of_operand cond) label
  | Label name -> Printf.sprintf "%s:" name
  | Call (ret, fname, args) ->
      Printf.sprintf "%s = call %s(%s)" (string_of_operand ret) fname
        (string_of_operands args)
  | Ret None -> "return"
  | Ret (Some op) -> Printf.sprintf "return %s" (string_of_operand op)
  | Assign (dst, src) ->
      Printf.sprintf "%s = %s" (string_of_operand dst) (string_of_operand src)

let print_ir_func (f : ir_func) =
  Printf.printf "function %s(%s):\n" f.name (String.concat ", " f.args);
  List.iter (fun inst -> Printf.printf "  %s\n" (string_of_ir_inst inst)) f.body

let string_of_ir_term = function
  | TermGoto l -> Printf.sprintf "  terminator: goto %s" l
  | TermIf (cond, l1, l2) ->
      Printf.sprintf "  terminator: if %s goto %s else goto %s"
        (string_of_operand cond) l1 l2
  | TermRet None -> "  terminator: return"
  | TermRet (Some op) ->
      Printf.sprintf "  terminator: return %s" (string_of_operand op)
  | TermSeq l-> Printf.sprintf "  terminator: seqence %s" l

let print_ir_block (b : ir_block) =
  Printf.printf "%s:\n" b.label;
  List.iter
    (fun inst -> Printf.printf "    %s\n" (string_of_ir_inst inst))
    b.insts;
  Printf.printf "%s\n" (string_of_ir_term b.terminator);
  Printf.printf "    preds: [%s]\n" (String.concat ", " b.preds);
  Printf.printf "    succs: [%s]\n" (String.concat ", " b.succs)

let print_ir_func_o (f : ir_func_o) =
  Printf.printf "function %s(%s):\n" f.name (String.concat ", " f.args);
  List.iter print_ir_block f.blocks

(* 修正后的版本 *)
let print_ir_program (prog : ir_program) =
  match prog with
  | Ir_funcs funcs -> List.iter print_ir_func funcs
  | Ir_funcs_o funcs -> List.iter print_ir_func_o funcs
  | Ir_funcs_alloc funcs ->
      List.iter (fun f ->
        Printf.printf "function %s(%s): (allocated)\n" f.name (String.concat ", " f.args);
        List.iter print_ir_block f.blocks
      ) funcs