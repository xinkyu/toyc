type operand =
  | Reg of string (* 临时寄存器 *)
  | Imm of int (* 立即数 *)
  | Var of string (* 变量名 *)

type ir_inst =
  | Binop of string * operand * operand * operand (* t1 = t2 + t3 *)
  | Unop of string * operand * operand (* t1 = -t2 *)
  | Load of operand * operand (* t1 = *t2 *)
  | Store of operand * operand (* *t1 = t2 *)
  | Goto of string (* 优化的 IR 没有 *)
  | IfGoto of operand * string (* 优化的 IR 没有 *)
  | Label of string (* 优化的 IR 没有 *)
  | Call of operand * string * operand list
  (* 优化后的 IR 没有 *)
  (* t1 = call f(args) *)
  | Ret of operand option (* 优化后的 IR 没有 *)
  | Assign of operand * operand (* t1 = t2 *)

type ir_func = { name : string; args : string list; body : ir_inst list }

(* 用于优化 *)
type ir_term =
  | TermGoto of string
  | TermIf of operand * string * string
  | TermRet of operand option
  | TermSeq of string
  (* | TermCall (* 不用管 *) *)

type ir_block = {
  label : string;
  mutable insts : ir_inst list;
  mutable terminator : ir_term;
  mutable preds : string list;
  mutable succs : string list;
}

(* 用于 IR 优化的 func 定义 *)
type ir_func_o = { name : string; args : string list; blocks : ir_block list }
type ir_program = Ir_funcs of ir_func list | Ir_funcs_o of ir_func_o list