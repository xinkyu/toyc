(* file: lib/ir.ml *)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

type operand =
  | Reg of string
  | Imm of int
  | Var of string

type ir_inst =
  | Binop of string * operand * operand * operand
  | Unop of string * operand * operand
  | Load of operand * operand
  | Store of operand * operand
  | Goto of string
  | IfGoto of operand * string
  | Label of string
  | Call of operand * string * operand list
  | Ret of operand option
  | Assign of operand * operand

type ir_func = { name : string; args : string list; body : ir_inst list }

type ir_term =
  | TermGoto of string
  | TermIf of operand * string * string
  | TermRet of operand option
  | TermSeq of string

type ir_block = {
  label : string;
  mutable insts : ir_inst list;
  mutable terminator : ir_term;
  mutable preds : string list;
  mutable succs : string list;
  mutable def: StringSet.t;
  mutable use: StringSet.t;
  mutable live_in: StringSet.t;
  mutable live_out: StringSet.t;
}

type ir_func_o = { name : string; args : string list; blocks : ir_block list }

(* --- 新增的类型，用于存放分配结果 --- *)
type allocated_func = {
  name: string;
  args: string list;
  blocks: ir_block list;
  alloc_map: Regalloc.allocation StringMap.t;
  mutable stack_size: int; (* 总栈帧大小 *)
}

(* --- 更新 ir_program 类型以包含新变体 --- *)
type ir_program =
  | Ir_funcs of ir_func list
  | Ir_funcs_o of ir_func_o list
  | Ir_funcs_alloc of allocated_func list