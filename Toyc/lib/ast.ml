(* 基本类型定义 *)
type typ =
  | TInt
  (* 整数类型 *)
  | TVoid (* 空类型 *)

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | Neq
  | Less
  | Leq
  | Greater
  | Geq
  | Land
  | Lor

type unop = Not | Plus | Minus

type expr =
  | Binop of binop * expr * expr
  | Unop of unop * expr
  | ID of string
  | Number of int
  | Call of string * expr list

(* 语句 *)
type stmt =
  | Block of stmt list (* 语句块 {...} *)
  | Empty (* 空语句 ; *)
  | ExprStmt of expr (* 表达式语句 *)
  | Decl of string * expr option (* 变量声明（带or不带初始化） *)
  | Assign of string * expr (* 赋值语句 *)
  | If of expr * stmt * stmt option (* if语句（else可选） *)
  | While of expr * stmt (* while循环 *)
  | Break (* break语句 *)
  | Continue (* continue语句 *)
  | Return of expr option (* return语句（返回值可选） *)

(* 函数参数 *)
type param = string (* 参数名（类型固定为int） *)

(* 函数定义 *)
type func_def = {
  ret_type : typ; (* 返回类型 *)
  func_name : string; (* 函数名 *)
  params : param list (* 参数列表 *);
  body : stmt list (* 函数体（语句列表） *);
}

(* 编译单元（整个程序） *)
type comp_unit = func_def list (* 函数定义列表 *)

let rec split_and = function
  | Binop (Land, x, y) -> split_and x @ split_and y
  | e -> [e]

(* 拆成一串 || 子表达式 *)
let rec split_or = function
  | Binop (Lor, x, y) -> split_or x @ split_or y
  | e -> [e]