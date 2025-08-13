open Ast

let stringtotyp = function TInt -> "int" | TVoid -> "void"

let stringtobinop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Eq -> "=="
  | Neq -> "!="
  | Less -> "<"
  | Leq -> "<="
  | Greater -> ">"
  | Geq -> ">="
  | Land -> "&&"
  | Lor -> "||"

let stringtounop = function Not -> "!" | Plus -> "+" | Minus -> "-"

let rec stringtoexpr = function
  | Number n -> Printf.sprintf "Number(%d)" n
  | ID s -> Printf.sprintf "ID(%s)" s
  | Call (fname, args) ->
      Printf.sprintf "Call(%s, [%s])" fname
        (String.concat "; " (List.map stringtoexpr args))
  | Binop (op, e1, e2) ->
      Printf.sprintf "Binop(%s, %s, %s)" (stringtobinop op)
        (stringtoexpr e1) (stringtoexpr e2)
  | Unop (op, e) ->
      Printf.sprintf "Unop(%s, %s)" (stringtounop op) (stringtoexpr e)

let rec stringtostmt = function
  | Block stmts ->
      Printf.sprintf "Block([\n  %s\n])"
        (String.concat ";\n  " (List.map stringtostmt stmts))
  | Empty -> "Empty"
  | ExprStmt e -> Printf.sprintf "ExprStmt(%s)" (stringtoexpr e)
  | Assign (id, e) -> Printf.sprintf "Assign(%s, %s)" id (stringtoexpr e)
  | Decl (id, None) -> Printf.sprintf "Decl(%s)" id
  | Decl (id, Some e) -> Printf.sprintf "Decl(%s, %s)" id (stringtoexpr e)
  | If (cond, s1, None) ->
      Printf.sprintf "If(%s, %s)" (stringtoexpr cond) (stringtostmt s1)
  | If (cond, s1, Some s2) ->
      Printf.sprintf "If(%s, %s, %s)" (stringtoexpr cond) (stringtostmt s1)
        (stringtostmt s2)
  | While (cond, body) ->
      Printf.sprintf "While(%s, %s)" (stringtoexpr cond) (stringtostmt body)
  | Break -> "Break"
  | Continue -> "Continue"
  | Return None -> "Return"
  | Return (Some e) -> Printf.sprintf "Return(%s)" (stringtoexpr e)

let stringtofunc_def f =
  Printf.sprintf "Function %s(%s) : %s {\n%s\n}" f.func_name
    (String.concat ", " f.params)
    (stringtotyp f.ret_type)
    (String.concat "\n" (List.map (fun s -> "  " ^ stringtostmt s) f.body))

let stringtocomp_unit (unit : comp_unit) : string =
  String.concat "\n\n" (List.map stringtofunc_def unit)