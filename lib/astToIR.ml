(* astToIR.ml *)
open Ast
open Ir

module Env = Map.Make (String)

module Envs = struct
  type t = operand Env.t list
  let empty : t = [Env.empty]
  let enter (stk : t) : t = Env.empty :: stk
  let exit = function
    | _ :: tl -> tl
    | [] -> failwith "EnvStack.exit: empty stack"
  let add name v = function
    | top :: tl -> Env.add name v top :: tl
    | [] -> failwith "EnvStack.add: empty stack"
  let rec lookup name = function
    | [] -> failwith ("unbound variable: " ^ name)
    | m :: ms -> (match Env.find_opt name m with Some v -> v | None -> lookup name ms)
end

type context = {
  env_stack : Envs.t ref;
  break_lbl : string option;
  continue_lbl : string option;
}

module LabelMap = Map.Make (String)

let tempid = ref 0
let ftemp () = let id = !tempid in incr tempid; Reg ("t" ^ string_of_int id)

let nameid = ref 0
let fname base = let id = !nameid in incr nameid; base ^ "_" ^ string_of_int id

let labelid = ref 0
let irlabid = ref 0
let flabel () = let id = !labelid in incr labelid; "L" ^ string_of_int id

let fIRlabel (labelmap : string LabelMap.t) (l : param) : string * string LabelMap.t =
  match LabelMap.find_opt l labelmap with
  | Some lbl -> (lbl, labelmap)
  | None ->
      let id = !irlabid in incr irlabid;
      let lbl = "LABEL" ^ string_of_int id in
      (lbl, LabelMap.add l lbl labelmap)

let string_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Eq -> "==" | Neq -> "!=" | Less -> "<" | Leq -> "<=" | Greater -> ">"
  | Geq -> ">=" | Land -> "&&" | Lor -> "||"

let string_unop = function Not -> "!" | Plus -> "+" | Minus -> "-"

type stmt_res = Normal of ir_inst list | Returned of ir_inst list
let flatten = function Normal code | Returned code -> code
let ends insts = match List.rev insts with | Goto _ :: _ | Ret _ :: _ -> true | _ -> false

let rec expr_ir (ctx : context) (e : expr) : operand * ir_inst list =
  match e with
  | Number n -> (Imm n, [])
  | ID name -> (Envs.lookup name !(ctx.env_stack), [])
  | Unop (op, e1) ->
      let operand, code = expr_ir ctx e1 in
      let res = ftemp () in
      (res, code @ [ Unop (string_unop op, res, operand) ])
  | Binop (op, e1, e2) ->
      let lhs, c1 = expr_ir ctx e1 in
      let rhs, c2 = expr_ir ctx e2 in
      let dst = ftemp () in
      (dst, (c1 @ c2) @ [ Binop (string_binop op, dst, lhs, rhs) ])
  | Call (f, args) ->
      let codes, oprs =
        List.fold_left (fun (ac, ao) arg -> let o, c = expr_ir ctx arg in (ac @ c, ao @ [o]))
        ([], []) args
      in
      let ret = ftemp () in
      (ret, codes @ [ Call (ret, f, oprs) ])

let rec dstmt = function
  | If (cond, then_b, Some else_b) ->
      let ands = split_and cond in
      if List.length ands > 1 then
        let rec nand = function | [x] -> If(x, then_b, Some else_b) | hd::tl -> If(hd, Block [nand tl], Some else_b) | [] -> Block []
        in nand ands |> dstmt
      else
      let ors = split_or cond in
      if List.length ors > 1 then
        let rec nor = function | [x] -> If(x, then_b, Some else_b) | hd::tl -> If(hd, then_b, Some (nor tl)) | [] -> Block []
        in nor ors |> dstmt
      else If(cond, dstmt then_b, Some (dstmt else_b))
  | If(cond, then_b, None) ->
      let ands = split_and cond in
      if List.length ands > 1 then
        let rec nand = function | [x] -> If(x, then_b, None) | hd::tl -> If(hd, Block [nand tl], None) | [] -> Block []
        in nand ands |> dstmt
      else
      let ors = split_or cond in
      if List.length ors > 1 then
        let rec nor = function | [x] -> If(x, then_b, None) | hd::tl -> If(hd, then_b, Some (nor tl)) | [] -> Block []
        in nor ors |> dstmt
      else If(cond, dstmt then_b, None)
  | While(cond, body) -> While(cond, dstmt body)
  | Block ss -> Block(List.map dstmt ss)
  | other -> other

let rec stmt_res (ctx : context) (s : stmt) : stmt_res =
  match s with
  | Empty -> Normal []
  | ExprStmt e -> let _, code = expr_ir ctx e in Normal code
  | Decl (x, None) ->
      let new_name = fname x in
      ctx.env_stack := Envs.add x (Var new_name) !(ctx.env_stack); Normal []
  | Decl (x, Some e) ->
      let v, c = expr_ir ctx e in let new_name = fname x in
      ctx.env_stack := Envs.add x (Var new_name) !(ctx.env_stack); Normal (c @ [ Assign (Var new_name, v) ])
  | Assign (x, e) ->
      let v, c = expr_ir ctx e in let var = Envs.lookup x !(ctx.env_stack) in Normal (c @ [ Assign (var, v) ])
  | Return None -> Returned [ Ret None ]
  | Return (Some e) -> let v, c = expr_ir ctx e in Returned (c @ [ Ret (Some v) ])
  | If (cond, tstmt, Some fstmt) ->
      let cnd, cc = expr_ir ctx cond in
      let lthen = flabel () and lelse = flabel () and lend = flabel () in
      let then_res = stmt_res ctx tstmt and else_res = stmt_res ctx fstmt in
      let raw_then = flatten then_res in let then_code = if ends raw_then then raw_then else raw_then @ [ Goto lend ] in
      let raw_else = flatten else_res in let else_code = if ends raw_else then raw_else else raw_else @ [ Goto lend ] in
      let code = cc @ [ IfGoto (cnd, lthen); Goto lelse ] @ [ Label lthen ] @ then_code @ [ Label lelse ] @ else_code @ [ Label lend ] in
      (match (then_res, else_res) with Returned _, _ | _, Returned _ -> Returned code | _ -> Normal code)
  | If (cond, tstmt, None) ->
      let cnd, cc = expr_ir ctx cond in let lthen = flabel () and lskip = flabel () in
      let then_res = stmt_res ctx tstmt in let then_code = flatten then_res in
      let code = cc @ [ IfGoto (cnd, lthen); Goto lskip ] @ [ Label lthen ] @ then_code @ [ Label lskip ] in
      Normal code
  | While (cond, body) ->
      let lcond = flabel () and lbody = flabel () and lend = flabel () in
      let ctx_loop = { ctx with break_lbl = Some lend; continue_lbl = Some lcond } in
      let cnd, ccode = expr_ir ctx_loop cond in
      let bcode = flatten (stmt_res ctx_loop body) in
      Normal ([ Goto lcond; Label lcond ] @ ccode @ [ IfGoto (cnd, lbody); Goto lend ] @ [ Label lbody ] @ bcode @ [ Goto lcond; Label lend ])
  | Break -> (match ctx.break_lbl with Some lbl -> Normal [ Goto lbl ] | None -> failwith "break")
  | Continue -> (match ctx.continue_lbl with Some lbl -> Normal [ Goto lbl ] | None -> failwith "continue")
  | Block stmts ->
      ctx.env_stack := Envs.enter !(ctx.env_stack);
      let rec loop acc = function | [] -> Normal acc | hd::tl -> (match stmt_res ctx hd with Returned c -> Returned (acc @ c) | Normal c -> loop (acc @ c) tl) in
      let res = loop [] stmts in
      ctx.env_stack := Envs.exit !(ctx.env_stack); res

let func_ir (f : func_def) : ir_func =
  let des_body = match dstmt (Block f.body) with Block ss -> ss | _ -> f.body in
  let f' = { f with body = des_body } in
  let init_env = List.fold_left (fun m x -> Env.add x (Var x) m) Env.empty f'.params in
  let ctx0 = { env_stack = ref [init_env]; break_lbl = None; continue_lbl = None } in
  let raw_code = flatten (stmt_res ctx0 (Block f'.body)) in
  let bodycode = match List.rev raw_code with Label _ :: rest_rev -> List.rev rest_rev | _ -> raw_code in
  { name = f'.func_name; args = f'.params; body = bodycode }

let pblocks (insts : ir_inst list) : ir_block list =
  let rec split acc curr label labelmap insts = match insts with
    | [] -> if curr = [] then List.rev acc else List.rev ({ label; insts=List.rev curr; terminator=TermRet None; preds=[]; succs=[] } :: acc)
    | Label l :: rest ->
        if curr = [] then let next_label, labelmap' = fIRlabel labelmap l in split acc [] next_label labelmap' rest
        else let next_label, labelmap' = fIRlabel labelmap l in let blk = { label; insts = List.rev curr; terminator = TermSeq next_label; preds = []; succs = [] } in split (blk :: acc) [] next_label labelmap' rest
    | Goto l :: rest ->
        let goto_label, map' = fIRlabel labelmap l in let next_label, map'' = fIRlabel map' ("__b" ^ string_of_int !irlabid) in
        let blk = { label; insts = List.rev curr; terminator = TermGoto goto_label; preds = []; succs = [] } in split (blk :: acc) [] next_label map'' rest
    | IfGoto (cond, l) :: rest ->
        let then_label, map' = fIRlabel labelmap l in let else_label, map'' = fIRlabel map' ("__e" ^ string_of_int !irlabid) in
        let blk = { label; insts = List.rev curr; terminator = TermIf (cond, then_label, else_label); preds = []; succs = [] } in split (blk :: acc) [] else_label map'' rest
    | Ret op :: rest ->
        let next_label, map' = fIRlabel labelmap ("__r" ^ string_of_int !irlabid) in
        let blk = { label; insts = List.rev curr; terminator = TermRet op; preds = []; succs = [] } in split (blk :: acc) [] next_label map' rest
    | inst :: rest -> split acc (inst :: curr) label labelmap rest
  in let entry_label, labelmap = fIRlabel LabelMap.empty "entry" in split [] [] entry_label labelmap insts

let func_iro (f : func_def) : ir_func_o =
  let init_map = List.fold_left (fun m name -> Env.add name (Var name) m) Env.empty f.params in
  let ctx0 = { env_stack = ref [init_map]; break_lbl = None; continue_lbl = None } in
  let bodycode = flatten (stmt_res ctx0 (Block f.body)) in
  let linear_ir = match List.rev bodycode with Label _ :: rest_rev -> List.rev rest_rev | _ -> bodycode in
  let raw_blocks = pblocks linear_ir in
  let pre_opt_func = { name = f.func_name; args = f.params; blocks = raw_blocks } in
  Cfg.optimize pre_opt_func

let program_ir (cu : comp_unit) (optimize_flag : bool) : ir_program =
  if optimize_flag then Ir_funcs_o (List.map func_iro cu)
  else Ir_funcs (List.map func_ir cu)