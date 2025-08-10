(*astToIR.ml*)
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
  break_lbl : string option; (* break 跳转目标 *)
  continue_lbl : string option; (* continue 跳转目标 *)
}

module LabelMap = Map.Make (String)

let tempid = ref 0

let ftemp () =
  let id = !tempid in
  incr tempid;
  Reg ("t" ^ string_of_int id)

let nameid = ref 0
let fname base = let id = !nameid in incr nameid; base ^ "_" ^ string_of_int id

let labelid = ref 0
let irlabid = ref 0

let flabel () =
  let id = !labelid in
  incr labelid;
  "L" ^ string_of_int id

let fIRlabel (labelmap : string LabelMap.t) (l : param) :
    string * string LabelMap.t =
  (* 先查找 l 是否已经分配了 label，如果有直接返回，否则分配新 label，并写回 map *)
  match LabelMap.find_opt l labelmap with
  | Some lbl -> (lbl, labelmap)
  | None ->
      let id = !irlabid in
      incr irlabid;
      let lbl = "LABEL" ^ string_of_int id in
      let labelmap' = LabelMap.add l lbl labelmap in
      (lbl, labelmap')

(* 操作符到字符串映射 *)
let string_binop = function
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

let string_unop = function Not -> "!" | Plus -> "+" | Minus -> "-"

(* stmt_res 用于处理 return 终止：Normal/Returned 两种结果 *)
type stmt_res = Normal of ir_inst list | Returned of ir_inst list

(* 将 stmt_res 展平为代码列表 *)
let flatten = function Normal code | Returned code -> code

(* 检查代码段最后一条是否是 Goto 指定标签或 Return *)
let ends insts =
  match List.rev insts with
  | Goto _ :: _ -> true
  | Ret _ :: _ -> true
  | _ -> false

(* 表达式转换：返回目标寄存器和 IR 指令列表 *)
let rec expr_ir (ctx : context) (e : expr) : operand * ir_inst list =
  match e with
  | Number n -> (Imm n, [])
  | ID name ->
      let operand = Envs.lookup name !(ctx.env_stack) in
      (operand, [])
  | Unop (op, e1) -> (
      let operand, code = expr_ir ctx e1 in
      match operand with
      | Imm n ->
          let folded =
            match op with
            | Plus -> Imm n (* +n = n *)
            | Minus -> Imm (-n) (* -n *)
            | Not -> Imm (if n = 0 then 1 else 0)
            (* !n *)
          in
          (folded, code)
      | _ ->
          let res = ftemp () in
          (res, code @ [ Unop (string_unop op, res, operand) ]))
  
  | Binop (Land, e1, e2) ->
      let res = ftemp() in
      let l_rhs = flabel() in
      let l_end = flabel() in
      let v1, c1 = expr_ir ctx e1 in
      let code = c1 @ [
          IfGoto(v1, l_rhs);      (* If e1 is non-zero, check e2 *)
          Assign(res, Imm(0));    (* Else, result is 0 *)
          Goto(l_end);
          Label(l_rhs);
      ] in
      let v2, c2 = expr_ir ctx e2 in
      let temp_bool = ftemp() in
      let code = code @ c2 @ [
          Binop("!=", temp_bool, v2, Imm(0)); (* Convert v2 to boolean 0 or 1 *)
          Assign(res, temp_bool);
          Label(l_end);
      ] in
      (res, code)

  | Binop (Lor, e1, e2) ->
      let res = ftemp() in
      let l_rhs = flabel() in
      let l_true = flabel() in
      let l_end = flabel() in
      let v1, c1 = expr_ir ctx e1 in
      let code = c1 @ [
          IfGoto(v1, l_true);      (* If e1 is non-zero, result is 1 *)
          Goto(l_rhs);             (* Else, check e2 *)
      ] in
      let v2, c2 = expr_ir ctx e2 in
      let temp_bool = ftemp() in
      let code = code @ c2 @ [
          Label(l_rhs);
          Binop("!=", temp_bool, v2, Imm(0)); (* Convert v2 to boolean *)
          Assign(res, temp_bool);
          Goto(l_end);

          Label(l_true);
          Assign(res, Imm(1));
          Label(l_end);
      ] in
      (res, code)

  | Binop (op, e1, e2) -> (
      let lhs, c1 = expr_ir ctx e1 in
      let rhs, c2 = expr_ir ctx e2 in
      match (lhs, rhs) with
      | Imm a, Imm b ->
          let folded =
            match op with
            | Add -> Imm (a + b)
            | Sub -> Imm (a - b)
            | Mul -> Imm (a * b)
            | Div -> Imm (a / b)
            | Mod -> Imm (a mod b)
            | Eq -> Imm (if a = b then 1 else 0)
            | Neq -> Imm (if a <> b then 1 else 0)
            | Less -> Imm (if a < b then 1 else 0)
            | Leq -> Imm (if a <= b then 1 else 0)
            | Greater -> Imm (if a > b then 1 else 0)
            | Geq -> Imm (if a >= b then 1 else 0)
            | Lor | Land -> failwith "Never touched"
          in
          (folded, c1 @ c2)
      | _ ->
          let dst = ftemp () in
          (dst, c1 @ c2 @ [ Binop (string_binop op, dst, lhs, rhs) ]))
  | Call (f, args) ->
      (* 参数顺序按出现顺序计算 *)
      let codes, oprs =
        List.fold_left
          (fun (acc_code, acc_opr) arg ->
            let opr, code = expr_ir ctx arg in
            (acc_code @ code, acc_opr @ [ opr ]))
          ([], []) args
      in
      let ret = ftemp () in
      (ret, codes @ [ Call (ret, f, oprs) ])

(* 将 if(cond, then_b, else_b) 里的 cond 展开 *)
let rec dstmt = function
  | If (cond, then_b, Some else_b) ->
      let ands = split_and cond in
      if List.length ands > 1 then
        (* a && b && c => nested if a then if b then if c ... *)
        let rec nand = function
          | [x]    -> If(x, then_b, Some else_b)
          | hd::tl -> If(hd, Block [nand tl], Some else_b)
          | []     -> Block []  (* 理论不会到 *)
        in nand ands |> dstmt
      else
      let ors = split_or cond in
      if List.length ors > 1 then
        (* a || b || c => if a then then_b else if b ... *)
        let rec nor = function
          | [x]    -> If(x, then_b, Some else_b)
          | hd::tl -> If(hd, then_b, Some (nor tl))
          | []     -> Block []
        in nor ors |> dstmt
      else
        (* 原子条件 *)
        If(cond, dstmt then_b, Some (dstmt else_b))

  | If(cond, then_b, None) ->
      (* 类似处理一个分支的 if *)
      let ands = split_and cond in
      if List.length ands > 1 then
        let rec nand = function
          | [x]    -> If(x, then_b, None)
          | hd::tl -> If(hd, Block [nand tl], None)
          | []     -> Block []
        in nand ands |> dstmt
      else
      let ors = split_or cond in
      if List.length ors > 1 then
        let rec nor = function
          | [x]    -> If(x, then_b, None)
          | hd::tl -> If(hd, then_b, Some (nor tl))
          | []     -> Block []
        in nor ors |> dstmt
      else
        If(cond, dstmt then_b, None)

  | While(cond, body) ->
      (* 把 while(cond) body 变成 if(cond) body; while(cond) body *)
      While(cond, dstmt body)

  | Block ss -> Block(List.map dstmt ss)
  | other    -> other

(* 语句翻译，返回 Normal/Returned，支持块作用域、break/continue、return 提前终止 *)
let rec stmt_res (ctx : context) (s : stmt) : stmt_res =
  match s with
  | Empty -> Normal []
  | ExprStmt e ->
      let _, code = expr_ir ctx e in
      Normal code
  | Decl (x, None) ->
      let new_name = fname x in
      ctx.env_stack := Envs.add x (Var new_name) !(ctx.env_stack);
      Normal []
  | Decl (x, Some e) ->
      let v, c = expr_ir ctx e in
      let new_name = fname x in
      ctx.env_stack := Envs.add x (Var new_name) !(ctx.env_stack);
      Normal (c @ [ Assign (Var new_name, v) ])
  | Assign (x, e) ->
      let v, c = expr_ir ctx e in
      let var = Envs.lookup x !(ctx.env_stack) in
      Normal (c @ [ Assign (var, v) ])
  | Return None -> Returned [ Ret None ]
  | Return (Some e) ->
      let v, c = expr_ir ctx e in
      Returned (c @ [ Ret (Some v) ])
  | If (cond, tstmt, Some fstmt) -> (
      let cnd, cc = expr_ir ctx cond in
      let lthen = flabel ()
      and lelse = flabel ()
      and lend = flabel () in
      let then_res = stmt_res ctx tstmt
      and else_res = stmt_res ctx fstmt in
      let raw_then = flatten then_res in
      let then_code =
        if ends raw_then then raw_then
        else raw_then @ [ Goto lend ]
      in
      let raw_else = flatten else_res in
      let else_code =
        if ends raw_else then raw_else
        else raw_else @ [ Goto lend ]
      in
      let code =
        cc
        @ [ IfGoto (cnd, lthen); Goto lelse ]
        @ [ Label lthen ] @ then_code @ [ Label lelse ] @ else_code
        @ [ Label lend ]
      in
      Normal code)
  | If (cond, tstmt, None) ->
      let cnd, cc = expr_ir ctx cond in
      let lthen = flabel () and lskip = flabel () in
      let then_res = stmt_res ctx tstmt in
      let then_code = flatten then_res in
      let code =
        cc
        @ [ IfGoto (cnd, lthen); Goto lskip ]
        @ [ Label lthen ] @ then_code @ [ Label lskip ]
      in
      Normal code
  | While (cond, body) ->
      (* 循环标签 *)
      let lcond = flabel ()
      and lbody = flabel ()
      and lend = flabel () in
      let ctx_loop =
        { ctx with break_lbl = Some lend; continue_lbl = Some lcond }
      in
      let cnd, ccode = expr_ir ctx_loop cond in
      let body_res = stmt_res ctx_loop body in
      let bcode = flatten body_res in
      let code =
        [ Goto lcond; Label lcond ]
        @ ccode
        @ [ IfGoto (cnd, lbody); Goto lend ]
        @ [ Label lbody ] @ bcode @ [ Goto lcond; Label lend ]
      in
      (* 无法从循环体中直接 return：若想支持可在 body_res 捕获 *)
      Normal code
  | Break -> (
      match ctx.break_lbl with
      | Some lbl -> Normal [ Goto lbl ]
      | None -> failwith "break used outside loop")
  | Continue -> (
      match ctx.continue_lbl with
      | Some lbl -> Normal [ Goto lbl ]
      | None -> failwith "continue used outside loop")
  | Block stmts ->
      (* 块作用域隔离 *)
      ctx.env_stack := Envs.enter !(ctx.env_stack);
      let rec loop acc = function
        | [] -> Normal acc
        | hd::tl -> (match stmt_res ctx hd with
            | Returned c -> Returned (acc @ c)
            | Normal c -> loop (acc @ c) tl)
      in
      let res = loop [] stmts in
      ctx.env_stack := Envs.exit !(ctx.env_stack);
      res

(* 函数转换 *)
let func_ir (f : func_def) : ir_func =
  let des_body =
    match dstmt (Block f.body) with
    | Block ss -> ss
    | _        -> f.body
  in
  let f' = { f with body = des_body } in
  (* 初始化 env: 参数映射 *)
  let init_env =
    List.fold_left (fun m x -> Env.add x (Var x) m) Env.empty f'.params
  in
  let ctx0 = { env_stack = ref [init_env]; break_lbl = None; continue_lbl = None } in
  (* 翻译函数体 *)
  let body_res = stmt_res ctx0 (Block f'.body) in
  (* 先拿到全部 IR 指令 *)
  let raw_code = flatten body_res in
  (* 如果末尾恰好是一个孤立 Label，就把它丢掉 *)
  let bodycode =
    match List.rev raw_code with
    | Label _ :: rest_rev -> List.rev rest_rev
    | _ -> raw_code
  in
  (* Add a default return 0 for main if it falls off the end *)
  let final_bodycode =
    if f'.func_name = "main" && not (ends bodycode) then
      bodycode @ [Ret (Some (Imm 0))]
    else
      bodycode
  in
  { name = f'.func_name; args = f'.params; body = final_bodycode }

(* 线性IR -> 过程块IR *)
let pblocks (insts : ir_inst list) : ir_block list =
  let rec split acc curr label labelmap insts =
    match insts with
    | [] -> 
        List.rev acc
        (*| _ -> failwith "Basic block must end with a terminator")*)
    | Label l :: rest -> (
        (* 当前块结束，开启新块 *)
        match curr with
        | [] ->
            let next_label, labelmap' = fIRlabel labelmap l in
            split acc [ Label l ] next_label labelmap' rest
        | _ ->
            let next_label, labelmap' = fIRlabel labelmap l in
            let blk =
              {
                label;
                insts = List.rev curr;
                terminator = TermSeq next_label;
                preds = [];
                succs = [];
              }
            in
            let acc' = blk :: acc in
            split acc' [ Label l ] next_label labelmap' rest)
    | Goto l :: rest ->
        let goto_label, labelmap' = fIRlabel labelmap l in
        (* 刷新一个无意义的 blk, 确保编程者不会出现的 label *)
        let next_label, labelmap'' =
          fIRlabel labelmap' ("__blk" ^ string_of_int !irlabid)
        in
        let blk =
          {
            label;
            insts = List.rev (Goto l :: curr);
            terminator = TermGoto goto_label;
            preds = [];
            succs = [];
          }
        in
        split (blk :: acc) [] next_label labelmap'' rest
    | IfGoto (cond, l) :: rest ->
        let then_label, labelmap' = fIRlabel labelmap l in
        let else_label, labelmap'' =
          fIRlabel labelmap' ("__else" ^ string_of_int !irlabid)
        in
        let blk =
          {
            label;
            insts = List.rev (IfGoto (cond, l) :: curr);
            terminator = TermIf (cond, then_label, else_label);
            preds = [];
            succs = [];
          }
        in
        split (blk :: acc) [] else_label labelmap'' rest
    | Ret op :: rest ->
        let next_label, labelmap' =
          fIRlabel labelmap ("__ret" ^ string_of_int !irlabid)
        in
        let blk =
          {
            label;
            insts = List.rev (Ret op :: curr);
            terminator = TermRet op;
            preds = [];
            succs = [];
          }
        in
        split (blk :: acc) [] next_label labelmap' rest
    | inst :: rest -> split acc (inst :: curr) label labelmap rest
  in
  (* 确保用户不使用 entry 标签 *)
  let entry_label, labelmap = fIRlabel LabelMap.empty "entry" in
  split [] [] entry_label labelmap insts

(* 优化版本的 ir 控制块 *)
let func_iro (f : func_def) : ir_func_o =
  let init_map =
    List.fold_left
      (fun m name -> Env.add name (Var name) m)
      Env.empty f.params
  in
   let ctx0 = { env_stack = ref [init_map]; break_lbl = None; continue_lbl = None } in
  let bodycode = stmt_res ctx0 (Block f.body) |> flatten in
  let linear_ir =
    (* 额外处理孤立的 label *)
    match List.rev bodycode with
    | Label _ :: rest_rev -> List.rev rest_rev
    | _ -> bodycode
  in
  let raw_blocks = pblocks linear_ir in
  (* 构建前驱/后继关系，并剔除空块/重复块 *)
  let cfg_blocks = Cfg.build_cfg raw_blocks in
  let opt_blocks = Cfg.optimize cfg_blocks in
  { name = f.func_name; args = f.params; blocks = opt_blocks }

(* 编译单元转换 *)
let program_ir (cu : comp_unit) (optimize_flag : bool) : ir_program =
  if optimize_flag then Ir_funcs_o (List.map func_iro cu)
  else Ir_funcs (List.map func_ir cu)