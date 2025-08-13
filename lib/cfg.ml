(* cfg.ml *)
open Ir
module s_set = Set.Make(String)
module s_map = Map.Make(String)

type const_state = int option
(* 映射变量名 -> 常量值（或None表示非常量） *)
type const_env = const_state s_map.t
(*取模*)
let w_mod n =
    Int32.to_int (Int32.logand m 0xFFFFFFFFl)

(* 合并多个环境的状态 *)
let m_envs (envs : const_env list) : const_env =
  if envs = [] then s_map.empty
  else
    let all_vars = List.fold_left (fun acc env ->
        s_map.fold (fun k _ acc -> s_set.add k acc) env acc
      ) s_set.empty envs in
    s_set.fold (fun var acc ->
        let states = List.map (fun env ->
            try s_map.find var env with Not_found -> None
          ) envs in
        let is_same = match states with
          | [] -> true
          | hd::tl -> List.for_all ((=) hd) tl
        in
        if is_same then
          s_map.add var (List.hd states) acc
        else
          s_map.add var None acc
      ) all_vars s_map.empty

let eval_oper env op =
  match op with
  | Var name | Reg name ->
      (try match s_map.find name env with
       | Some i -> Imm i
       | None -> op
       with Not_found -> op)
  | Imm _ -> op

let eval_binop op op1 op2 =
  match (op1, op2) with
  | (Imm a, Imm b) ->
  (match op with
   | "+" -> Some (w_mod (a + b))
   | "-" -> Some (w_mod (a - b))
   | "*" -> Some (w_mod (a * b))
   | "/" when b <> 0 -> Some (w_mod (a / b))
   | "%" when b <> 0 -> Some (w_mod (a mod b))
   | "==" -> Some (if a = b then 1 else 0)
   | "!=" -> Some (if a <> b then 1 else 0)
   | "<" -> Some (if a < b then 1 else 0)
   | "<=" -> Some (if a <= b then 1 else 0)
   | ">" -> Some (if a > b then 1 else 0)
   | ">=" -> Some (if a >= b then 1 else 0)
   | _ -> None)
  | _ -> None

let eval_unop op op1 =
  match op1 with
  | Imm a ->
  (match op with
   | "!" -> Some (if a = 0 then 1 else 0)
   | "-" -> Some (w_mod (-a))
   | "+" -> Some (w_mod a)
   | _ -> None)
  | _ -> None

let p_inst env inst =
  match inst with
  | Assign (dst, src) ->
      let src' = eval_oper env src in
      let env' =
        match dst with
        | Var name | Reg name ->
            (match src' with
             | Imm i -> s_map.add name (Some i) env
             | _ -> s_map.add name None env)
        | _ -> env
      in
      Assign (dst, src'), env'

  | Binop (op, dst, src1, src2) ->
      let src1' = eval_oper env src1 in
      let src2' = eval_oper env src2 in
      (match eval_binop op src1' src2' with
       | Some i -> Assign (dst, Imm i), s_map.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Binop (op, dst, src1', src2'), s_map.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Unop (op, dst, src) ->
      let src' = eval_oper env src in
      (match eval_unop op src' with
       | Some i -> Assign (dst, Imm i), s_map.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Unop (op, dst, src'), s_map.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Call (dst, fname, args) ->
      let args' = List.map (eval_oper env) args in
      let env' = match dst with Var v | Reg v -> s_map.add v None env | _ -> env in
      Call (dst, fname, args'), env'

  | Load (dst, addr) ->
      let addr' = eval_oper env addr in
      let env' = match dst with Var v | Reg v -> s_map.add v None env | _ -> env in
      Load (dst, addr'), env'

  | Store (addr, value) ->
      let addr' = eval_oper env addr in
      let value' = eval_oper env value in
      Store (addr', value'), env

  | IfGoto (cond, label) ->
      IfGoto (eval_oper env cond, label), env

  | Ret op_opt ->
      Ret (Option.map (eval_oper env) op_opt), env

  | Goto _ | Label _ as t -> t, env

let process_terminator env term =
  match term with
  | TermIf (cond, l1, l2) -> TermIf (eval_oper env cond, l1, l2)
  | TermRet o -> TermRet (Option.map (eval_oper env) o)
  | TermGoto _ | TermSeq _ as t -> t

(* 构建 CFG 并清理不可达块 *)
let b_cfg (blocks : ir_block list) : ir_block list =
  if blocks = [] then [] else
  (* 1. 构造 label -> block 的映射 *)
  let label_map =
    List.fold_left (fun m b -> s_map.add b.label b m) s_map.empty blocks
  in
  (* 2. 清空 preds/succs *)
  List.iter (fun b -> b.preds <- []; b.succs <- []) blocks;
  (* 3. 填充 preds/succs *)
  List.iter (fun b ->
    let add_edge from_lbl to_lbl =
      match s_map.find_opt to_lbl label_map with
      | Some succ ->
          b.succs <- to_lbl :: b.succs;
          succ.preds <- from_lbl :: succ.preds
      | None -> ()  (* 忽略不存在的目标 *)
    in
    match b.terminator with
    | TermGoto l        -> add_edge b.label l
    | TermSeq l         -> add_edge b.label l
    | TermIf (_, l1, l2) -> add_edge b.label l1; add_edge b.label l2
    | TermRet _         -> ()
  ) blocks;
  (* 4. 不可达块清理：从入口执行 DFS *)
  let entry_label = (List.hd blocks).label in
  let visited = Hashtbl.create (List.length blocks) in
  let rec dfs lbl =
    if not (Hashtbl.mem visited lbl) then begin
      Hashtbl.add visited lbl ();
      match s_map.find_opt lbl label_map with
      | Some blk -> List.iter dfs blk.succs
      | None     -> ()
    end
  in
  dfs entry_label;
  (* 5. 过滤并返回可达块，并修剪 succs/preds *)
  let reachable = List.filter (fun b -> Hashtbl.mem visited b.label) blocks in
  let reach_set = List.fold_left (fun s b -> s_map.add b.label () s) s_map.empty reachable in
  List.iter (fun b ->
    b.succs <- List.filter (fun l -> s_map.mem l reach_set) b.succs;
    b.preds <- List.filter (fun l -> s_map.mem l reach_set) b.preds
  ) reachable;
  reachable

let const_pro (blocks : ir_block list) : ir_block list =
  let block_map = List.fold_left (fun m b -> s_map.add b.label b m) s_map.empty blocks in
  let in_envs = ref s_map.empty in
  let out_envs = ref s_map.empty in
  List.iter (fun b ->
    in_envs := s_map.add b.label s_map.empty !in_envs;
    out_envs := s_map.add b.label s_map.empty !out_envs
  ) blocks;
  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b.label worklist) blocks;
  while not (Queue.is_empty worklist) do
    let label = Queue.take worklist in
    let blk = s_map.find label block_map in
    let preds = blk.preds in
    let in_env =
      if preds = [] then s_map.empty
      else m_envs (List.map (fun p -> s_map.find p !out_envs) preds)
    in
    in_envs := s_map.add label in_env !in_envs;
    let new_insts, out_env = List.fold_left (fun (acc, env) inst ->
      let inst', env' = p_inst env inst in
      acc @ [inst'], env'
    ) ([], in_env) blk.insts in
    let new_term = process_terminator out_env blk.terminator in
    let old_out = s_map.find label !out_envs in
    if not (s_map.equal (=) out_env old_out) then begin
      out_envs := s_map.add label out_env !out_envs;
      List.iter (fun succ -> Queue.add succ worklist) blk.succs
    end;
    blk.insts <- new_insts;
    blk.terminator <- new_term;
  done;
  blocks

let optimize blocks =
  blocks |> b_cfg |> const_pro