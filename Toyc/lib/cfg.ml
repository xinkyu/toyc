(* cfg.ml *)
open Ir
module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

type const_state = int option
(* 映射变量名 -> 常量值（或None表示非常量） *)
type const_env = const_state StringMap.t
(*取模*)
let word_mod n =
  let m = Int32.of_int n in
  Int32.to_int (Int32.logand m 0xFFFFFFFFl)

(* 合并多个环境的状态 *)
let merge_envs (envs : const_env list) : const_env =
  if envs = [] then StringMap.empty
  else
    let all_vars = List.fold_left (fun acc env ->
        StringMap.fold (fun k _ acc -> StringSet.add k acc) env acc
      ) StringSet.empty envs in
    StringSet.fold (fun var acc ->
        let states = List.map (fun env ->
            try StringMap.find var env with Not_found -> None
          ) envs in
        let is_same = match states with
          | [] -> true
          | hd::tl -> List.for_all ((=) hd) tl
        in
        if is_same then
          StringMap.add var (List.hd states) acc
        else
          StringMap.add var None acc
      ) all_vars StringMap.empty

let eval_operand env op =
  match op with
  | Var name | Reg name ->
      (try match StringMap.find name env with
       | Some i -> Imm i
       | None -> op
       with Not_found -> op)
  | Imm _ -> op

let eval_binop op op1 op2 =
  match (op1, op2) with
  | (Imm a, Imm b) ->
  (match op with
   | "+" -> Some (word_mod (a + b))
   | "-" -> Some (word_mod (a - b))
   | "*" -> Some (word_mod (a * b))
   | "/" when b <> 0 -> Some (word_mod (a / b))
   | "%" when b <> 0 -> Some (word_mod (a mod b))
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
   | "-" -> Some (word_mod (-a))
   | "+" -> Some (word_mod a)
   | _ -> None)
  | _ -> None

let process_inst env inst =
  match inst with
  | Assign (dst, src) ->
      let src' = eval_operand env src in
      let env' =
        match dst with
        | Var name | Reg name ->
            (match src' with
             | Imm i -> StringMap.add name (Some i) env
             | _ -> StringMap.add name None env)
        | _ -> env
      in
      Assign (dst, src'), env'

  | Binop (op, dst, src1, src2) ->
      let src1' = eval_operand env src1 in
      let src2' = eval_operand env src2 in
      (match eval_binop op src1' src2' with
       | Some i -> Assign (dst, Imm i), StringMap.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Binop (op, dst, src1', src2'), StringMap.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Unop (op, dst, src) ->
      let src' = eval_operand env src in
      (match eval_unop op src' with
       | Some i -> Assign (dst, Imm i), StringMap.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Unop (op, dst, src'), StringMap.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Call (dst, fname, args) ->
      let args' = List.map (eval_operand env) args in
      let env' = match dst with Var v | Reg v -> StringMap.add v None env | _ -> env in
      Call (dst, fname, args'), env'

  | Load (dst, addr) ->
      let addr' = eval_operand env addr in
      let env' = match dst with Var v | Reg v -> StringMap.add v None env | _ -> env in
      Load (dst, addr'), env'

  | Store (addr, value) ->
      let addr' = eval_operand env addr in
      let value' = eval_operand env value in
      Store (addr', value'), env

  | IfGoto (cond, label) ->
      let cond' = eval_operand env cond in
      (* 增强常量折叠: 如果条件是常量，可以直接决定跳转 *)
      (match cond' with
       | Imm 0 -> Goto "__dead_code", env  (* 条件为假，永不跳转 *)
       | Imm _ -> Goto label, env          (* 条件为真，总是跳转 *)
       | _ -> IfGoto (cond', label), env)

  | Ret op_opt ->
      Ret (Option.map (eval_operand env) op_opt), env

  | Goto _ | Label _ as t -> t, env

let process_terminator env term =
  match term with
  | TermIf (cond, l1, l2) -> 
      let cond' = eval_operand env cond in
      (* 增强的常量条件处理 *)
      (match cond' with
       | Imm 0 -> TermGoto l2  (* 条件恒为假，直接跳转到 else 分支 *)
       | Imm _ -> TermGoto l1  (* 条件恒为真，直接跳转到 then 分支 *)
       | _ -> TermIf (cond', l1, l2))
  | TermRet o -> TermRet (Option.map (eval_operand env) o)
  | TermGoto _ | TermSeq _ as t -> t

(* 构建 CFG 并清理不可达块 *)
let build_cfg (blocks : ir_block list) : ir_block list =
  if blocks = [] then [] else
  (* 1. 构造 label -> block 的映射 *)
  let label_map =
    List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks
  in
  (* 2. 清空 preds/succs *)
  List.iter (fun b -> b.preds <- []; b.succs <- []) blocks;
  (* 3. 填充 preds/succs *)
  List.iter (fun b ->
    let add_edge from_lbl to_lbl =
      match StringMap.find_opt to_lbl label_map with
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
      match StringMap.find_opt lbl label_map with
      | Some blk -> List.iter dfs blk.succs
      | None     -> ()
    end
  in
  dfs entry_label;
  (* 5. 过滤并返回可达块，并修剪 succs/preds *)
  let reachable = List.filter (fun b -> Hashtbl.mem visited b.label) blocks in
  let reach_set = List.fold_left (fun s b -> StringMap.add b.label () s) StringMap.empty reachable in
  List.iter (fun b ->
    b.succs <- List.filter (fun l -> StringMap.mem l reach_set) b.succs;
    b.preds <- List.filter (fun l -> StringMap.mem l reach_set) b.preds
  ) reachable;
  reachable

(* 增强的常量传播，更好地处理分支 *)
let constant_propagation (blocks : ir_block list) : ir_block list =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  let in_envs = ref StringMap.empty in
  let out_envs = ref StringMap.empty in
  List.iter (fun b ->
    in_envs := StringMap.add b.label StringMap.empty !in_envs;
    out_envs := StringMap.add b.label StringMap.empty !out_envs
  ) blocks;
  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b.label worklist) blocks;
  while not (Queue.is_empty worklist) do
    let label = Queue.take worklist in
    let blk = StringMap.find label block_map in
    let preds = blk.preds in
    let in_env =
      if preds = [] then StringMap.empty
      else merge_envs (List.map (fun p -> StringMap.find p !out_envs) preds)
    in
    in_envs := StringMap.add label in_env !in_envs;
    let new_insts, out_env = List.fold_left (fun (acc, env) inst ->
      let inst', env' = process_inst env inst in
      acc @ [inst'], env'
    ) ([], in_env) blk.insts in
    let new_term = process_terminator out_env blk.terminator in
    let old_out = StringMap.find label !out_envs in
    if not (StringMap.equal (=) out_env old_out) then begin
      out_envs := StringMap.add label out_env !out_envs;
      List.iter (fun succ -> Queue.add succ worklist) blk.succs
    end;
    blk.insts <- new_insts;
    blk.terminator <- new_term;
  done;
  blocks

(* 新增: 合并基本块 - 消除跳转到跳转的链 *)
let merge_blocks (blocks : ir_block list) : ir_block list =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  
  (* 找到一个标签的最终目标（跟随跳转链） *)
  let rec find_target label visited =
    if List.mem label visited then label (* 防止循环 *)
    else
      match StringMap.find_opt label block_map with
      | Some blk -> 
          (match blk.terminator with
           | TermGoto target when blk.insts = [] -> 
               find_target target (label :: visited)
           | _ -> label)
      | None -> label
  in
  
  (* 更新所有跳转，使其直接跳到最终目标 *)
  List.iter (fun blk ->
    match blk.terminator with
    | TermGoto label -> 
        let final_target = find_target label [] in
        if final_target <> label then
          blk.terminator <- TermGoto final_target
    | TermIf (cond, then_label, else_label) ->
        let final_then = find_target then_label [] in
        let final_else = find_target else_label [] in
        if final_then <> then_label || final_else <> else_label then
          blk.terminator <- TermIf (cond, final_then, final_else)
    | TermSeq label ->
        let final_target = find_target label [] in
        if final_target <> label then
          blk.terminator <- TermSeq final_target
    | _ -> ()
  ) blocks;
  
  (* 重建CFG，清理不可达块 *)
  build_cfg blocks

(* 新增: 简化冗余条件判断 *)
let simplify_conditions (blocks : ir_block list) : ir_block list =
  List.iter (fun blk ->
    match blk.terminator with
    | TermIf (_, then_label, else_label) when then_label = else_label ->
        (* 如果分支相同，直接替换为跳转 *)
        blk.terminator <- TermGoto then_label
    | TermIf (Imm 0, _, else_label) ->
        (* 条件永远为假 *)
        blk.terminator <- TermGoto else_label
    | TermIf (Imm _, then_label, _) ->
        (* 条件永远为真 *)
        blk.terminator <- TermGoto then_label
    | _ -> ()
  ) blocks;
  
  (* 重建CFG，清理不可达块 *)
  build_cfg blocks

(* 增强的优化流程 *)
let optimize blocks =
  blocks 
  |> build_cfg 
  |> constant_propagation 
  |> simplify_conditions
  |> merge_blocks
  |> build_cfg  (* 最后再次构建CFG，确保清理所有不可达块 *)