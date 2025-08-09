(* file: cfg.ml *)
open Ir
(* StringSet 已经移到 ir.ml, 这里不再需要 *)
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
      IfGoto (eval_operand env cond, label), env

  | Ret op_opt ->
      Ret (Option.map (eval_operand env) op_opt), env

  | Goto _ | Label _ as t -> t, env

let process_terminator env term =
  match term with
  | TermIf (cond, l1, l2) -> TermIf (eval_operand env cond, l1, l2)
  | TermRet o -> TermRet (Option.map (eval_operand env) o)
  | TermGoto _ | TermSeq _ as t -> t

(* ---- 从这里开始是为活跃性分析新增的代码 ---- *)

(* 辅助函数，从 operand 中提取虚拟寄存器名 *)
let vreg_of_operand = function
  | Reg s | Var s -> Some s
  | Imm _ -> None

let add_vreg_to_set set op =
  match vreg_of_operand op with
  | Some name -> StringSet.add name set
  | None -> set

(* 计算单条指令的 def 和 use 集合 *)
let inst_def_use (inst: ir_inst) : (StringSet.t * StringSet.t) =
  match inst with
  | Binop (_, dst, lhs, rhs) -> (* t1 = t2 + t3 *)
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set (add_vreg_to_set StringSet.empty lhs) rhs in
      (def, use)
  | Unop (_, dst, src) -> (* t1 = -t2 *)
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set StringSet.empty src in
      (def, use)
  | Assign (dst, src) -> (* t1 = t2 *)
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set StringSet.empty src in
      (def, use)
  | Call (dst, _, args) -> (* t1 = call f(args) *)
      let def = add_vreg_to_set StringSet.empty dst in
      let use = List.fold_left add_vreg_to_set StringSet.empty args in
      (def, use)
  | Store (addr, value) -> (* *t1 = t2 *)
      let use = add_vreg_to_set (add_vreg_to_set StringSet.empty addr) value in
      (StringSet.empty, use)
  | IfGoto (cond, _) -> (* if t1 goto L *)
      (StringSet.empty, add_vreg_to_set StringSet.empty cond)
  | Ret (Some op) -> (* return t1 *)
      (StringSet.empty, add_vreg_to_set StringSet.empty op)
  | Load (dst, src) -> (* t1 = *t2 *)
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set StringSet.empty src in
      (def, use)
  | _ -> (* Goto, Label, Ret None *)
      (StringSet.empty, StringSet.empty)

(* 计算并填充单个块的 def 和 use 集合 *)
let compute_block_def_use (b: ir_block) =
  let block_def, block_use =
    List.fold_left (fun (acc_def, acc_use) inst ->
      let inst_def, inst_use = inst_def_use inst in
      (* use = (use U inst_use) - def *)
      let new_use = StringSet.union acc_use (StringSet.diff inst_use acc_def) in
      (* def = def U inst_def *)
      let new_def = StringSet.union acc_def inst_def in
      (new_def, new_use)
    ) (StringSet.empty, StringSet.empty) b.insts
  in
  (* 别忘了处理终结指令 (terminator) *)
  let term_use = match b.terminator with
    | TermIf (cond, _, _) -> add_vreg_to_set StringSet.empty cond
    | TermRet (Some op) -> add_vreg_to_set StringSet.empty op
    | _ -> StringSet.empty
  in
  b.def <- block_def;
  b.use <- StringSet.union block_use (StringSet.diff term_use block_def)

(* 活跃性分析主函数 *)
let liveness_analysis (blocks: ir_block list) =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in

  (* 1. 初始化所有块 *)
  List.iter (fun b ->
    compute_block_def_use b; (* 计算 def/use *)
    b.live_in <- StringSet.empty;  (* 初始化 live_in/live_out *)
    b.live_out <- StringSet.empty;
  ) blocks;

  (* 2. 工作列表算法 *)
  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b worklist) blocks; (* 初始将所有块加入列表 *)

  while not (Queue.is_empty worklist) do
    let b = Queue.take worklist in

    (* 3. 更新 live_out[b] = U_{s in succ[b]} live_in[s] *)
    let new_live_out =
      List.fold_left (fun acc succ_label ->
        match StringMap.find_opt succ_label block_map with
        | Some succ_block -> StringSet.union acc succ_block.live_in
        | None -> acc
      ) StringSet.empty b.succs
    in
    b.live_out <- new_live_out;

    (* 4. 更新 live_in[b] = use[b] U (live_out[b] - def[b]) *)
    let old_live_in = b.live_in in
    let new_live_in = StringSet.union b.use (StringSet.diff b.live_out b.def) in
    b.live_in <- new_live_in;

    (* 5. 如果 live_in 变化，将前驱加入工作列表 *)
    if not (StringSet.equal old_live_in new_live_in) then
      List.iter (fun pred_label ->
        match StringMap.find_opt pred_label block_map with
        | Some pred_block -> Queue.add pred_block worklist
        | None -> ()
      ) b.preds
  done

(* ---- 活跃性分析代码结束 ---- *)


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
    | TermGoto l -> add_edge b.label l
    | TermSeq l -> add_edge b.label l
    | TermIf (_, l1, l2) -> add_edge b.label l1; add_edge b.label l2
    | TermRet _ -> ()
  ) blocks;
  (* 4. 不可达块清理：从入口执行 DFS *)
  let entry_label = (List.hd blocks).label in
  let visited = Hashtbl.create (List.length blocks) in
  let rec dfs lbl =
    if not (Hashtbl.mem visited lbl) then begin
      Hashtbl.add visited lbl ();
      match StringMap.find_opt lbl label_map with
      | Some blk -> List.iter dfs blk.succs
      | None -> ()
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

(* 更新后的 optimize 函数 *)
let optimize blocks =
  let reachable_blocks = build_cfg blocks in
  let propagated_blocks = constant_propagation reachable_blocks in
  (* 在这里调用新的分析 *)
  liveness_analysis propagated_blocks;
  propagated_blocks