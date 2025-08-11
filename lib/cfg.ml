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
      let dst_name = match dst with Var v | Reg v -> v | _ -> "" in
      (match eval_binop op src1' src2' with
       | Some i -> (* 1. 常量折叠 (已有逻辑) *)
           Assign (dst, Imm i), StringMap.add dst_name (Some i) env
       | None -> (* 2. 尝试代数化简 *)
           (match (op, src1', src2') with
            (* 恒等规则: x + 0 = x, x - 0 = x, x * 1 = x, x / 1 = x *)
            | ("+", v, Imm 0) | ("+", Imm 0, v) ->
                Assign (dst, v), StringMap.add dst_name None env (* 保守更新env *)
            | ("-", v, Imm 0) ->
                Assign (dst, v), StringMap.add dst_name None env (* 保守更新env *)
            | ("*", v, Imm 1) | ("*", Imm 1, v) ->
                Assign (dst, v), StringMap.add dst_name None env (* 保守更新env *)
            | ("/", v, Imm 1) ->
                Assign (dst, v), StringMap.add dst_name None env (* 保守更新env *)

            (* 零规则: x * 0 = 0, x - x = 0 *)
            | ("-", v1, v2) when v1 = v2 ->
                Assign (dst, Imm 0), StringMap.add dst_name (Some 0) env
            | ("*", _, Imm 0) | ("*", Imm 0, _) ->
                Assign (dst, Imm 0), StringMap.add dst_name (Some 0) env

            (* 强度削减: x * 2 -> x + x,  x * -1 -> -x *)
            | ("*", v, Imm 2) | ("*", Imm 2, v) ->
                Binop ("+", dst, v, v), StringMap.add dst_name None env
            | ("*", v, Imm (-1)) ->
                Unop ("-", dst, v), StringMap.add dst_name None env
            | ("*", Imm (-1), v) ->
                Unop ("-", dst, v), StringMap.add dst_name None env
            
            (* 默认: 无法化简，保持原样 *)
            | _ ->
                Binop (op, dst, src1', src2'), StringMap.add dst_name None env
           )
      )

  | Unop (op, dst, src) ->
      let src' = eval_operand env src in
      let dst_name = match dst with Var v | Reg v -> v | _ -> "" in
      (match eval_unop op src' with
       | Some i -> (* 1. 常量折叠 (已有逻辑) *)
           Assign (dst, Imm i), StringMap.add dst_name (Some i) env
       | None -> (* 2. 尝试代数化简 *)
            (match op with
             (* 恒等规则: +x = x *)
             | "+" -> Assign (dst, src'), StringMap.add dst_name None env (* 保守更新env *)
             (* 默认: 无法化简，保持原样 *)
             | _   -> Unop (op, dst, src'), StringMap.add dst_name None env
            )
      )

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

(* 增强：在常量传播时简化条件分支 *)
let process_terminator env term =
  match term with
  | TermIf (cond, l1, l2) ->
      (match eval_operand env cond with
       | Imm 0 -> TermGoto l2 (* 条件为假，跳转到 else 分支 *)
       | Imm _ -> TermGoto l1 (* 条件为非零(真)，跳转到 then 分支 *)
       | v -> TermIf (v, l1, l2))
  | TermRet o -> TermRet (Option.map (eval_operand env) o)
  | TermGoto _ | TermSeq _ as t -> t

(* 构建 CFG 并清理不可达块 *)
let build_cfg (blocks : ir_block list) : ir_block list =
  if blocks = [] then [] else
  let label_map =
    List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks
  in
  List.iter (fun b -> b.preds <- []; b.succs <- []) blocks;
  List.iter (fun b ->
    let add_edge from_lbl to_lbl =
      try let succ = StringMap.find to_lbl label_map in
          b.succs <- to_lbl :: b.succs;
          succ.preds <- from_lbl :: succ.preds
      with Not_found -> ()
    in
    match b.terminator with
    | TermGoto l | TermSeq l -> add_edge b.label l
    | TermIf (_, l1, l2) -> add_edge b.label l1; add_edge b.label l2
    | TermRet _ -> ()
  ) blocks;
  let entry_label = (List.hd blocks).label in
  let visited = Hashtbl.create (List.length blocks) in
  let rec dfs lbl =
    if not (Hashtbl.mem visited lbl) then begin
      Hashtbl.add visited lbl ();
      try let blk = StringMap.find lbl label_map in
          List.iter dfs blk.succs
      with Not_found -> ()
    end
  in
  dfs entry_label;
  let reachable = List.filter (fun b -> Hashtbl.mem visited b.label) blocks in
  let reach_set = List.fold_left (fun s b -> StringMap.add b.label () s) StringMap.empty reachable in
  List.iter (fun b ->
    b.succs <- List.filter (fun l -> StringMap.mem l reach_set) b.succs;
    b.preds <- List.filter (fun l -> StringMap.mem l reach_set) b.preds
  ) reachable;
  reachable

let constant_propagation (blocks : ir_block list) : (ir_block list * bool) =
  if blocks = [] then (blocks, false) else
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  let in_envs = ref StringMap.empty in
  let out_envs = ref StringMap.empty in
  List.iter (fun b ->
    in_envs := StringMap.add b.label StringMap.empty !in_envs;
    out_envs := StringMap.add b.label StringMap.empty !out_envs
  ) blocks;
  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b.label worklist) blocks;
  let changed = ref false in
  while not (Queue.is_empty worklist) do
    let label = Queue.take worklist in
    let blk = StringMap.find label block_map in
    let old_insts = blk.insts in
    let old_term = blk.terminator in
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
    if old_insts <> new_insts || old_term <> new_term then changed := true;
    let old_out = StringMap.find label !out_envs in
    if not (StringMap.equal (=) out_env old_out) then begin
      out_envs := StringMap.add label out_env !out_envs;
      List.iter (fun succ -> if StringMap.mem succ block_map then Queue.add succ worklist) blk.succs
    end;
    blk.insts <- new_insts;
    blk.terminator <- new_term;
  done;
  (blocks, !changed)

let tail_recursion_optimization (func : ir_func_o) : ir_func_o =
  let open Ir in
  if func.blocks = [] then func else
  let entry_label = (List.hd func.blocks).label in
  let current_func_name = func.name in
  let params = func.args in
  let modified = ref false in
  List.iter (fun block ->
    match block.terminator with
    | TermRet (Some ret_val) -> (
        match List.rev block.insts with
        | Call (dst, fname, args) :: rest_rev ->
            if fname = current_func_name && dst = ret_val && List.length params = List.length args then
            begin
              let insts_without_call = List.rev rest_rev in
              let assignments = List.map2 (fun p a -> Assign (Var p, a)) params args in
              block.insts <- insts_without_call @ assignments;
              block.terminator <- TermGoto entry_label;
              modified := true
            end
        | _ -> ()
      )
    | _ -> ()
  ) func.blocks;
  if !modified then { func with blocks = build_cfg func.blocks } else func

(* 修正：块合并只执行一轮，并返回是否修改过的标志 *)
let merge_blocks_pass (blocks : ir_block list) : (ir_block list * bool) =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  let merged_out_tbl = Hashtbl.create (List.length blocks) in
  let modified = ref false in
  List.iter (fun b ->
    if not (Hashtbl.mem merged_out_tbl b.label) then
      match b.terminator with
      | TermGoto target_label | TermSeq target_label ->
        (try
          let target_block = StringMap.find target_label block_map in
          if List.length target_block.preds = 1 && List.hd target_block.preds = b.label then
          begin
            b.insts <- b.insts @ target_block.insts;
            b.terminator <- target_block.terminator;
            Hashtbl.add merged_out_tbl target_label ();
            modified := true
          end
        with Not_found -> ())
      | _ -> ()
  ) blocks;
  (List.filter (fun b -> not (Hashtbl.mem merged_out_tbl b.label)) blocks, !modified)

(* 重构：使用不动点迭代的优化流程 *)
let optimize (func : ir_func_o) : ir_func_o =
  let func_ref = ref { func with blocks = build_cfg func.blocks } in
  
  (* 1. 尾递归优化 (只需运行一次) *)
  func_ref := tail_recursion_optimization !func_ref;

  (* 2. 交替运行常量传播和块合并，直到没有优化可做 *)
  let changed_in_iter = ref true in
  while !changed_in_iter do
    changed_in_iter := false;

    (* 常量传播 *)
    let (cp_blocks, cp_changed) = constant_propagation !func_ref.blocks in
    if cp_changed then
    begin
      changed_in_iter := true;
      (* CP可能简化了分支，需要重建CFG *)
      func_ref := {!func_ref with blocks = build_cfg cp_blocks};
    end;
    
    (* 块合并 *)
    let (merged_blocks, merged_changed) = merge_blocks_pass !func_ref.blocks in
    if merged_changed then
    begin
      changed_in_iter := true;
      (* 合并后需要重建CFG *)
      func_ref := {!func_ref with blocks = build_cfg merged_blocks}
    end
  done;
  !func_ref