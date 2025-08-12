(* cfg.ml *)
open Ir
module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(* A module to manage block-level data for dataflow analyses *)
module BlockMap = Map.Make(String)

type const_state = IsConst of int | NotAConst

type const_env = const_state StringMap.t

(*******************************************************************)
(* CFG Construction and Utilities *)
(*******************************************************************)

let build_cfg (blocks : ir_block list) : ir_block list =
  if blocks = [] then [] else
  let label_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
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
      try let blk = StringMap.find lbl label_map in List.iter dfs blk.succs
      with Not_found -> () end in
  dfs entry_label;
  let reachable = List.filter (fun b -> Hashtbl.mem visited b.label) blocks in
  let reach_set = List.fold_left (fun s b -> StringMap.add b.label () s) StringMap.empty reachable in
  List.iter (fun b ->
    b.succs <- List.filter (fun l -> StringMap.mem l reach_set) b.succs;
    b.preds <- List.filter (fun l -> StringMap.mem l reach_set) b.preds
  ) reachable;
  reachable

(*******************************************************************)
(* Constant and Copy Propagation *)
(*******************************************************************)

let merge_envs (envs : const_env list) : const_env =
  if envs = [] then StringMap.empty
  else
    let all_vars = List.fold_left (fun acc env -> StringMap.fold (fun k _ acc -> StringSet.add k acc) env acc) StringSet.empty envs in
    StringSet.fold (fun var acc ->
      let states = List.map (fun env -> try StringMap.find var env with Not_found -> NotAConst) envs in
      let first_state = List.hd states in
      let all_same = List.for_all (fun s -> s = first_state) (List.tl states) in
      if all_same && first_state <> NotAConst then StringMap.add var first_state acc
      else StringMap.add var NotAConst acc
    ) all_vars StringMap.empty

let eval_operand env op =
  match op with
  | Var name | Reg name -> (try match StringMap.find name env with IsConst i -> Imm i | NotAConst -> op with Not_found -> op)
  | Imm _ -> op

let eval_binop op v1 v2 = match v1, v2 with
  | Imm a, Imm b ->
      let a32, b32 = Int32.of_int a, Int32.of_int b in
      let res = match op with
        | "+" -> Some (Int32.add a32 b32) | "-" -> Some (Int32.sub a32 b32)
        | "*" -> Some (Int32.mul a32 b32)
        | "/" when b <> 0 -> Some (Int32.div a32 b32) | "%" when b <> 0 -> Some (Int32.rem a32 b32)
        | "==" -> Some (if a = b then 1l else 0l) | "!=" -> Some (if a <> b then 1l else 0l)
        | "<" -> Some (if a < b then 1l else 0l) | "<=" -> Some (if a <= b then 1l else 0l)
        | ">" -> Some (if a > b then 1l else 0l) | ">=" -> Some (if a >= b then 1l else 0l)
        | _ -> None
      in Option.map Int32.to_int res
  | _ -> None

let eval_unop op v1 = match v1 with
  | Imm a ->
      let a32 = Int32.of_int a in
      let res = match op with
        | "!" -> Some (if a = 0 then 1l else 0l)
        | "-" -> Some (Int32.neg a32) | "+" -> Some a32
        | _ -> None
      in Option.map Int32.to_int res
  | _ -> None

let const_prop_transfer_inst env inst =
  let get_name op = match op with Var s | Reg s -> s | _ -> "" in
  let dst_name = match inst with Binop(_,d,_,_)|Unop(_,d,_)|Assign(d,_)|Load(d,_)|Call(d,_,_) -> get_name d | _ -> "" in
  let new_inst, new_state = match inst with
    | Assign (dst, src) ->
        let src' = eval_operand env src in
        let new_state = match src' with Imm i -> IsConst i | _ -> NotAConst in
        Assign(dst, src'), new_state
    | Binop (op, dst, src1, src2) ->
        let s1' = eval_operand env src1 and s2' = eval_operand env src2 in
        (match eval_binop op s1' s2' with
         | Some i -> Assign (dst, Imm i), IsConst i
         | None -> Binop (op, dst, s1', s2'), NotAConst)
    | Unop (op, dst, src) ->
        let s' = eval_operand env src in
        (match eval_unop op s' with
         | Some i -> Assign (dst, Imm i), IsConst i
         | None -> Unop (op, dst, s'), NotAConst)
    | Call (dst, fname, args) -> Call (dst, fname, List.map (eval_operand env) args), NotAConst
    | other -> other, NotAConst
  in
  let new_env = if dst_name <> "" then StringMap.add dst_name new_state env else env in
  new_inst, new_env

let constant_propagation (blocks : ir_block list) : (ir_block list * bool) =
  if blocks = [] then ([], false) else
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  let out_envs = ref (List.fold_left (fun m b -> StringMap.add b.label StringMap.empty m) StringMap.empty blocks) in
  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b.label worklist) blocks;
  let changed = ref false in
  while not (Queue.is_empty worklist) do
    let label = Queue.take worklist in
    let blk = StringMap.find label block_map in
    let preds = blk.preds in
    let in_env = if preds = [] then StringMap.empty else merge_envs (List.map (fun p -> StringMap.find p !out_envs) preds) in
    let old_insts = blk.insts and old_term = blk.terminator in
    let (new_insts, out_env) = List.fold_left (fun (is, e) i -> let i', e' = const_prop_transfer_inst e i in (is@[i'], e')) ([], in_env) blk.insts in
    let new_term = match blk.terminator with
      | TermIf (cond, l1, l2) -> (match eval_operand out_env cond with Imm 0 -> TermGoto l2 | Imm _ -> TermGoto l1 | v -> TermIf (v, l1, l2))
      | TermRet o -> TermRet (Option.map (eval_operand out_env) o)
      | other -> other
    in
    if old_insts <> new_insts || old_term <> new_term then changed := true;
    let old_out = StringMap.find label !out_envs in
    if not (StringMap.equal (=) out_env old_out) then begin
      out_envs := StringMap.add label out_env !out_envs;
      List.iter (fun succ -> if StringMap.mem succ block_map then Queue.add succ worklist) blk.succs
    end;
    blk.insts <- new_insts; blk.terminator <- new_term;
  done;
  (blocks, !changed)

(*******************************************************************)
(* Dead Code Elimination *)
(*******************************************************************)

module VarSet = StringSet
let op_to_set op = match op with Var s | Reg s -> VarSet.singleton s | Imm _ -> VarSet.empty
let use inst = match inst with
  | Binop (_, _, s1, s2) -> VarSet.union (op_to_set s1) (op_to_set s2)
  | Unop (_, _, s) | Assign (_, s) | Load (_, s) -> op_to_set s
  | Store (a, v) -> VarSet.union (op_to_set a) (op_to_set v)
  | Call (_, _, args) -> List.fold_left VarSet.union VarSet.empty (List.map op_to_set args)
  | _ -> VarSet.empty
let def inst = match inst with
  | Binop (_, d, _, _) | Unop (_, d, _) | Assign (d, _) | Load (d, _) | Call (d, _, _) -> op_to_set d
  | _ -> VarSet.empty
let is_critical inst = match inst with Store _ | Call _ -> true | _ -> false

let dead_code_elimination (blocks: ir_block list) : (ir_block list * bool) =
  if blocks = [] then ([], false) else
  let module B = StringMap in
  let live_in = ref (B.map (fun _ -> VarSet.empty) (B.of_list (List.map (fun b -> (b.label, b)) blocks))) in
  let live_out = ref !live_in in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun b ->
      let new_live_out = List.fold_left (fun s l -> VarSet.union s (B.find l !live_in)) VarSet.empty b.succs in
      if not (VarSet.equal new_live_out (B.find b.label !live_out)) then (live_out := B.add b.label new_live_out !live_out; changed := true);
      let term_use = match b.terminator with TermIf(c,_,_) -> op_to_set c | TermRet(Some o) -> op_to_set o | _ -> VarSet.empty in
      let live = VarSet.union term_use new_live_out in
      let block_live = List.fold_right (fun i a -> VarSet.union (use i) (VarSet.diff a (def i))) b.insts live in
      if not (VarSet.equal block_live (B.find b.label !live_in)) then (live_in := B.add b.label block_live !live_in; changed := true)
    ) (List.rev blocks)
  done;
  let dce_changed = ref false in
  List.iter (fun b ->
    let term_use = match b.terminator with TermIf(c,_,_) -> op_to_set c | TermRet(Some o) -> op_to_set o | _ -> VarSet.empty in
    let live = ref (VarSet.union term_use (B.find b.label !live_out)) in
    let new_insts = List.fold_right (fun inst acc ->
      let def_set = def inst in
      if not (is_critical inst) && VarSet.is_empty (VarSet.inter def_set !live) then (dce_changed := true; acc)
      else (live := VarSet.union (use inst) (VarSet.diff !live def_set); inst :: acc)
    ) b.insts [] in
    if List.length new_insts <> List.length b.insts then dce_changed := true;
    b.insts <- new_insts
  ) blocks;
  (blocks, !dce_changed)

(*******************************************************************)
(* Other Optimizations & Main Loop *)
(*******************************************************************)

let tail_recursion_optimization (func : ir_func_o) : (ir_func_o * bool) =
  let open Ir in if func.blocks = [] then (func, false) else
  let entry_label = (List.hd func.blocks).label in
  let current_func_name = func.name and params = func.args in
  let modified = ref false in
  List.iter (fun block ->
    match block.terminator with
    | TermRet (Some ret_val) ->
        (match List.rev block.insts with
        | Assign(dst_assign, src_assign) :: Call(dst_call, fname, args) :: rest_rev
           when dst_assign = ret_val && src_assign = dst_call && fname = current_func_name && List.length params = List.length args ->
            let assignments = List.map2 (fun p a -> Assign (Var p, a)) params args in
            block.insts <- (List.rev rest_rev) @ assignments;
            block.terminator <- TermGoto entry_label;
            modified := true
        | Call (dst, fname, args) :: rest_rev
          when fname = current_func_name && dst = ret_val && List.length params = List.length args ->
            let assignments = List.map2 (fun p a -> Assign (Var p, a)) params args in
            block.insts <- (List.rev rest_rev) @ assignments;
            block.terminator <- TermGoto entry_label;
            modified := true
        | _ -> ())
    | _ -> ()
  ) func.blocks;
  (func, !modified)

let optimize (func : ir_func_o) : ir_func_o =
  let func_ref = ref { func with blocks = build_cfg func.blocks } in
  let changed_in_iter = ref true in
  while !changed_in_iter do
    changed_in_iter := false;
    let run_pass pass =
      let (new_blocks, changed) = pass !func_ref.blocks in
      if changed then changed_in_iter := true;
      (* FIX: Added missing curly braces for record update syntax *)
      { !func_ref with blocks = build_cfg new_blocks }
    in
    func_ref := run_pass constant_propagation;
    func_ref := run_pass dead_code_elimination;
    let (tro_func, tro_changed) = tail_recursion_optimization !func_ref in
    if tro_changed then (changed_in_iter := true; func_ref := {tro_func with blocks = build_cfg tro_func.blocks});
  done;
  !func_ref