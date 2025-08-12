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
(* Loop-Invariant Code Motion (LICM) *)
(*******************************************************************)

(* 计算支配树 *)
let compute_dominators (blocks : ir_block list) : (StringSet.t StringMap.t * StringSet.t StringMap.t) =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  let all_nodes = StringSet.of_list (List.map (fun b -> b.label) blocks) in
  let entry_label = (List.hd blocks).label in
  
  (* 初始化支配集合：入口节点只被自己支配，其他节点被所有节点支配 *)
  let init_doms = StringMap.fold (fun label _ acc ->
    if label = entry_label then
      StringMap.add label (StringSet.singleton label) acc
    else
      StringMap.add label all_nodes acc
  ) block_map StringMap.empty in
  
  (* 计算一个节点的支配者集合 *)
  let compute_new_doms curr_label doms =
    let curr_block = StringMap.find curr_label block_map in
    let pred_doms = 
      match curr_block.preds with
      | [] -> StringSet.singleton curr_label  (* 入口节点 *)
      | p::ps -> 
          List.fold_left (fun acc pred ->
            StringSet.inter acc (StringMap.find pred doms)
          ) (StringMap.find p doms) ps
    in
    StringSet.add curr_label pred_doms
  in
  
  (* 迭代计算支配关系直到不变 *)
  let rec fix_point doms =
    let new_doms = StringMap.fold (fun label _ acc ->
      StringMap.add label (compute_new_doms label doms) acc
    ) block_map StringMap.empty in
    if StringMap.equal StringSet.equal doms new_doms then doms
    else fix_point new_doms
  in
  
  let dominators = fix_point init_doms in
  
  (* 计算严格支配者集合 *)
  let strict_dominators = StringMap.map (fun dom_set ->
    StringSet.remove (StringSet.choose dom_set) dom_set  (* 移除节点自身 *)
  ) dominators in
  
  (dominators, strict_dominators)

(* 识别循环 *)
let identify_loops (blocks : ir_block list) (dominators : StringSet.t StringMap.t) : (string * string list) list =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  
  (* 检查是否存在返祖边 *)
  let is_back_edge from_label to_label =
    StringSet.mem from_label (StringMap.find to_label dominators)
  in
  
  (* 收集所有返祖边 *)
  let back_edges = List.fold_left (fun acc block ->
    List.fold_left (fun acc' succ ->
      if is_back_edge block.label succ then
        (block.label, succ) :: acc'
      else acc'
    ) acc block.succs
  ) [] blocks in
  
  (* 对于每个返祖边，找出循环体中的所有基本块 *)
  List.filter_map (fun (from_label, header_label) ->
    try
      let rec collect_loop_body worklist body =
        match worklist with
        | [] -> body
        | curr :: rest ->
            if StringSet.mem curr body then
              collect_loop_body rest body
            else
              let new_body = StringSet.add curr body in
              match StringMap.find_opt curr block_map with
              | None -> body  (* 如果找不到基本块，保持当前循环体不变 *)
              | Some block ->
                  let new_worklist = 
                    List.filter (fun pred -> not (StringSet.mem pred new_body))
                      block.preds @ rest
                  in
                  collect_loop_body new_worklist new_body
      in
      let loop_body = collect_loop_body [from_label] (StringSet.singleton header_label) in
      Some (header_label, StringSet.elements loop_body)
    with Not_found -> None  (* 如果在处理过程中出现任何查找错误，跳过这个循环 *)
  ) back_edges

(* 创建循环前置头部 *)
let create_preheader (blocks : ir_block list) (header : string) : ir_block list =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  match StringMap.find_opt header block_map with
  | None -> blocks  (* 如果找不到循环头，返回原始块列表 *)
  | Some header_block ->
      (* 找出所有来自循环外的前驱 *)
      let outside_preds = List.filter (fun pred ->
        match StringMap.find_opt pred block_map with
        | None -> false  (* 如果找不到前驱块，忽略它 *)
        | Some pred_block ->
            not (List.exists (fun succ -> succ = header) pred_block.succs)
      ) header_block.preds in
      
      if outside_preds = [] then blocks else
      let preheader_label = header ^ "_ph" in
      (* 检查是否已经存在前置头部 *)
      if List.exists (fun b -> b.label = preheader_label) blocks then
        blocks
      else
        let preheader = {
          label = preheader_label;
          insts = [];
          terminator = TermGoto header;
          preds = outside_preds;
          succs = [header]
        } in
        
        (* 更新原有块的前驱后继关系 *)
        List.iter (fun pred_label ->
          match StringMap.find_opt pred_label block_map with
          | None -> ()  (* 如果找不到前驱块，跳过它 *)
          | Some pred_block ->
              pred_block.succs <- List.map (fun s -> if s = header then preheader_label else s) pred_block.succs
        ) outside_preds;
        
        header_block.preds <- preheader_label :: 
          List.filter (fun p -> not (List.mem p outside_preds)) header_block.preds;
        
        preheader :: blocks

(* 分析循环不变量 *)
let find_loop_invariants (blocks : ir_block list) (loop_blocks : string list) (_ : string) : ir_inst list =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  
  (* 检查操作数是否循环不变 *)
  let is_operand_invariant op defined_in_loop =
    match op with
    | Imm _ -> true
    | Var name | Reg name ->
        not (StringSet.mem name defined_in_loop)
  in
  
  (* 收集循环内定义的变量 *)
  let defined_in_loop = List.fold_left (fun acc label ->
    let block = StringMap.find label block_map in
    List.fold_left (fun acc' inst ->
      match inst with
      | Binop(_, dst, _, _) | Unop(_, dst, _) | Load(dst, _)
      | Call(dst, _, _) | Assign(dst, _) ->
          (match dst with
           | Var name | Reg name -> StringSet.add name acc'
           | _ -> acc')
      | _ -> acc'
    ) acc block.insts
  ) StringSet.empty loop_blocks in
  
  (* 检查指令是否循环不变 *)
  let is_inst_invariant inst =
    match inst with
    | Binop(_, _, src1, src2) ->
        is_operand_invariant src1 defined_in_loop &&
        is_operand_invariant src2 defined_in_loop
    | Unop(_, _, src) ->
        is_operand_invariant src defined_in_loop
    | Assign(_, src) ->
        is_operand_invariant src defined_in_loop
    | _ -> false
  in
  
  (* 收集所有循环不变量指令 *)
  List.fold_left (fun acc label ->
    let block = StringMap.find label block_map in
    List.fold_left (fun acc' inst ->
      if is_inst_invariant inst then inst :: acc'
      else acc'
    ) acc block.insts
  ) [] loop_blocks

(* LICM主函数 *)
let loop_invariant_code_motion (blocks : ir_block list) : (ir_block list * bool) =
  if blocks = [] then ([], false) else
  let changed = ref false in
  let (dominators, _) = compute_dominators blocks in
  let loops = identify_loops blocks dominators in
  
  (* 为每个循环创建前置头部并进行代码移动 *)
  let blocks_ref = ref blocks in
  List.iter (fun (header, loop_blocks) ->
    blocks_ref := create_preheader !blocks_ref header;
    let invariant_insts = find_loop_invariants !blocks_ref loop_blocks header in
    if invariant_insts <> [] then begin
      changed := true;
      let preheader_label = header ^ "_ph" in
      match List.find_opt (fun b -> b.label = preheader_label) !blocks_ref with
      | Some preheader ->
          preheader.insts <- preheader.insts @ invariant_insts;
          
          (* 从循环中删除被移动的指令 *)
          List.iter (fun label ->
            match List.find_opt (fun b -> b.label = label) !blocks_ref with
            | Some block ->
                block.insts <- List.filter (fun inst -> not (List.mem inst invariant_insts)) block.insts
            | None -> ()
          ) loop_blocks
      | None -> ()
    end
  ) loops;
  
  (!blocks_ref, !changed)

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
      { !func_ref with blocks = build_cfg new_blocks }
    in
    (* 先进行常量传播，为LICM创造更多机会 *)
    func_ref := run_pass constant_propagation;
    
    (* 执行循环不变量代码外提 *)
    func_ref := run_pass loop_invariant_code_motion;
    
    (* 最后进行死代码消除，清理可能产生的无用代码 *)
    func_ref := run_pass dead_code_elimination;
    
    (* 尾递归优化 *)
    let (tro_func, tro_changed) = tail_recursion_optimization !func_ref in
    if tro_changed then (changed_in_iter := true; func_ref := {tro_func with blocks = build_cfg tro_func.blocks});
  done;
  !func_ref