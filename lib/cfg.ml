(* cfg.ml *)
open Ir
module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(* 增强的状态类型，用于同时支持常量传播和拷贝传播 *)
type const_state =
  | IsConst of int      (* 是一个值为int的常量 *)
  | IsCopy of operand   (* 是另一个操作数的拷贝 *)
  | NotAConst           (* 非常量或未知状态 *)

(* 映射变量名 -> 状态 *)
type const_env = const_state StringMap.t

(*取模*)
let word_mod n =
  let m = Int32.of_int n in
  Int32.to_int (Int32.logand m 0xFFFFFFFFl)

(* 合并多个环境的状态，现在能处理新的 const_state *)
let merge_envs (envs : const_env list) : const_env =
  if envs = [] then StringMap.empty
  else
    let all_vars = List.fold_left (fun acc env ->
        StringMap.fold (fun k _ acc -> StringSet.add k acc) env acc
      ) StringSet.empty envs in
    StringSet.fold (fun var acc ->
        let states = List.map (fun env ->
            try StringMap.find var env with Not_found -> NotAConst (* 默认是未知 *)
          ) envs in
        let first_state = List.hd states in
        let all_same = List.for_all (fun s -> s = first_state) (List.tl states) in
        if all_same then
          StringMap.add var first_state acc
        else
          StringMap.add var NotAConst acc (* 不同路径值不同，变为未知 *)
      ) all_vars StringMap.empty

(* 递归地解析操作数，处理拷贝链，增加循环检测 *)
let rec eval_operand_rec env op visited =
  if List.mem op visited then op (* 发现循环(e.g. a=b,b=a)，停止解析 *)
  else
    match op with
    | Var name | Reg name ->
        (try
          match StringMap.find name env with
          | IsConst i -> Imm i
          | IsCopy next_op -> eval_operand_rec env next_op (op :: visited)
          | NotAConst -> op
        with Not_found -> op)
    | Imm _ -> op

let eval_operand env op = eval_operand_rec env op []

let eval_binop op op1 op2 =
  match (op1, op2) with
  | (Imm a, Imm b) ->
  (match op with
   | "+" -> Some (word_mod (a + b)) | "-" -> Some (word_mod (a - b))
   | "*" -> Some (word_mod (a * b)) | "/" when b <> 0 -> Some (word_mod (a / b))
   | "%" when b <> 0 -> Some (word_mod (a mod b)) | "==" -> Some (if a = b then 1 else 0)
   | "!=" -> Some (if a <> b then 1 else 0) | "<" -> Some (if a < b then 1 else 0)
   | "<=" -> Some (if a <= b then 1 else 0) | ">" -> Some (if a > b then 1 else 0)
   | ">=" -> Some (if a >= b then 1 else 0) | _ -> None)
  | _ -> None

let eval_unop op op1 =
  match op1 with
  | Imm a ->
  (match op with
   | "!" -> Some (if a = 0 then 1 else 0) | "-" -> Some (word_mod (-a))
   | "+" -> Some (word_mod a) | _ -> None)
  | _ -> None

let process_inst env inst =
  match inst with
  | Assign (dst, src) ->
      let src' = eval_operand env src in
      let env' =
        match dst with
        | Var name | Reg name ->
            (match src' with
             | Imm i -> StringMap.add name (IsConst i) env
             | Var _ | Reg _ -> StringMap.add name (IsCopy src') env
            )
        | _ -> env
      in
      Assign (dst, src'), env'
  | Binop (op, dst, src1, src2) ->
      let src1' = eval_operand env src1 in
      let src2' = eval_operand env src2 in
      let dst_name = match dst with Var v | Reg v -> v | _ -> "" in
      (match eval_binop op src1' src2' with
       | Some i -> Assign (dst, Imm i), StringMap.add dst_name (IsConst i) env
       | None ->
           (match (op, src1', src2') with
            | ("+", v, Imm 0) | ("+", Imm 0, v) | ("-", v, Imm 0) | ("*", v, Imm 1) | ("*", Imm 1, v) | ("/", v, Imm 1) ->
                Assign (dst, v), StringMap.add dst_name (IsCopy v) env
            | ("-", v1, v2) when v1 = v2 -> Assign (dst, Imm 0), StringMap.add dst_name (IsConst 0) env
            | ("*", _, Imm 0) | ("*", Imm 0, _) -> Assign (dst, Imm 0), StringMap.add dst_name (IsConst 0) env
            | ("*", v, Imm 2) | ("*", Imm 2, v) -> Binop ("+", dst, v, v), StringMap.add dst_name NotAConst env
            | ("*", v, Imm (-1)) -> Unop ("-", dst, v), StringMap.add dst_name NotAConst env
            | ("*", Imm (-1), v) -> Unop ("-", dst, v), StringMap.add dst_name NotAConst env
            | _ -> Binop (op, dst, src1', src2'), StringMap.add dst_name NotAConst env))
  | Unop (op, dst, src) ->
      let src' = eval_operand env src in
      let dst_name = match dst with Var v | Reg v -> v | _ -> "" in
      (match eval_unop op src' with
       | Some i -> Assign (dst, Imm i), StringMap.add dst_name (IsConst i) env
       | None ->
          (match op with
            | "+" -> Assign(dst, src'), StringMap.add dst_name (IsCopy src') env
            | _ -> Unop (op, dst, src'), StringMap.add dst_name NotAConst env))
  | Call (dst, fname, args) ->
      let args' = List.map (eval_operand env) args in
      let env' = match dst with Var v | Reg v -> StringMap.add v NotAConst env | _ -> env in
      Call (dst, fname, args'), env'
  | Load (dst, addr) ->
      let addr' = eval_operand env addr in
      let env' = match dst with Var v | Reg v -> StringMap.add v NotAConst env | _ -> env in
      Load (dst, addr'), env'
  | Store (addr, value) ->
      let addr' = eval_operand env addr in
      let value' = eval_operand env value in
      Store (addr', value'), env
  | IfGoto (cond, label) -> IfGoto (eval_operand env cond, label), env
  | Ret op_opt -> Ret (Option.map (eval_operand env) op_opt), env
  | Goto _ | Label _ as t -> t, env

let process_terminator env term =
  match term with
  | TermIf (cond, l1, l2) ->
      (match eval_operand env cond with
       | Imm 0 -> TermGoto l2 | Imm _ -> TermGoto l1
       | v -> TermIf (v, l1, l2))
  | TermRet o -> TermRet (Option.map (eval_operand env) o)
  | TermGoto _ | TermSeq _ as t -> t

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
    let old_insts = blk.insts in let old_term = blk.terminator in
    let preds = blk.preds in
    let in_env = if preds = [] then StringMap.empty else merge_envs (List.map (fun p -> StringMap.find p !out_envs) preds) in
    in_envs := StringMap.add label in_env !in_envs;
    let new_insts, out_env = List.fold_left (fun (acc, env) inst ->
        let inst', env' = process_inst env inst in acc @ [inst'], env'
      ) ([], in_env) blk.insts in
    let new_term = process_terminator out_env blk.terminator in
    if old_insts <> new_insts || old_term <> new_term then changed := true;
    let old_out = StringMap.find label !out_envs in
    if not (StringMap.equal (=) out_env old_out) then begin
      out_envs := StringMap.add label out_env !out_envs;
      List.iter (fun succ -> if StringMap.mem succ block_map then Queue.add succ worklist) blk.succs end;
    blk.insts <- new_insts;
    blk.terminator <- new_term;
  done;
  (blocks, !changed)

let tail_recursion_optimization (func : ir_func_o) : ir_func_o =
  let open Ir in if func.blocks = [] then func else
  let entry_label = (List.hd func.blocks).label in
  let current_func_name = func.name in let params = func.args in
  let modified = ref false in
  List.iter (fun block ->
    match block.terminator with
    | TermRet (Some ret_val) -> (
        match List.rev block.insts with
        | Assign(dst_assign, src_assign) :: Call(dst_call, fname, args) :: rest_rev
          when dst_assign = ret_val && src_assign = dst_call && fname = current_func_name && List.length params = List.length args ->
            let insts_without_call_and_assign = List.rev rest_rev in
            let assignments = List.map2 (fun p a -> Assign (Var p, a)) params args in
            block.insts <- insts_without_call_and_assign @ assignments;
            block.terminator <- TermGoto entry_label; modified := true
        | Call (dst, fname, args) :: rest_rev
          when fname = current_func_name && dst = ret_val && List.length params = List.length args ->
            let insts_without_call = List.rev rest_rev in
            let assignments = List.map2 (fun p a -> Assign (Var p, a)) params args in
            block.insts <- insts_without_call @ assignments;
            block.terminator <- TermGoto entry_label; modified := true
        | _ -> ())
    | _ -> ()
  ) func.blocks;
  if !modified then { func with blocks = build_cfg func.blocks } else func

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

(* --- 新增DCE部分 --- *)
module VarSet = StringSet

let op_to_set (op: operand) : VarSet.t =
    match op with
    | Var s | Reg s -> VarSet.singleton s
    | Imm _ -> VarSet.empty

let use (inst: ir_inst) : VarSet.t =
    match inst with
    | Binop (_, _, src1, src2) -> VarSet.union (op_to_set src1) (op_to_set src2)
    | Unop (_, _, src) -> op_to_set src
    | Assign (_, src) -> op_to_set src
    | Load (_, addr) -> op_to_set addr
    | Store (addr, value) -> VarSet.union (op_to_set addr) (op_to_set value)
    | Call (_, _, args) -> List.fold_left VarSet.union VarSet.empty (List.map op_to_set args)
    | IfGoto (cond, _) -> op_to_set cond
    | Ret (Some op) -> op_to_set op
    | Ret None | Goto _ | Label _ -> VarSet.empty

let def (inst: ir_inst) : VarSet.t =
    match inst with
    | Binop (_, dst, _, _) | Unop (_, dst, _) | Assign (dst, _) | Load (dst, _) | Call (dst, _, _) -> op_to_set dst
    | _ -> VarSet.empty

let is_critical (inst: ir_inst) : bool =
    match inst with
    | Store _ | Call _ | Ret _ | IfGoto _ | Goto _ -> true
    | _ -> false

let dead_code_elimination (blocks: ir_block list) : (ir_block list * bool) =
    if blocks = [] then (blocks, false) else
    (* let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in -- 这行是多余的 *)
    let live_in = ref StringMap.empty in
    let live_out = ref StringMap.empty in
    List.iter (fun b ->
        live_in := StringMap.add b.label VarSet.empty !live_in;
        live_out := StringMap.add b.label VarSet.empty !live_out
    ) blocks;
    let changed = ref true in
    while !changed do
        changed := false;
        List.iter (fun b ->
            let succ_live_in = List.map (fun succ_label -> StringMap.find succ_label !live_in) b.succs in
            let new_live_out = List.fold_left VarSet.union VarSet.empty succ_live_in in
            let old_live_out = StringMap.find b.label !live_out in
            if not (VarSet.equal new_live_out old_live_out) then
            begin
                live_out := StringMap.add b.label new_live_out !live_out;
                changed := true
            end;
            let term_use = match b.terminator with
                | TermIf(cond, _, _) -> op_to_set cond
                | TermRet(Some op) -> op_to_set op
                | _ -> VarSet.empty
            in
            let live = VarSet.union term_use new_live_out in
            let block_live = List.fold_right (fun inst acc ->
                let def_set = def inst in
                let use_set = use inst in
                VarSet.union use_set (VarSet.diff acc def_set)
            ) b.insts live in
            let old_live_in = StringMap.find b.label !live_in in
            if not (VarSet.equal block_live old_live_in) then
            begin
                live_in := StringMap.add b.label block_live !live_in;
                changed := true
            end
        ) (List.rev blocks)
    done;

    let dce_changed = ref false in
    List.iter (fun b ->
        let term_use = match b.terminator with
            | TermIf(cond, _, _) -> op_to_set cond | TermRet(Some op) -> op_to_set op | _ -> VarSet.empty in
        let live = ref (VarSet.union term_use (StringMap.find b.label !live_out)) in
        let new_insts = List.fold_right (fun inst acc ->
            let def_set = def inst in
            if not (is_critical inst) && VarSet.is_empty (VarSet.inter def_set !live) then
            begin
                dce_changed := true; acc
            end
            else
            begin
                let use_set = use inst in
                live := VarSet.union use_set (VarSet.diff !live def_set);
                inst :: acc
            end
        ) b.insts [] in
        b.insts <- new_insts
    ) blocks;
    (blocks, !dce_changed)

(* --- 优化流程主函数更新 --- *)
let optimize (func : ir_func_o) : ir_func_o =
  let func_ref = ref { func with blocks = build_cfg func.blocks } in
  
  (* 1. 尾递归优化 (只需运行一次) *)
  func_ref := tail_recursion_optimization !func_ref;
  
  (* 2. 交替运行优化，直到没有变化 *)
  let changed_in_iter = ref true in
  while !changed_in_iter do
    changed_in_iter := false;
    
    (* 2a. 常量/拷贝传播 *)
    let (cp_blocks, cp_changed) = constant_propagation !func_ref.blocks in
    if cp_changed then
    begin
      changed_in_iter := true;
      func_ref := {!func_ref with blocks = build_cfg cp_blocks};
    end;

    (* 2b. 死代码消除 *)
    let (dce_blocks, dce_changed) = dead_code_elimination !func_ref.blocks in
    if dce_changed then
    begin
        changed_in_iter := true;
        func_ref := {!func_ref with blocks = dce_blocks};
    end;

    (* 2c. 块合并 *)
    let (merged_blocks, merged_changed) = merge_blocks_pass !func_ref.blocks in
    if merged_changed then
    begin
      changed_in_iter := true;
      func_ref := {!func_ref with blocks = build_cfg merged_blocks}
    end
  done;
  !func_ref