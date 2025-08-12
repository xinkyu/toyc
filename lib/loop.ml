(* loop.ml *)
open Ir
open Cfg
module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(*******************************************************************)
(* 1. Dominator Analysis (支配树分析) *)
(*******************************************************************)

type dominator_info = {
  doms: StringSet.t StringMap.t; (* doms.(n) 是支配 n 的节点集合 *)
  idom: string StringMap.t;      (* idom.(n) 是 n 的直接支配节点 *)
}

(* 计算支配树 *)
let analyze_dominators (blocks: ir_block list) (entry_label: string) : dominator_info =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  let all_nodes = List.fold_left (fun s b -> StringSet.add b.label s) StringSet.empty blocks in
  
  let doms = ref (List.fold_left (fun m b ->
    if b.label = entry_label then StringMap.add b.label (StringSet.singleton entry_label) m
    else StringMap.add b.label all_nodes m
  ) StringMap.empty blocks) in

  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun b ->
      if b.label <> entry_label then
        let preds = b.preds in
        let pred_doms = List.map (fun p -> StringMap.find p !doms) preds in
        let new_dom =
          match pred_doms with
          | [] -> StringSet.empty
          | hd :: tl -> List.fold_left StringSet.inter hd tl
        in
        let new_dom = StringSet.add b.label new_dom in
        if not (StringSet.equal new_dom (StringMap.find b.label !doms)) then (
          doms := StringMap.add b.label new_dom !doms;
          changed := true
        )
    ) blocks
  done;

  let final_doms = !doms in
  let idom = StringMap.mapi (fun n dom_set ->
    let proper_dominators = StringSet.remove n dom_set in
    try
      StringSet.find_first (fun d1 ->
        StringSet.for_all (fun d2 ->
          if d1 = d2 then true else not (StringSet.mem d1 (StringMap.find d2 final_doms))
        ) proper_dominators
      ) proper_dominators
    with Not_found -> "" (* entry has no idom *)
  ) final_doms in
  { doms = final_doms; idom }

let dominates (dom_info: dominator_info) (dominator: string) (node: string) : bool =
  try StringSet.mem dominator (StringMap.find node dom_info.doms)
  with Not_found -> false

(*******************************************************************)
(* 2. Loop Detection (循环识别) *)
(*******************************************************************)

type loop_info = {
  header: string;
  blocks: StringSet.t;
}

(* 利用支配关系和回边来寻找循环 *)
let find_loops (blocks: ir_block list) (dom_info: dominator_info) : loop_info list =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  let loops = ref [] in
  List.iter (fun b ->
    List.iter (fun succ_label ->
      if dominates dom_info succ_label b.label then (* Found a back edge b -> succ *)
        let header = succ_label in
        let loop_blocks = ref (StringSet.of_list [header; b.label]) in
        let stack = ref [b.label] in
        while !stack <> [] do
          let curr = List.hd !stack in
          stack := List.tl !stack;
          let current_block = StringMap.find curr block_map in
          List.iter (fun pred_label ->
            if not (StringSet.mem pred_label !loop_blocks) then (
              loop_blocks := StringSet.add pred_label !loop_blocks;
              stack := pred_label :: !stack
            )
          ) current_block.preds
        done;
        loops := { header; blocks = !loop_blocks } :: !loops
    ) b.succs
  ) blocks;
  !loops

(*******************************************************************)
(* 3. Reaching Definitions Analysis (到达定值分析) *)
(*******************************************************************)
type reaching_def = (string * string) (* var_name * block_label_of_def *)
module DefSet = Set.Make(struct type t = reaching_def let compare = compare end)

type reaching_def_info = {
  in_defs: DefSet.t StringMap.t;
  out_defs: DefSet.t StringMap.t;
}

let get_def_var_name inst =
  match inst with
  | Binop (_, d, _, _) | Unop (_, d, _) | Assign (d, _) | Load (d, _) | Call (d, _, _) ->
      (match d with Var s | Reg s -> Some s | Imm _ -> None)
  | _ -> None

let analyze_reaching_definitions (blocks: ir_block list) : reaching_def_info =
  let block_map = List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty blocks in
  
  let all_defs = List.fold_left (fun acc b ->
    List.fold_left (fun acc_inst inst ->
      match get_def_var_name inst with
      | Some v -> DefSet.add (v, b.label) acc_inst
      | None -> acc_inst
    ) acc b.insts
  ) DefSet.empty blocks in
  
  let defs_by_var = DefSet.fold (fun (v, l) m ->
    let current_defs = try StringMap.find v m with Not_found -> DefSet.empty in
    StringMap.add v (DefSet.add (v, l) current_defs) m
  ) all_defs StringMap.empty in

  let gen = StringMap.map (fun b ->
    List.fold_left (fun s i -> match get_def_var_name i with Some v -> DefSet.add (v, b.label) s | None -> s) DefSet.empty b.insts
  ) block_map in

  let kill = StringMap.mapi (fun label _ ->
    let my_defs = StringMap.find label gen in
    DefSet.fold (fun (v, _) acc ->
      let all_defs_for_v = StringMap.find v defs_by_var in
      DefSet.union (DefSet.remove (v, label) all_defs_for_v) acc
    ) my_defs DefSet.empty
  ) block_map in

  let in_defs = ref (StringMap.map (fun _ -> DefSet.empty) block_map) in
  let out_defs = ref (StringMap.map (fun _ -> DefSet.empty) block_map) in

  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b.label worklist) blocks;

  while not (Queue.is_empty worklist) do
    let label = Queue.take worklist in
    let blk = StringMap.find label block_map in
    let preds = blk.preds in
    
    let new_in =
      if preds = [] then DefSet.empty
      else List.fold_left (fun acc p_label ->
        let pred_out = try StringMap.find p_label !out_defs with Not_found -> DefSet.empty in
        DefSet.union acc pred_out
      ) DefSet.empty preds
    in
    in_defs := StringMap.add label new_in !in_defs;

    let old_out = try StringMap.find label !out_defs with Not_found -> DefSet.empty in
    let gen_set = StringMap.find label gen in
    let kill_set = StringMap.find label kill in
    let new_out = DefSet.union gen_set (DefSet.diff new_in kill_set) in
    
    if not (DefSet.equal old_out new_out) then (
      out_defs := StringMap.add label new_out !out_defs;
      List.iter (fun succ -> Queue.add succ worklist) blk.succs
    )
  done;
  { in_defs = !in_defs; out_defs = !out_defs }

(*******************************************************************)
(* 4. Loop Invariant Code Motion (LICM) Transformation *)
(*******************************************************************)

let label_id = ref 0
let new_label prefix =
  incr label_id;
  Printf.sprintf ".%s_%d" prefix !label_id

let is_movable_inst = function
  | Binop _ | Unop _ | Assign _ | Load _ -> true
  (* Calls and Stores have side effects, can't be moved safely without more analysis *)
  | Call _ | Store _ | Ret _ | Goto _ | IfGoto _ | Label _ -> false

let get_used_vars inst =
  let op_to_var op = match op with Var v | Reg v -> Some v | Imm _ -> None in
  let add_opt_to_set set opt = match opt with Some v -> StringSet.add v set | None -> set in
  match inst with
  | Binop (_, _, s1, s2) -> add_opt_to_set (add_opt_to_set StringSet.empty (op_to_var s1)) (op_to_var s2)
  | Unop (_, _, s) | Assign (_, s) | Load (_, s) -> add_opt_to_set StringSet.empty (op_to_var s)
  | Store (d, s) -> add_opt_to_set (add_opt_to_set StringSet.empty (op_to_var d)) (op_to_var s)
  | Call (_, _, args) -> List.fold_left (fun s op -> add_opt_to_set s (op_to_var op)) StringSet.empty args
  | _ -> StringSet.empty

(* The main transformation function *)
let loop_invariant_code_motion (func : ir_func_o) : (ir_func_o * bool) =
  if func.blocks = [] then (func, false) else
  
  let entry_label = (List.hd func.blocks).label in
  let dom_info = analyze_dominators func.blocks entry_label in
  let loops = find_loops func.blocks dom_info in
  if loops = [] then (func, false) else
  
  let reaching_defs_info = analyze_reaching_definitions func.blocks in
  let changed = ref false in
  let block_map_ref = ref (List.fold_left (fun m b -> StringMap.add b.label b m) StringMap.empty func.blocks) in

  List.iter (fun loop ->
    (* Step 1: Create a preheader for the loop *)
    let header = StringMap.find loop.header !block_map_ref in
    let preheader_label =
      if List.length header.preds = 1 then
        let pred_label = List.hd header.preds in
        let pred_block = StringMap.find pred_label !block_map_ref in
        if List.length pred_block.succs = 1 then pred_label (* Predecessor is a valid preheader *)
        else ""
      else ""
    in
    let (preheader_label, preheader_block) =
      if preheader_label <> "" then (preheader_label, StringMap.find preheader_label !block_map_ref)
      else (
        changed := true;
        let new_ph_label = new_label "preheader" in
        let new_ph_block = { label=new_ph_label; insts=[]; terminator=TermGoto loop.header; preds=[]; succs=[loop.header] } in
        
        (* Rewire CFG *)
        let original_preds = header.preds in
        List.iter (fun p_label ->
          let pred_block = StringMap.find p_label !block_map_ref in
          pred_block.succs <- new_ph_label :: (List.filter ((<>) loop.header) pred_block.succs);
          begin match pred_block.terminator with
            | TermGoto l when l = loop.header -> pred_block.terminator <- TermGoto new_ph_label
            | TermIf (c, t, e) when t = loop.header -> pred_block.terminator <- TermIf (c, new_ph_label, e)
            | TermIf (c, t, e) when e = loop.header -> pred_block.terminator <- TermIf (c, t, new_ph_label)
            | TermSeq l when l = loop.header -> pred_block.terminator <- TermSeq new_ph_label
            | _ -> () (* This might happen for complex CFGs, may need more robust handling *)
          end;
          new_ph_block.preds <- p_label :: new_ph_block.preds
        ) original_preds;
        header.preds <- [new_ph_label];
        block_map_ref := StringMap.add new_ph_label new_ph_block !block_map_ref;
        (new_ph_label, new_ph_block)
      )
    in

    (* Step 2: Find and hoist invariant code *)
    let hoisted_in_iter = ref true in
    while !hoisted_in_iter do
      hoisted_in_iter := false;
      StringSet.iter (fun b_label ->
        let b = StringMap.find b_label !block_map_ref in
        let block_in_defs = StringMap.find b_label reaching_defs_info.in_defs in
        let (new_insts, hoisted_insts) = List.partition (fun inst ->
          if not (is_movable_inst inst) then true (* Not invariant *)
          else
            let used = get_used_vars inst in
            let def_var = get_def_var_name inst in
            (* An instruction is invariant if all used variables are defined outside the loop *)
            let is_invariant = StringSet.for_all (fun var ->
              let defs_of_var = DefSet.filter (fun (v,_) -> v = var) block_in_defs in
              not (DefSet.is_empty defs_of_var) && DefSet.for_all (fun (_, def_label) -> not (StringSet.mem def_label loop.blocks)) defs_of_var
            ) used
            in
            (* Also, ensure we don't move a re-definition out of the loop *)
            let is_redefined_in_loop =
              match def_var with
              | None -> false
              | Some v ->
                  let other_defs_in_loop = StringSet.fold (fun l_label acc ->
                    if l_label = b_label then acc
                    else
                      let other_b = StringMap.find l_label !block_map_ref in
                      acc || List.exists (fun i -> get_def_var_name i = Some v) other_b.insts
                  ) loop.blocks false
                  in other_defs_in_loop
            in
            not is_invariant || is_redefined_in_loop
        ) b.insts in

        if hoisted_insts <> [] then (
          changed := true;
          hoisted_in_iter := true;
          b.insts <- new_insts;
          preheader_block.insts <- preheader_block.insts @ hoisted_insts
        )
      ) loop.blocks
    done
  ) loops;

  let new_blocks = StringMap.fold (fun _ b acc -> b :: acc) !block_map_ref [] in
  ({ func with blocks = new_blocks }, !changed)