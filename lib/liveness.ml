(* file: lib/liveness.ml *)
open Ir

module VSet = Set.Make(String)
module LabelMap = Map.Make(String)

(* Get the name from an operand if it's a Var or Reg *)
let get_name = function
  | Var s | Reg s -> Some s
  | Imm _ -> None

(* Get a set of names from a list of operands *)
let names_from_operands ops =
  List.fold_left (fun acc op ->
    match get_name op with
    | Some name -> VSet.add name acc
    | None -> acc
  ) VSet.empty ops

(*
  Calculate the DEF and USE sets for a single instruction.
  Returns a pair: (def_set, use_set)
*)
let def_use (inst : ir_inst) : VSet.t * VSet.t =
  match inst with
  | Binop (_, dst, lhs, rhs) ->
      let def = names_from_operands [dst] in
      let use = names_from_operands [lhs; rhs] in
      (def, use)
  | Unop (_, dst, src) ->
      let def = names_from_operands [dst] in
      let use = names_from_operands [src] in
      (def, use)
  | Assign (dst, src) ->
      let def = names_from_operands [dst] in
      let use = names_from_operands [src] in
      (def, use)
  | Call (dst, _, args) ->
      let def = names_from_operands [dst] in
      let use = names_from_operands args in
      (def, use)
  | Load (dst, src) -> (* t1 = *t2 *)
      let def = names_from_operands [dst] in
      let use = names_from_operands [src] in
      (def, use)
  | Store (addr, src) -> (* *t1 = t2 *)
      let def = VSet.empty in
      let use = names_from_operands [addr; src] in
      (def, use)
  | IfGoto (cond, _) ->
      (VSet.empty, names_from_operands [cond])
  | Ret (Some op) ->
      (VSet.empty, names_from_operands [op])
  | Ret None -> (VSet.empty, VSet.empty)
  | Goto _ | Label _ -> (VSet.empty, VSet.empty)

(* 也为终结符计算def/use *)
let term_def_use term =
  match term with
  | TermIf (cond, _, _) ->
      (VSet.empty, names_from_operands [cond])
  | TermRet (Some op) ->
      (VSet.empty, names_from_operands [op])
  | TermRet None | TermGoto _ | TermSeq _ ->
      (VSet.empty, VSet.empty)

(*
  The main liveness analysis function.
  It performs a backward dataflow analysis on the CFG.
  Returns a pair of maps: (live_in_sets, live_out_sets)
*)
let analyze (func: ir_func_o) : (VSet.t LabelMap.t * VSet.t LabelMap.t) =
  let blocks = func.blocks in
  
  let live_in = ref LabelMap.empty in
  let live_out = ref LabelMap.empty in

  (* Initialize live_in and live_out for all blocks *)
  List.iter (fun b ->
    live_in := LabelMap.add b.label VSet.empty !live_in;
    live_out := LabelMap.add b.label VSet.empty !live_out;
  ) blocks;

  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun b ->
      (* live_out[b] = union of live_in[s] for all successors s of b *)
      let succ_live_ins = List.fold_left (fun acc succ_label ->
          try VSet.union acc (LabelMap.find succ_label !live_in)
          with Not_found -> acc (* 处理可能不存在的后继块 *)
        ) VSet.empty b.succs
      in
      
      let old_out = LabelMap.find b.label !live_out in
      if not (VSet.equal succ_live_ins old_out) then begin
        live_out := LabelMap.add b.label succ_live_ins !live_out;
        changed := true;
      end;

      (* 计算块的全部指令的def/use，包括终结符 *)
      let block_def, block_use = 
        let def_from_insts, use_from_insts = List.fold_left (fun (d_acc, u_acc) inst ->
            let d, u = def_use inst in
            (VSet.union d d_acc, VSet.union u (VSet.diff u_acc d))
          ) (VSet.empty, VSet.empty) b.insts
        in
        let term_def, term_use = term_def_use b.terminator in
        (VSet.union def_from_insts term_def, VSet.union use_from_insts term_use)
      in
      
      (* live_in[b] = use[b] U (live_out[b] - def[b]) *)
      let new_in = VSet.union block_use (VSet.diff (LabelMap.find b.label !live_out) block_def) in
      let old_in = LabelMap.find b.label !live_in in
      if not (VSet.equal new_in old_in) then begin
        live_in := LabelMap.add b.label new_in !live_in;
        changed := true;
      end
    ) (List.rev blocks) (* 反向迭代以加速收敛 *)
  done;

  (!live_in, !live_out)