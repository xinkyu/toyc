open Ir

(*
 * Liveness.ml: 活性分析模块
 *)

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

(* 从 operand 中提取变量名 *)
let vars_of_operand (op: operand) : StringSet.t =
  match op with
  | Reg r | Var r -> StringSet.singleton r
  | Imm _ -> StringSet.empty

(* 计算单条指令的 use 和 def 集合 *)
let get_use_def_inst (inst: ir_inst) : StringSet.t * StringSet.t =
  match inst with
  | Binop (_, dst, src1, src2) ->
      let uses = StringSet.union (vars_of_operand src1) (vars_of_operand src2) in
      let defs = vars_of_operand dst in
      (uses, defs)
  | Unop (_, dst, src) ->
      let uses = vars_of_operand src in
      let defs = vars_of_operand dst in
      (uses, defs)
  | Assign (dst, src) ->
      let uses = vars_of_operand src in
      let defs = vars_of_operand dst in
      (uses, defs)
  | Call (dst, _, args) ->
      let uses = List.fold_left (fun acc op -> StringSet.union acc (vars_of_operand op)) StringSet.empty args in
      let defs = vars_of_operand dst in
      (uses, defs)
  | Ret (Some op) -> (vars_of_operand op, StringSet.empty)
  | Store (addr, src) ->
      (StringSet.union (vars_of_operand addr) (vars_of_operand src), StringSet.empty)
  | IfGoto (cond, _) -> (vars_of_operand cond, StringSet.empty)
  | Load (dst, src) -> (vars_of_operand src, vars_of_operand dst)
  | _ -> (StringSet.empty, StringSet.empty)

(* 计算基本块的 use 和 def 集合 *)
let get_use_def_block (block: ir_block) : StringSet.t * StringSet.t =
  List.fold_left (fun (uses, defs) inst ->
    let inst_uses, inst_defs = get_use_def_inst inst in
    let new_uses = StringSet.union inst_uses (StringSet.diff uses inst_defs) in
    let new_defs = StringSet.union defs inst_defs in
    (new_uses, new_defs)
  ) (StringSet.empty, StringSet.empty) block.insts

(* 主分析函数 *)
let analyze (func: ir_func_o) : (StringSet.t StringMap.t * StringSet.t StringMap.t) =
  let blocks = func.blocks in
  (* FIX: Removed unused 'block_map' variable *)

  (* 1. 计算所有块的 use/def 集 *)
  let use_map = ref StringMap.empty in
  let def_map = ref StringMap.empty in
  List.iter (fun b ->
    let uses, defs = get_use_def_block b in
    use_map := StringMap.add b.label uses !use_map;
    def_map := StringMap.add b.label defs !def_map;
  ) blocks;

  (* 2. 初始化 liveIn 和 liveOut 集合 *)
  let live_in = ref StringMap.empty in
  let live_out = ref StringMap.empty in
  List.iter (fun b ->
    live_in := StringMap.add b.label StringSet.empty !live_in;
    live_out := StringMap.add b.label StringSet.empty !live_out;
  ) blocks;

  (* 3. 迭代计算，直到不动点 *)
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun b ->
      (* 计算 liveOut[b] = U_{s in succ(b)} liveIn[s] *)
      let new_live_out = List.fold_left (fun acc succ_label ->
        let succ_live_in = StringMap.find succ_label !live_in in
        StringSet.union acc succ_live_in
      ) StringSet.empty b.succs in

      (* 计算 liveIn[b] = use[b] U (liveOut[b] - def[b]) *)
      let use_b = StringMap.find b.label !use_map in
      let def_b = StringMap.find b.label !def_map in
      let new_live_in = StringSet.union use_b (StringSet.diff new_live_out def_b) in

      (* 检查集合是否变化 *)
      let old_live_in = StringMap.find b.label !live_in in
      let old_live_out = StringMap.find b.label !live_out in
      if not (StringSet.equal new_live_in old_live_in && StringSet.equal new_live_out old_live_out) then
        changed := true;

      live_in := StringMap.add b.label new_live_in !live_in;
      live_out := StringMap.add b.label new_live_out !live_out;
    ) (List.rev blocks)
  done;

  (!live_in, !live_out)
