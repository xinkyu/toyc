open Ir

(*
 * Liveness.ml: 活性分析模块
 *
 * 这个模块实现了编译后端所需的数据流分析——活性分析。
 * 它的核心功能是为给定的控制流图（CFG）计算出在每个程序点（具体来说是每个基本块的入口和出口）
 * 哪些变量是“活跃”的。
 *
 * 一个变量是活跃的，意味着它当前持有的值在未来可能会被用到。
 * 这个信息对于寄存器分配至关重要，因为它告诉我们哪些变量需要被保存在寄存器中。
 *
 * 分析过程：
 * 1. 为每个基本块计算 `uses` (块内使用的变量) 和 `defs` (块内定义的变量) 集合。
 * 2. 使用一个迭代的、后向的数据流分析算法来计算每个块的 `liveIn` 和 `liveOut` 集合。
 * - `liveOut[B] = U liveIn[S]` (对于 B 的所有后继 S)
 * - `liveIn[B] = uses[B] U (liveOut[B] - defs[B])`
 * 3. 持续迭代直到所有集合不再变化。
 *)

(* 使用 OCaml 的 Set 和 Map 模块来处理变量名集合和映射 *)
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
  (* Load, Ret None, Goto, Label 不产生 use/def *)
  | Load (dst, src) -> (vars_of_operand src, vars_of_operand dst)
  | _ -> (StringSet.empty, StringSet.empty)

(* 计算基本块的 use 和 def 集合 *)
let get_use_def_block (block: ir_block) : StringSet.t * StringSet.t =
  List.fold_left (fun (uses, defs) inst ->
    let inst_uses, inst_defs = get_use_def_inst inst in
    (* 顺序很重要: use 是在 def 之前发生的 *)
    (* use_B = (use_B - inst_defs) U inst_uses *)
    let new_uses = StringSet.union inst_uses (StringSet.diff uses inst_defs) in
    let new_defs = StringSet.union defs inst_defs in
    (new_uses, new_defs)
  ) (StringSet.empty, StringSet.empty) block.insts

(* 主分析函数 *)
let analyze (func: ir_func_o) : (StringSet.t StringMap.t * StringSet.t StringMap.t) =
  let blocks = func.blocks in
  let block_map = List.fold_left (fun map b -> StringMap.add b.label b map) StringMap.empty blocks in

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
    ) (List.rev blocks) (* 从后向前遍历可能收敛更快 *)
  done;

  (!live_in, !live_out)
