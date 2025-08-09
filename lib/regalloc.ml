(* file: lib/RegAlloc.ml *)

open Ir
module StringMap = Map.Make(String)

(*******************************************************************)
(** 数据结构定义                          **)
(*******************************************************************)

(* 寄存器的最终分配位置 *)
type allocation =
  | InReg of string  (* 分配到物理寄存器 *)
  | OnStack of int (* 分配到栈上，值为偏移量 *)

(* 活跃区间的数据结构 *)
type live_interval = {
  vreg  : string; (* 虚拟寄存器名 *)
  mutable start : int;
  mutable end_  : int;
}

(*******************************************************************)
(** 活跃区间构造 (阶段二)                          **)
(*******************************************************************)

(* 辅助函数，从 operand 中提取虚拟寄存器名 *)
let vreg_of_operand = function
  | Reg s | Var s -> Some s
  | Imm _ -> None

let add_vreg_to_set set op =
  match vreg_of_operand op with
  | Some name -> StringSet.add name set
  | None -> set

(* 计算单条指令的 def 和 use 集合 (与 cfg.ml 中版本相同) *)
let inst_def_use (inst: ir_inst) : (StringSet.t * StringSet.t) =
  match inst with
  | Binop (_, dst, lhs, rhs) ->
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set (add_vreg_to_set StringSet.empty lhs) rhs in
      (def, use)
  | Unop (_, dst, src) ->
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set StringSet.empty src in
      (def, use)
  | Assign (dst, src) ->
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set StringSet.empty src in
      (def, use)
  | Call (dst, _, args) ->
      let def = add_vreg_to_set StringSet.empty dst in
      let use = List.fold_left add_vreg_to_set StringSet.empty args in
      (def, use)
  | Store (addr, value) ->
      let use = add_vreg_to_set (add_vreg_to_set StringSet.empty addr) value in
      (StringSet.empty, use)
  | IfGoto (cond, _) ->
      (StringSet.empty, add_vreg_to_set StringSet.empty cond)
  | Ret (Some op) ->
      (StringSet.empty, add_vreg_to_set StringSet.empty op)
  | Load (dst, src) ->
      let def = add_vreg_to_set StringSet.empty dst in
      let use = add_vreg_to_set StringSet.empty src in
      (def, use)
  | _ -> (StringSet.empty, StringSet.empty)

(* 构造活跃区间 *)
let build_live_intervals (blocks: ir_block list) : live_interval StringMap.t =
  let intervals = ref StringMap.empty in
  let instruction_count = ref (-1) in

  let touch_interval vreg point =
    let current_interval =
      match StringMap.find_opt vreg !intervals with
      | Some i -> i
      | None -> { vreg; start = point; end_ = point }
    in
    current_interval.start <- min current_interval.start point;
    current_interval.end_ <- max current_interval.end_ point;
    intervals := StringMap.add vreg current_interval !intervals
  in

  List.iter (fun block ->
    let block_start_n = !instruction_count + 1 in
    let block_end_n = block_start_n + (List.length block.insts) - 1 in
    
    let live_now = ref block.live_out in
    (* 从后向前遍历指令，更新 live 集合 *)
    List.iteri (fun i inst ->
      let n = block_end_n - i in
      let defs, uses = inst_def_use inst in

      (* 扩展当前活跃变量的区间 *)
      StringSet.iter (fun v -> touch_interval v n) !live_now;
      
      (* 更新 live 集合: live_before = use U (live_after - def) *)
      live_now := StringSet.union uses (StringSet.diff !live_now defs);
    ) (List.rev block.insts);

    (* 处理 live_in *)
    StringSet.iter (fun v -> touch_interval v block_start_n) !live_now;

    (* 最后再过一遍指令，确保所有 def/use 点都被覆盖 *)
    instruction_count := block_start_n -1;
     List.iter (fun inst ->
      instruction_count := !instruction_count + 1;
      let n = !instruction_count in
      let defs, uses = inst_def_use inst in
      StringSet.iter (fun v -> touch_interval v n) uses;
      StringSet.iter (fun v -> touch_interval v n) defs;
    ) block.insts;

  ) blocks;

  !intervals

(*******************************************************************)
(** 线性扫描分配 (阶段三)                         **)
(*******************************************************************)

(* 可用物理寄存器列表 (RISC-V) *)
(* 我们使用 t0-t6 作为临时寄存器，s0-s11 作为需要保存的寄存器 *)
let physical_registers = [
  "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6";
  "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11";
]

let allocate_registers (intervals: live_interval list) =
  let sorted_intervals = List.sort (fun a b -> compare a.start b.start) intervals in
  let active = ref [] in
  let free_regs = ref physical_registers in
  let allocation_map = ref StringMap.empty in
  let stack_offset = ref 0 in

  let expire_old_intervals interval =
    let still_active, expired =
      List.partition (fun active_i -> active_i.end_ >= interval.start) !active
    in
    active := still_active;
    List.iter (fun expired_i ->
      match StringMap.find expired_i.vreg !allocation_map with
      | InReg reg_name -> free_regs := reg_name :: !free_regs
      | OnStack _ -> () (* Already on stack, no register to free *)
    ) expired
  in

  let spill_at_interval interval =
    let last_active = List.hd (List.rev (List.sort (fun a b -> compare a.end_ b.end_) !active)) in
    if last_active.end_ > interval.end_ then
      (* 溢出 active 列表中结束最晚的区间 *)
      let reg_to_spill =
        match StringMap.find last_active.vreg !allocation_map with
        | InReg r -> r
        | _ -> failwith "Inactive interval found without register"
      in
      active := List.filter (fun i -> i.vreg <> last_active.vreg) !active;
      
      stack_offset := !stack_offset - 4;
      allocation_map := StringMap.add last_active.vreg (OnStack !stack_offset) !allocation_map;
      
      allocation_map := StringMap.add interval.vreg (InReg reg_to_spill) !allocation_map;
      active := List.sort (fun a b -> compare a.end_ b.end_) (interval :: !active)
    else
      (* 溢出当前区间本身 *)
      stack_offset := !stack_offset - 4;
      allocation_map := StringMap.add interval.vreg (OnStack !stack_offset) !allocation_map
  in

  List.iter (fun interval ->
    expire_old_intervals interval;
    if List.length !active < List.length physical_registers then
      (
        let reg = List.hd !free_regs in
        free_regs := List.tl !free_regs;
        allocation_map := StringMap.add interval.vreg (InReg reg) !allocation_map;
        active := List.sort (fun a b -> compare a.end_ b.end_) (interval :: !active)
      )
    else
      spill_at_interval interval
  ) sorted_intervals;

  (!allocation_map, !stack_offset)

(*******************************************************************)
(** 主入口函数**)
(*******************************************************************)


let run (blocks: ir_block list) : (allocation StringMap.t * int) =
  let intervals_map = build_live_intervals blocks in
  let intervals_list = StringMap.bindings intervals_map |> List.map snd in
  allocate_registers intervals_list
