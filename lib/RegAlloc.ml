(* file: lib/RegAlloc.ml *)

open Ir (* open Ir 会自动引入 allocation 类型 *)
module StringMap = Map.Make(String)

(*******************************************************************)
(** 数据结构定义                          **)
(*******************************************************************)

(* allocation 类型已移至 ir.ml *)

type live_interval = {
  vreg  : string;
  mutable start : int;
  mutable end_  : int;
}

(*******************************************************************)
(** 活跃区间构造                          **)
(*******************************************************************)

let vreg_of_operand = function
  | Reg s | Var s -> Some s
  | Imm _ -> None

let add_vreg_to_set set op =
  match vreg_of_operand op with
  | Some name -> StringSet.add name set
  | None -> set

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
    List.iteri (fun i inst ->
      let n = block_end_n - i in
      let defs, uses = inst_def_use inst in
      StringSet.iter (fun v -> touch_interval v n) !live_now;
      live_now := StringSet.union uses (StringSet.diff !live_now defs);
    ) (List.rev block.insts);
    StringSet.iter (fun v -> touch_interval v block_start_n) !live_now;
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
(** 线性扫描分配                          **)
(*******************************************************************)

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
      | OnStack _ -> ()
    ) expired
  in

  let spill_at_interval interval =
    let last_active = List.hd (List.rev (List.sort (fun a b -> compare a.end_ b.end_) !active)) in
    if last_active.end_ > interval.end_ then
      (
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
      )
    else
      (
        stack_offset := !stack_offset - 4;
        allocation_map := StringMap.add interval.vreg (OnStack !stack_offset) !allocation_map
      )
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
(** 主入口函数                            **)
(*******************************************************************)

let run (blocks: ir_block list) : (allocation StringMap.t * int) =
  let intervals_map = build_live_intervals blocks in
  let intervals_list = StringMap.bindings intervals_map |> List.map snd in
  allocate_registers intervals_list