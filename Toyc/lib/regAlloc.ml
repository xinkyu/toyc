open Ir
open Liveness

(*
 * RegAlloc.ml: 寄存器分配模块
 *
 * 这个模块实现了线性扫描寄存器分配算法。
 *
 * 阶段 1 & 2: 构建活跃区间 (已完成)
 * 阶段 3: 实现线性扫描分配算法 (本次更新)
 *
 * 算法流程:
 * 1. 初始化一个物理寄存器池。
 * 2. 将所有变量的活跃区间按起始点排序。
 * 3. 遍历排序后的区间列表：
 * a. 首先，检查当前 active 列表中的区间，释放掉已经结束的区间及其寄存器。
 * b. 如果有可用的物理寄存器，就分配给当前区间。
 * c. 如果没有可用的寄存器，则执行溢出(Spill)逻辑：
 * - 在当前区间和 active 列表中的所有区间里，选择一个结束点最远的进行溢出。
 * - 如果溢出的是一个已分配的区间，则将其寄存器回收并分配给当前区间。
 * 4. 返回一个映射表，记录每个变量被分配到的位置（物理寄存器或栈上的溢出槽）。
 *)

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)

(* 区间范围 *)
type range = {
  start_point : int;
  end_point   : int;
}

(* 活跃区间数据结构 *)
type live_interval = {
  var_name : string;
  mutable ranges : range list; (* 一个变量可能有多个不连续的活跃范围 *)
  mutable assigned_reg : string option; (* 分配到的物理寄存器 *)
  mutable spill_cost : float; (* 溢出代价，未来可用于优化 *)
}

(* 分配结果：变量可以被分配到物理寄存器或栈上的溢出槽 *)
type allocation_location =
  | InReg of string (* 物理寄存器名, e.g., "t0" *)
  | Spilled of int  (* 栈上的溢出槽位索引, e.g., 0, 1, 2... *)

(* 辅助函数：打印 range *)
let string_of_range r = Printf.sprintf "[%d, %d]" r.start_point r.end_point

(* 辅助函数：打印 interval *)
let string_of_interval i =
  let ranges_str = String.concat ", " (List.map string_of_range i.ranges) in
  Printf.sprintf "%s -> %s" i.var_name ranges_str

(* 步骤 1: 指令编号 (与之前相同) *)
let number_instructions (func: ir_func_o) : (ir_inst IntMap.t * (string, int * int) Hashtbl.t) =
  let inst_map = ref IntMap.empty in
  let block_ranges = Hashtbl.create (List.length func.blocks) in
  let current_id = ref 0 in
  List.iter (fun b ->
    let block_start_id = !current_id in
    List.iter (fun inst ->
      inst_map := IntMap.add !current_id inst !inst_map;
      current_id := !current_id + 2;
    ) b.insts;
    current_id := !current_id + 2;
    let block_end_id = !current_id in
    Hashtbl.add block_ranges b.label (block_start_id, block_end_id);
  ) func.blocks;
  (!inst_map, block_ranges)

(* 步骤 2 & 3: 构建并合并区间 (与之前相同) *)
let build_intervals (func: ir_func_o) (live_in: StringSet.t StringMap.t) (live_out: StringSet.t StringMap.t) : live_interval list =
  let _, block_ranges = number_instructions func in
  let intervals = Hashtbl.create 100 in
  let get_or_create_interval var =
    match Hashtbl.find_opt intervals var with
    | Some i -> i
    | None ->
        let new_i = { var_name = var; ranges = []; assigned_reg = None; spill_cost = 0.0 } in
        Hashtbl.add intervals var new_i;
        new_i
  in
  let add_range var start_p end_p =
    let interval = get_or_create_interval var in
    interval.ranges <- { start_point = start_p; end_point = end_p } :: interval.ranges
  in
  List.iter (fun b ->
    let block_start, block_end = Hashtbl.find block_ranges b.label in
    let live = ref (StringMap.find b.label live_out) in
    let insts_with_ids =
      let rec assign_ids id = function
        | [] -> []
        | inst :: rest -> (id, inst) :: assign_ids (id - 2) rest
      in
      assign_ids (block_end - 2) (List.rev b.insts)
    in
    List.iter (fun (id, inst) ->
      let _, defs = get_use_def_inst inst in
      let uses, _ = get_use_def_inst inst in
      StringSet.iter (fun v ->
        live := StringSet.remove v !live;
        add_range v id id;
      ) defs;
      StringSet.iter (fun v ->
        live := StringSet.add v !live;
        add_range v id id;
      ) uses;
    ) (List.rev insts_with_ids);
    StringSet.iter (fun v ->
      add_range v block_start block_end
    ) !live;
  ) func.blocks;
  let final_intervals = Hashtbl.fold (fun _ interval acc ->
    let sorted_ranges = List.sort (fun r1 r2 -> compare r1.start_point r2.start_point) interval.ranges in
    let merged =
      match sorted_ranges with
      | [] -> []
      | hd :: tl ->
          List.fold_left (fun (current :: acc) next ->
            if next.start_point <= current.end_point + 1 then
              { current with end_point = max current.end_point next.end_point } :: acc
            else
              next :: current :: acc
          ) [hd] tl
    in
    interval.ranges <- List.rev merged;
    if interval.ranges <> [] then interval :: acc else acc
  ) intervals [];
  final_intervals

(* *** 新增部分：线性扫描分配算法 *** *)

(* 可用物理寄存器池 (RISC-V 临时寄存器) *)
let physical_registers =
  Array.init 7 (fun i -> "t" ^ string_of_int i)

(* 获取区间的起始点和结束点 *)
let get_start_point interval = (List.hd interval.ranges).start_point
let get_end_point interval = (List.hd (List.rev interval.ranges)).end_point

(* 主分配函数 *)
let linear_scan_allocate (intervals: live_interval list) : (string, allocation_location) Hashtbl.t =
  let allocation_map = Hashtbl.create (List.length intervals) in
  let free_regs = ref (Array.to_list physical_registers) in
  let active = ref [] in (* 按结束点排序的 active interval 列表 *)
  let spill_count = ref 0 in

  (* 1. 按起始点对所有区间进行排序 *)
  let sorted_intervals = List.sort (fun a b -> compare (get_start_point a) (get_start_point b)) intervals in

  List.iter (fun current_interval ->
    let current_start = get_start_point current_interval in

    (* 2. Expire old intervals: 检查 active 列表，释放已经结束的区间的寄存器 *)
    let still_active, expired = List.partition (fun active_interval ->
      get_end_point active_interval >= current_start
    ) !active in
    List.iter (fun expired_interval ->
      match expired_interval.assigned_reg with
      | Some reg -> free_regs := reg :: !free_regs
      | None -> () (* Spilled interval has no register to free *)
    ) expired;
    active := still_active;

    (* 3. 分配或溢出 *)
    if List.length !active < Array.length physical_registers then (
      (* 3a. 分配: 有可用寄存器 *)
      let reg = List.hd !free_regs in
      free_regs := List.tl !free_regs;
      current_interval.assigned_reg <- Some reg;
      Hashtbl.add allocation_map current_interval.var_name (InReg reg);
      active := List.sort (fun a b -> compare (get_end_point a) (get_end_point b)) (current_interval :: !active);
    ) else (
      (* 3b. 溢出: 没有可用寄存器 *)
      let last_active = List.hd (List.rev !active) in (* 结束点最远的区间 *)
      if get_end_point last_active > get_end_point current_interval then (
        (* 溢出 active 列表中的 last_active *)
        let reg_to_reassign = Option.get last_active.assigned_reg in
        last_active.assigned_reg <- None;
        Hashtbl.replace allocation_map last_active.var_name (Spilled !spill_count);
        spill_count := !spill_count + 1;

        (* 将回收的寄存器分配给 current_interval *)
        current_interval.assigned_reg <- Some reg_to_reassign;
        Hashtbl.add allocation_map current_interval.var_name (InReg reg_to_reassign);
        active := List.filter (fun i -> i.var_name <> last_active.var_name) !active;
        active := List.sort (fun a b -> compare (get_end_point a) (get_end_point b)) (current_interval :: !active);
      ) else (
        (* 溢出当前区间 current_interval *)
        Hashtbl.add allocation_map current_interval.var_name (Spilled !spill_count);
        spill_count := !spill_count + 1;
      )
    )
  ) sorted_intervals;

  allocation_map
