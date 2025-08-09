open Ir
open Liveness

module StringMap = Map.Make(String)
module IntMap = Map.Make(Int)

type range = {
  start_point : int;
  end_point   : int;
}

type live_interval = {
  var_name : string;
  mutable ranges : range list;
  mutable assigned_reg : string option;
  mutable spill_cost : float;
}

type allocation_location =
  | InReg of string
  | Spilled of int

let string_of_range r = Printf.sprintf "[%d, %d]" r.start_point r.end_point

let string_of_interval i =
  let ranges_str = String.concat ", " (List.map string_of_range i.ranges) in
  Printf.sprintf "%s -> %s" i.var_name ranges_str

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

(* FIX: Prefixed unused 'live_in' with an underscore to silence the warning. *)
let build_intervals (func: ir_func_o) (_live_in: StringSet.t StringMap.t) (live_out: StringSet.t StringMap.t) : live_interval list =
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
          (* FIX: Made the pattern matching exhaustive to handle the empty list case, satisfying the compiler warning. *)
          List.fold_left (fun acc next ->
            match acc with
            | current :: rest ->
                if next.start_point <= current.end_point + 1 then
                  { current with end_point = max current.end_point next.end_point } :: rest
                else
                  next :: acc
            | [] -> [next] (* This case is logically unreachable but required by the compiler *)
          ) [hd] tl
    in
    interval.ranges <- List.rev merged;
    if interval.ranges <> [] then interval :: acc else acc
  ) intervals []
  in
  final_intervals

let physical_registers =
  Array.init 7 (fun i -> "t" ^ string_of_int i)

let get_start_point interval = (List.hd interval.ranges).start_point
let get_end_point interval = (List.hd (List.rev interval.ranges)).end_point

let linear_scan_allocate (intervals: live_interval list) : (string, allocation_location) Hashtbl.t =
  let allocation_map = Hashtbl.create (List.length intervals) in
  let free_regs = ref (Array.to_list physical_registers) in
  let active = ref [] in
  let spill_count = ref 0 in
  let sorted_intervals = List.sort (fun a b -> compare (get_start_point a) (get_start_point b)) intervals in
  List.iter (fun current_interval ->
    let current_start = get_start_point current_interval in
    let still_active, expired = List.partition (fun active_interval ->
      get_end_point active_interval >= current_start
    ) !active in
    List.iter (fun expired_interval ->
      match expired_interval.assigned_reg with
      | Some reg -> free_regs := reg :: !free_regs
      | None -> ()
    ) expired;
    active := still_active;
    if List.length !active < Array.length physical_registers then (
      let reg = List.hd !free_regs in
      free_regs := List.tl !free_regs;
      current_interval.assigned_reg <- Some reg;
      Hashtbl.add allocation_map current_interval.var_name (InReg reg);
      active := List.sort (fun a b -> compare (get_end_point a) (get_end_point b)) (current_interval :: !active);
    ) else (
      let last_active = List.hd (List.rev !active) in
      if get_end_point last_active > get_end_point current_interval then (
        let reg_to_reassign = Option.get last_active.assigned_reg in
        last_active.assigned_reg <- None;
        Hashtbl.replace allocation_map last_active.var_name (Spilled !spill_count);
        spill_count := !spill_count + 1;
        current_interval.assigned_reg <- Some reg_to_reassign;
        Hashtbl.add allocation_map current_interval.var_name (InReg reg_to_reassign);
        active := List.filter (fun i -> i.var_name <> last_active.var_name) !active;
        active := List.sort (fun a b -> compare (get_end_point a) (get_end_point b)) (current_interval :: !active);
      ) else (
        Hashtbl.add allocation_map current_interval.var_name (Spilled !spill_count);
        spill_count := !spill_count + 1;
      )
    )
  ) sorted_intervals;
  allocation_map
