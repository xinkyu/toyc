(* file: lib/linearScan.ml *)
open Ir

module VarMap = Map.Make(String)
module VSet = Liveness.VSet
module LabelMap = Liveness.LabelMap

(* An interval is a range [start, end] *)
type interval = { var_name: string; start: int; finish: int; }

(* 
 Build live intervals for all variables in a function.
 This version uses the results of the dataflow-based liveness analysis.
*)
let build_intervals (func: ir_func_o) : interval list =
  let _, live_out = Liveness.analyze func in
  let usage_map = ref VarMap.empty in
  let inst_num = ref 0 in

  let add_usage var pos =
    let current_uses = try VarMap.find var !usage_map with Not_found -> [] in
    usage_map := VarMap.add var (pos :: current_uses) !usage_map
  in

  List.iter (fun block ->
    let live = ref (LabelMap.find block.label live_out) in
    (* Iterate backwards through the instructions in the block *)
    List.iteri (fun i _ ->
      let inst_idx = List.length block.insts - 1 - i in
      let inst = List.nth block.insts inst_idx in
      let pos = !inst_num + inst_idx in
      let def, use = Liveness.def_use inst in

      (* A variable is live at this point if it's in live_out, def, or use *)
      VSet.iter (fun v -> add_usage v pos) !live;
      VSet.iter (fun v -> add_usage v pos) def;
      VSet.iter (fun v -> add_usage v pos) use;

      (* Update live set for the preceding instruction *)
      live := VSet.union use (VSet.diff !live def)
    ) block.insts;
    inst_num := !inst_num + List.length block.insts
  ) func.blocks;

  (* For each variable, create an interval from its min to max usage point *)
  VarMap.fold (fun var uses acc ->
    if uses = [] then acc
    else
      let sorted_uses = List.sort_uniq compare uses in
      let new_interval : interval = { 
        var_name = var;
        start = List.hd sorted_uses; 
        finish = List.hd (List.rev sorted_uses);
      } in
      new_interval :: acc
  ) !usage_map []

type allocation_result =
| PhysicalRegister of string
| StackSlot of int

(* RISC-V calling convention: t0-t6 are caller-saved temporaries.
  We can use them freely within a function. Let's use t0-t5 for allocation.
  t6 will be reserved for temporary values during instruction translation. *)
let available_registers = ["t0"; "t1"; "t2"; "t3"; "t4"; "t5"]

let allocate (intervals: interval list) : (string, allocation_result) Hashtbl.t * int =
  let allocation_map = Hashtbl.create (List.length intervals) in
  let sorted_intervals = List.sort (fun a b -> compare a.start b.start) intervals in
  let active = ref [] in
  let free_registers = ref available_registers in
  let spill_offset = ref 0 in

  List.iter (fun current_interval ->
    (* 1. Expire old intervals and free their registers *)
    let new_active = ref [] in
    List.iter (fun (active_interval:interval) ->
      if active_interval.finish >= current_interval.start then
        new_active := active_interval :: !new_active
      else
        match Hashtbl.find allocation_map active_interval.var_name with
        | PhysicalRegister reg -> free_registers := reg :: !free_registers
        | StackSlot _ -> () (* Should not happen in active list *)
    ) !active;
    active := List.sort (fun a b -> compare a.finish b.finish) !new_active;

    (* 2. Try to allocate a register or spill *)
    if (List.length !free_registers) > 0 then begin
      (* Allocate a free register *)
      let reg = List.hd !free_registers in
      free_registers := List.tl !free_registers;
      Hashtbl.add allocation_map current_interval.var_name (PhysicalRegister reg);
      active := List.sort (fun a b -> compare a.finish b.finish) (current_interval :: !active)
    end else begin
      (* No free registers, must spill. *)
      let spill_candidate = List.hd (List.rev !active) in (* Last element in active ends latest *)
      
      if spill_candidate.finish > current_interval.finish then
        (* Spill the active interval that ends latest *)
        let reg_to_free =
          match Hashtbl.find allocation_map spill_candidate.var_name with
          | PhysicalRegister r -> r
          | StackSlot _ -> failwith "Logic error: Active interval chosen for spilling must have a physical register"
        in
        
        (* Update allocation: spill_candidate goes to stack, current_interval gets the freed register *)
        spill_offset := !spill_offset + 4;
        Hashtbl.replace allocation_map spill_candidate.var_name (StackSlot !spill_offset);
        Hashtbl.add allocation_map current_interval.var_name (PhysicalRegister reg_to_free);
        
        (* Update active list: remove the spilled interval, add the new one, and re-sort *)
        let updated_active = current_interval :: (List.filter (fun i -> i.var_name <> spill_candidate.var_name) !active) in
        active := List.sort (fun a b -> compare a.finish b.finish) updated_active
      else
        (* Spill the current interval as it ends later than any active one *)
        spill_offset := !spill_offset + 4;
        Hashtbl.add allocation_map current_interval.var_name (StackSlot !spill_offset)
    end
  ) sorted_intervals;

  (allocation_map, !spill_offset * 4)

