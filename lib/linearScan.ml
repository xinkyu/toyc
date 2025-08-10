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

  (* Helper to record a use or def of a variable at a specific instruction number *)
  let add_usage var pos =
    let current_uses = try VarMap.find var !usage_map with Not_found -> [] in
    usage_map := VarMap.add var (pos :: current_uses) !usage_map
  in

  (* 1. For each instruction, find all variables that are live *)
  List.iter (fun block ->
    let live = ref (LabelMap.find block.label live_out) in
    List.iteri (fun i _ ->
      let inst = List.nth block.insts (List.length block.insts - 1 - i) in
      let current_pos = !inst_num + (List.length block.insts - 1 - i) in
      
      let def, use = Liveness.def_use inst in
      
      (* Any variable in live_out or use is live at this point *)
      VSet.iter (fun v -> add_usage v current_pos) !live;
      VSet.iter (fun v -> add_usage v current_pos) use;

      (* Update the live set for the next instruction (previous in block) *)
      live := VSet.union use (VSet.diff !live def);
    ) block.insts;
    inst_num := !inst_num + (List.length block.insts)
  ) func.blocks;

  (* 2. For each variable, create an interval from its min to max usage point *)
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
  (* The final mapping from variable name to its location *)
  let allocation_map = Hashtbl.create (List.length intervals) in
  
  (* Sort intervals by increasing start point *)
  let sorted_intervals = List.sort (fun a b -> compare a.start b.start) intervals in

  let active = ref [] in
  let free_registers = ref available_registers in
  let spill_offset = ref 0 in

  List.iter (fun current_interval ->
    (* 1. Expire old intervals and remove any spilled intervals from active list *)
    let new_active = ref [] in
    List.iter (fun (active_interval:interval) ->
      match Hashtbl.find allocation_map active_interval.var_name with
      | PhysicalRegister reg ->
          if active_interval.finish >= current_interval.start then
            (* This interval is still active, keep it *)
            new_active := active_interval :: !new_active
          else
            (* This interval has expired, free its register *)
            free_registers := reg :: !free_registers
      | StackSlot _ ->
          (* This was spilled previously. It should not be in the active list.
             We remove it by not adding it to new_active. *)
          ()
    ) !active;
    active := List.sort (fun a b -> compare a.finish b.finish) !new_active;

    (* 2. Try to allocate a register *)
    if (List.length !free_registers) > 0 then begin
      (* Allocate a free register *)
      let reg = List.hd !free_registers in
      free_registers := List.tl !free_registers;
      
      Hashtbl.add allocation_map current_interval.var_name (PhysicalRegister reg);
      active := List.sort (fun a b -> compare a.finish b.finish) (current_interval :: !active);
    end else begin
      (* No free registers, must spill *)
      (* No free registers, must spill. To avoid the complex (and currently buggy)
         logic of spilling an *active* interval and moving its value to the stack,
         we will always spill the *current* interval. This is less optimal but guarantees correctness. *)
      spill_offset := !spill_offset + 4;
      Hashtbl.add allocation_map current_interval.var_name (StackSlot !spill_offset)
    end

  ) sorted_intervals;

  (allocation_map, !spill_offset)