open Ir

(* Register definitions *)
type reg = string  (* Register name like "a0", "t0" *)

(* Available registers *)
let callee_saved = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"]
let caller_saved = ["t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"]
let arg_regs = ["a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7"]

(* Live interval representation *)
type live_interval = {
  var : string;        (* Variable name *)
  start : int;         (* Start position *)
  ending : int;        (* End position *)
  mutable reg : reg option;  (* Assigned register *)
  mutable spill : bool;      (* Is spilled to memory *)
  mutable spill_loc : int option; (* Stack location if spilled *)
  uses : int;          (* Number of uses (for spill heuristic) *)
}

(* Find all variables/temporaries used in instruction *)
let vars_in_inst (inst : ir_inst) : string list =
  match inst with
  | Binop(_, dst, src1, src2) -> 
      let extract_var = function
        | Reg v | Var v -> [v]
        | Imm _ -> []
      in
      extract_var dst @ extract_var src1 @ extract_var src2
  | Unop(_, dst, src) -> 
      let extract_var = function
        | Reg v | Var v -> [v]
        | Imm _ -> []
      in
      extract_var dst @ extract_var src
  | Assign(dst, src) -> 
      let extract_var = function
        | Reg v | Var v -> [v]
        | Imm _ -> []
      in
      extract_var dst @ extract_var src
  | Call(dst, _, args) ->
      let extract_var = function
        | Reg v | Var v -> [v]
        | Imm _ -> []
      in
      extract_var dst @ List.concat (List.map extract_var args)
  | Load(dst, src) | Store(dst, src) ->
      let extract_var = function
        | Reg v | Var v -> [v]
        | Imm _ -> []
      in
      extract_var dst @ extract_var src
  | IfGoto(cond, _) ->
      let extract_var = function
        | Reg v | Var v -> [v]
        | Imm _ -> []
      in
      extract_var cond
  | Ret(Some op) ->
      let extract_var = function
        | Reg v | Var v -> [v]
        | Imm _ -> []
      in
      extract_var op
  | Goto _ | Label _ | Ret None -> []

(* Build live intervals for a function *)
let build_intervals (func : ir_func) : live_interval list =
  let all_vars = Hashtbl.create 50 in
  let def_pos = Hashtbl.create 50 in
  let use_counts = Hashtbl.create 50 in
  
  (* Pass 1: Find all variable definitions and uses *)
  let process_inst pos inst =
    let vars = vars_in_inst inst in
    List.iter (fun v -> 
      if not (Hashtbl.mem all_vars v) then
        Hashtbl.add all_vars v ();
      
      (* Count uses *)
      let count = try Hashtbl.find use_counts v with Not_found -> 0 in
      Hashtbl.replace use_counts v (count + 1);
      
      (* Record definition position for assignment targets *)
      match inst with
      | Binop(_, Reg v, _, _) | Binop(_, Var v, _, _)
      | Unop(_, Reg v, _) | Unop(_, Var v, _)
      | Assign(Reg v, _) | Assign(Var v, _)
      | Call(Reg v, _, _) | Call(Var v, _, _)
      | Load(Reg v, _) | Load(Var v, _) ->
          Hashtbl.replace def_pos v pos
      | _ -> ()
    ) vars
  in
  
  (* Process all instructions to find definitions *)
  List.iteri process_inst func.body;
  
  (* Pass 2: Determine live ranges *)
  let intervals = Hashtbl.create 50 in
  
  (* Initialize intervals with definition positions *)
  Hashtbl.iter (fun var _ ->
    let def = try Hashtbl.find def_pos var with Not_found -> 0 in
    let uses = try Hashtbl.find use_counts var with Not_found -> 0 in
    Hashtbl.add intervals var {
      var = var;
      start = def;
      ending = def; (* Will be updated in next pass *)
      reg = None;
      spill = false;
      spill_loc = None;
      uses = uses;
    }
  ) all_vars;
  
  (* Update ending positions based on uses *)
  List.iteri (fun pos inst ->
    match inst with
    | Binop(_, _, src1, src2) ->
        (match src1 with
         | Reg v | Var v -> 
             let interval = Hashtbl.find intervals v in
             interval.ending <- max interval.ending pos
         | _ -> ());
        (match src2 with
         | Reg v | Var v -> 
             let interval = Hashtbl.find intervals v in
             interval.ending <- max interval.ending pos
         | _ -> ())
    | Unop(_, _, src) ->
        (match src with
         | Reg v | Var v -> 
             let interval = Hashtbl.find intervals v in
             interval.ending <- max interval.ending pos
         | _ -> ())
    | Assign(_, src) ->
        (match src with
         | Reg v | Var v -> 
             let interval = Hashtbl.find intervals v in
             interval.ending <- max interval.ending pos
         | _ -> ())
    | Call(_, _, args) ->
        List.iter (function
          | Reg v | Var v -> 
              let interval = Hashtbl.find intervals v in
              interval.ending <- max interval.ending pos
          | _ -> ()
        ) args
    | Load(_, src) | Store(_, src) ->
        (match src with
         | Reg v | Var v -> 
             let interval = Hashtbl.find intervals v in
             interval.ending <- max interval.ending pos
         | _ -> ())
    | IfGoto(cond, _) ->
        (match cond with
         | Reg v | Var v -> 
             let interval = Hashtbl.find intervals v in
             interval.ending <- max interval.ending pos
         | _ -> ())
    | Ret(Some op) ->
        (match op with
         | Reg v | Var v -> 
             let interval = Hashtbl.find intervals v in
             interval.ending <- max interval.ending pos
         | _ -> ())
    | Goto _ | Label _ | Ret None -> ()
  ) func.body;
  
  (* Convert to list and sort by start position *)
  let result = Hashtbl.fold (fun _ interval acc -> interval :: acc) intervals [] in
  List.sort (fun a b -> compare a.start b.start) result

(* Linear scan register allocation *)
let linear_scan (intervals : live_interval list) : unit =
  let active = ref [] in
  let available_regs = ref (callee_saved @ caller_saved) in
  
  let expire_old_intervals current =
    active := List.filter (fun interval ->
      if interval.ending < current.start then begin
        (* Return this register to available pool *)
        match interval.reg with
        | Some r -> available_regs := r :: !available_regs; false
        | None -> false
      end else true
    ) !active
  in
  
  let spill_interval interval =
    (* Find the interval with the furthest endpoint *)
    let spill_candidate = 
      List.fold_left (fun (max_end, max_int) int ->
        if int.ending > max_end then (int.ending, Some int)
        else (max_end, max_int)
      ) (interval.ending, None) !active
    in
    
    match snd spill_candidate with
    | None -> interval.spill <- true  (* Spill the current interval *)
    | Some to_spill -> 
        if to_spill.ending > interval.ending then begin
          (* Spill the longer-living interval *)
          to_spill.spill <- true;
          to_spill.reg <- None;
          (* Use its register for current interval *)
          match to_spill.reg with
          | Some r -> 
              interval.reg <- Some r;
              active := interval :: (List.filter (fun i -> i != to_spill) !active)
          | None -> failwith "Spilled interval has no register"
        end else begin
          (* Spill the current interval *)
          interval.spill <- true
        end
  in
  
  (* Allocate registers using linear scan *)
  List.iter (fun interval ->
    expire_old_intervals interval;
    
    if !available_regs <> [] then begin
      (* Allocate a register *)
      let reg = List.hd !available_regs in
      available_regs := List.tl !available_regs;
      interval.reg <- Some reg;
      active := interval :: !active
    end else begin
      (* Need to spill *)
      spill_interval interval
    end
  ) intervals

(* Main register allocation function *)
let allocate_registers (func : ir_func) : (string * string option * int option) list =
  let intervals = build_intervals func in
  linear_scan intervals;
  
  (* Assign stack locations for spilled variables *)
  let next_spill_slot = ref 0 in
  List.iter (fun interval ->
    if interval.spill then begin
      interval.spill_loc <- Some !next_spill_slot;
      next_spill_slot := !next_spill_slot + 1
    end
  ) intervals;
  
  (* Return allocation results *)
  List.map (fun interval -> 
    (interval.var, interval.reg, interval.spill_loc)
  ) intervals