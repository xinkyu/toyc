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
  (* 执行活跃变量分析获取live_in和live_out集合 *)
  let live_in, live_out = Liveness.analyze func in
  let usage_map = ref VarMap.empty in
  let inst_num = ref 0 in
  let block_map = List.fold_left (fun map block -> 
    LabelMap.add block.label block map
  ) LabelMap.empty func.blocks in

  (* Helper to record a use or def of a variable at a specific instruction number *)
  let add_usage var pos =
    let current_uses = try VarMap.find var !usage_map with Not_found -> [] in
    usage_map := VarMap.add var (pos :: current_uses) !usage_map
  in

  (* 添加变量在终结符中的使用 *)
  let process_terminator block pos =
    let term_def, term_use = match block.terminator with
      | TermIf (cond, _, _) -> 
          let names = match get_name cond with
            | Some n -> VSet.singleton n
            | None -> VSet.empty
          in
          (VSet.empty, names)
      | TermRet (Some op) ->
          let names = match get_name op with
            | Some n -> VSet.singleton n
            | None -> VSet.empty
          in
          (VSet.empty, names)
      | _ -> (VSet.empty, VSet.empty)
    in
    VSet.iter (fun v -> add_usage v pos) term_use
  in

  (* 处理所有基本块 *)
  let process_blocks () =
    List.iter (fun block ->
      let block_live_out = LabelMap.find block.label live_out in
      
      (* 处理块中的每条指令及其活跃变量 *)
      List.iteri (fun i inst ->
        let pos = !inst_num + i in
        let def, use = Liveness.def_use inst in
        
        (* 记录每个变量在此指令的使用 *)
        VSet.iter (fun v -> add_usage v pos) use;
        
        (* 记录每个定义的变量 *)
        VSet.iter (fun v -> add_usage v pos) def;
      ) block.insts;
      
      (* 处理块的终结符 *)
      process_terminator block (!inst_num + List.length block.insts);
      
      (* 更新全局指令计数 *)
      inst_num := !inst_num + List.length block.insts + 1; (* +1 for terminator *)
      
      (* 处理后继块的入口处活跃的变量 *)
      List.iter (fun succ_label ->
        if LabelMap.mem succ_label block_map then
          let succ_live_in = LabelMap.find succ_label live_in in
          VSet.iter (fun v -> add_usage v !inst_num) succ_live_in
      ) block.succs;
    ) func.blocks
  in
  
  process_blocks ();

  (* 为每个变量创建活跃区间 *)
  VarMap.fold (fun var uses acc ->
    if uses = [] then acc
    else
      let sorted_uses = List.sort compare uses in
      let new_interval = { 
        var_name = var;
        start = List.hd sorted_uses; 
        finish = List.hd (List.rev sorted_uses);
      } in
      new_interval :: acc
  ) !usage_map []

and get_name = function
  | Var s | Reg s -> Some s
  | Imm _ -> None

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

  (* 为函数参数预先分配寄存器 *)
  let pre_allocate_args args =
    List.iteri (fun i arg ->
      if i < 8 && i < List.length available_registers then
        (* 把前8个参数分配到寄存器，优先使用 a0-a7，但考虑到调用约定，我们使用t0-t5 *)
        let reg = List.nth available_registers i in
        Hashtbl.add allocation_map arg (PhysicalRegister reg);
        free_registers := List.filter (fun r -> r <> reg) !free_registers
      else
        (* 其余参数溢出到栈上 *)
        begin
          spill_offset := !spill_offset + 4;
          Hashtbl.add allocation_map arg (StackSlot !spill_offset)
        end
    ) args
  in

  (* 遍历每个活跃区间进行分配 *)
  List.iter (fun current_interval ->
    (* 1. 过期旧区间并回收寄存器 *)
    active := List.filter (fun (interval:interval) ->
      if interval.finish >= current_interval.start then
        (* 区间仍然活跃 *)
        true
      else
        begin
          (* 区间已过期，释放其寄存器 *)
          match Hashtbl.find_opt allocation_map interval.var_name with
          | Some (PhysicalRegister reg) ->
              free_registers := reg :: !free_registers;
              false
          | _ -> false
        end
    ) !active;
    
    (* 将active列表按照结束时间排序，使得先结束的区间排在前面 *)
    active := List.sort (fun a b -> compare a.finish b.finish) !active;

    (* 2. 尝试分配寄存器 *)
    if List.length !free_registers > 0 then begin
      (* 分配一个空闲寄存器 *)
      let reg = List.hd !free_registers in
      free_registers := List.tl !free_registers;
      
      Hashtbl.add allocation_map current_interval.var_name (PhysicalRegister reg);
      active := current_interval :: !active;
    end else begin
      (* 没有空闲寄存器，必须溢出 *)
      (* 我们采用一个简单的策略：总是溢出当前区间 *)
      (* 更复杂的策略可能会溢出一个结束时间更晚的活跃区间 *)
      spill_offset := !spill_offset + 4;
      Hashtbl.add allocation_map current_interval.var_name (StackSlot !spill_offset);
    end;
    
    (* 确保active列表始终按照结束时间排序 *)
    active := List.sort (fun a b -> compare a.finish b.finish) !active;
  ) sorted_intervals;

  (allocation_map, !spill_offset)