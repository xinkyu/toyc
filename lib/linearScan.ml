(* file: lib/linearScan.ml *)
open Ir

module VarMap = Map.Make(String)
module VSet = Liveness.VSet
module LabelMap = Liveness.LabelMap

(* An interval is a range [start, end] *)
type interval = { var_name: string; start: int; finish: int; }

(* Helper function to extract variable name from operand *)
let get_name = function
  | Var s | Reg s -> Some s
  | Imm _ -> None

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
    let _, term_use = match block.terminator with
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
      let _ = LabelMap.find_opt block.label live_out in
      
      (* 处理块中的每条指令及其活跃变量 *)
      List.iteri (fun i inst ->
        let pos = !inst_num + i in
        let def, use = Liveness.def_use inst in
        
        (* 记录每个变量在此指令的使用和定义 *)
        VSet.iter (fun v -> add_usage v pos) use;
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

type allocation_result =
| PhysicalRegister of string
| StackSlot of int

(* RISC-V calling convention: t0-t6 are caller-saved temporaries.
  We can use them freely within a function. 
  t5, t6 are reserved for temporary values during instruction translation. *)
let available_registers = ["t0"; "t1"; "t2"; "t3"; "t4"]

let allocate (intervals: interval list) : (string, allocation_result) Hashtbl.t * int =
  (* The final mapping from variable name to its location *)
  let allocation_map = Hashtbl.create (List.length intervals) in

  (* Sort intervals by increasing start point *)
  let sorted_intervals = List.sort (fun a b -> compare a.start b.start) intervals in

  let active = ref [] in
  let free_registers = ref available_registers in
  let spill_offset = ref 0 in

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
      (* 没有空闲寄存器，采用改进的溢出策略 *)
      let spillable_active = List.filter (fun interval ->
        interval.finish > current_interval.finish
      ) !active in
      
      if spillable_active <> [] then begin
        (* 找到生命周期最长的变量并溢出它 *)
        let to_spill = List.hd (List.sort (fun a b -> 
          compare b.finish a.finish
        ) spillable_active) in
        
        (* 从活跃列表中移除该变量 *)
        active := List.filter (fun i -> i.var_name <> to_spill.var_name) !active;
        
        (* 回收它的寄存器 *)
        match Hashtbl.find_opt allocation_map to_spill.var_name with
        | Some (PhysicalRegister reg) ->
            free_registers := reg :: !free_registers;
            
            (* 将该变量溢出到栈 *)
            spill_offset := !spill_offset + 4;
            Hashtbl.replace allocation_map to_spill.var_name (StackSlot !spill_offset);
            
            (* 为当前变量分配回收的寄存器 *)
            let reg = List.hd !free_registers in
            free_registers := List.tl !free_registers;
            Hashtbl.add allocation_map current_interval.var_name (PhysicalRegister reg);
            active := current_interval :: !active;
        | _ -> 
            (* 如果找不到物理寄存器，则溢出当前变量 *)
            spill_offset := !spill_offset + 4;
            Hashtbl.add allocation_map current_interval.var_name (StackSlot !spill_offset);
      end else begin
        (* 没有可溢出的变量，溢出当前变量 *)
        spill_offset := !spill_offset + 4;
        Hashtbl.add allocation_map current_interval.var_name (StackSlot !spill_offset);
      end
    end;
    
    (* 确保active列表始终按照结束时间排序 *)
    active := List.sort (fun a b -> compare a.finish b.finish) !active;
  ) sorted_intervals;

  (allocation_map, !spill_offset)