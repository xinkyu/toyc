(* reg_alloc.ml - 寄存器分配优化模块 *)
open Ir

(* 可用的寄存器列表 (s0-s11) *)
let available_registers = [
  "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; 
  "s6"; "s7"; "s8"; "s9"; "s10"; "s11"
]

(* 变量使用信息 *)
type var_info = {
  mutable use_count: int;       (* 使用次数 *)
  mutable last_use: int;        (* 最后一次使用的位置 *)
  mutable reg: string option;   (* 分配的寄存器 *)
  mutable spill: bool;          (* 是否需要溢出到栈 *)
}

module StringMap = Map.Make(String)

(* 分析变量使用情况 *)
let analyze_var_usage (insts : ir_inst list) : var_info StringMap.t =
  let var_map = ref StringMap.empty in
  let inst_index = ref 0 in
  
  (* 初始化变量信息 *)
  let get_or_create_info var =
    match StringMap.find_opt var !var_map with
    | Some info -> info
    | None ->
        let info = { use_count = 0; last_use = 0; reg = None; spill = false } in
        var_map := StringMap.add var info !var_map;
        info
  in
  
  (* 更新变量使用信息 *)
  let update_var_use var =
    let info = get_or_create_info var in
    info.use_count <- info.use_count + 1;
    info.last_use <- !inst_index
  in
  
  (* 分析操作数使用 *)
  let analyze_operand = function
    | Reg name | Var name -> update_var_use name
    | Imm _ -> ()
  in
  
  (* 遍历所有指令 *)
  List.iter (fun inst ->
    incr inst_index;
    match inst with
    | Assign (dst, src) -> 
        (match dst with 
         | Reg name | Var name -> update_var_use name 
         | _ -> ());
        analyze_operand src
    | Binop (_, dst, src1, src2) ->
        (match dst with 
         | Reg name | Var name -> update_var_use name 
         | _ -> ());
        analyze_operand src1;
        analyze_operand src2
    | Unop (_, dst, src) ->
        (match dst with 
         | Reg name | Var name -> update_var_use name 
         | _ -> ());
        analyze_operand src
    | Call (dst, _, args) ->
        (match dst with 
         | Reg name | Var name -> update_var_use name 
         | _ -> ());
        List.iter analyze_operand args
    | Load (dst, src) ->
        (match dst with 
         | Reg name | Var name -> update_var_use name 
         | _ -> ());
        analyze_operand src
    | Store (addr, value) ->
        analyze_operand addr;
        analyze_operand value
    | IfGoto (cond, _) ->
        analyze_operand cond
    | Ret (Some op) ->
        analyze_operand op
    | _ -> ()
  ) insts;
  
  !var_map

(* 分配寄存器 *)
let allocate_registers (var_map : var_info StringMap.t) : unit =
  (* 根据使用频率排序变量 *)
  let vars = 
    StringMap.bindings var_map
    |> List.map (fun (name, info) -> (name, info))
    |> List.sort (fun (_, info1) (_, info2) -> 
        compare info2.use_count info1.use_count)
  in
  
  (* 分配可用寄存器 *)
  let rec allocate reg_list = function
    | [] -> ()
    | (var_name, info) :: rest ->
        match reg_list with
        | [] -> 
            (* 没有可用寄存器，设置为需要溢出 *)
            info.spill <- true;
            allocate [] rest
        | reg :: regs ->
            (* 分配寄存器 *)
            info.reg <- Some reg;
            allocate regs rest
  in
  
  allocate available_registers vars

(* 获取变量的寄存器或栈位置 *)
let get_var_location (var_map : var_info StringMap.t) (var_name : string) : 
    [`Reg of string | `Stack] =
  match StringMap.find_opt var_name var_map with
  | Some info -> 
      (match info.reg with
       | Some reg -> `Reg reg
       | None -> `Stack)
  | None -> `Stack

(* 针对基本块的寄存器分配 *)
let allocate_registers_for_block (blk : ir_block) : var_info StringMap.t =
  let var_map = analyze_var_usage blk.insts in
  allocate_registers var_map;
  var_map

(* 针对函数的寄存器分配 *)
let allocate_registers_for_func (f : ir_func_o) : var_info StringMap.t =
  (* 合并所有基本块的指令 *)
  let all_insts = 
    List.fold_left (fun acc blk -> acc @ blk.insts) [] f.blocks
  in
  let var_map = analyze_var_usage all_insts in
  allocate_registers var_map;
  var_map