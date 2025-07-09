open Ir

(* 定义变量的活跃区间 *)
type live_interval = {
  var_name: string;
  start: int;  (* 开始位置 *)
  ending: int;  (* 结束位置 *)
  mutable assigned_reg: string option;  (* 分配的寄存器 *)
}

(* 表示寄存器使用情况 *)
type register_status = {
  mutable free: bool;
  mutable current_var: string option;
  mutable expires_at: int;
}

(* 创建可用的寄存器池 - RISC-V 临时寄存器 *)
let create_register_pool () =
  let registers = [
    "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6";  (* 临时寄存器 *)
    "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11";  (* 保存寄存器 *)
  ] in
  List.map (fun reg -> (reg, { free = true; current_var = None; expires_at = 0 })) registers

(* 计算变量的活跃区间 *)
let calculate_live_intervals (insts : ir_inst list) : live_interval list =
  let var_first_use = Hashtbl.create 100 in
  let var_last_use = Hashtbl.create 100 in
  
  (* 辅助函数：更新变量的使用位置 *)
  let update_use var_name pos =
    if not (Hashtbl.mem var_first_use var_name) then
      Hashtbl.add var_first_use var_name pos;
    Hashtbl.replace var_last_use var_name pos
  in
  
  (* 处理单个操作数 *)
  let process_operand op pos =
    match op with
    | Var name | Reg name -> update_use name pos
    | _ -> ()
  in
  
  (* 处理指令中的变量使用 *)
  List.iteri (fun pos inst ->
    match inst with
    | Binop (_, dst, op1, op2) ->
      (match dst with 
       | Var name | Reg name -> update_use name pos
       | _ -> ());
      process_operand op1 pos;
      process_operand op2 pos
      
    | Unop (_, dst, src) ->
      (match dst with 
       | Var name | Reg name -> update_use name pos
       | _ -> ());
      process_operand src pos
      
    | Assign (dst, src) ->
      (match dst with 
       | Var name | Reg name -> update_use name pos
       | _ -> ());
      process_operand src pos
      
    | Load (dst, src) ->
      (match dst with 
       | Var name | Reg name -> update_use name pos
       | _ -> ());
      process_operand src pos
      
    | Store (dst, src) ->
      process_operand dst pos;
      process_operand src pos
      
    | Call (dst, _, args) ->
      (match dst with 
       | Var name | Reg name -> update_use name pos
       | _ -> ());
      List.iter (fun arg -> process_operand arg pos) args
      
    | IfGoto (cond, _) -> 
      process_operand cond pos
      
    | Ret (Some op) -> 
      process_operand op pos
      
    | _ -> ()
  ) insts;
  
  (* 构建活跃区间列表 *)
  let intervals = ref [] in
  Hashtbl.iter (fun var_name first ->
    let last = Hashtbl.find var_last_use var_name in
    intervals := { var_name = var_name; start = first; ending = last; assigned_reg = None } :: !intervals
  ) var_first_use;
  
  (* 按开始位置排序 *)
  List.sort (fun a b -> compare a.start b.start) !intervals

(* 线性扫描寄存器分配算法 *)
let linear_scan_register_allocation (intervals : live_interval list) =
  (* 创建寄存器池 *)
  let reg_pool = create_register_pool () in
  let active = ref [] in
  
  (* 按照开始时间排序的区间 *)
  List.iter (fun interval ->
    (* 过期的区间从活跃列表中移除 *)
    active := List.filter (fun i -> i.ending >= interval.start) !active;
    
    (* 为过期区间的寄存器标记为可用 *)
    List.iter (fun expired_interval ->
      match expired_interval.assigned_reg with
      | Some reg_name ->
          let (_, status) = List.find (fun (r, _) -> r = reg_name) reg_pool in
          status.free <- true;
          status.current_var <- None
      | None -> ()
    ) (List.filter (fun i -> i.ending < interval.start) !active);
    
    (* 尝试分配寄存器 *)
    let assigned = ref false in
    List.iter (fun (reg_name, status) ->
      if not !assigned && status.free then begin
        interval.assigned_reg <- Some reg_name;
        status.free <- false;
        status.current_var <- Some interval.var_name;
        status.expires_at <- interval.ending;
        assigned := true
      end
    ) reg_pool;
    
    (* 如果没有可用寄存器，该变量将保留在栈上 *)
    active := interval :: !active
  ) intervals;
  
  (* 返回分配结果：变量名到寄存器的映射 *)
  let result = Hashtbl.create (List.length intervals) in
  List.iter (fun interval ->
    match interval.assigned_reg with
    | Some reg -> Hashtbl.add result interval.var_name reg
    | None -> () (* 保留在栈上的变量不添加到结果中 *)
  ) intervals;
  
  result

(* 主函数：对函数体进行寄存器分配 *)
let allocate_registers (func : ir_func) : (string, string) Hashtbl.t =
  let intervals = calculate_live_intervals func.body in
  linear_scan_register_allocation intervals
