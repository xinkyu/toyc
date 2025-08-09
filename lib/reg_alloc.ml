(* reg_alloc.ml - 简化的寄存器分配模块 *)
open Ir

(* 可用的寄存器列表 (t3-t6, s0-s11) *)
let available_registers = [
  "t3"; "t4"; "t5"; "t6";
  "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; 
  "s6"; "s7"; "s8"; "s9"; "s10"; "s11"
]

(* 变量使用统计 *)
type var_usage = {
  mutable count: int;      (* 使用次数 *)
  mutable reg: string option;  (* 分配的寄存器 *)
}

module StringMap = Map.Make(String)

(* 统计变量使用频率 *)
let analyze_usage (insts : ir_inst list) : var_usage StringMap.t =
  let usage_map = ref StringMap.empty in
  
  (* 记录变量使用 *)
  let record var =
    let info = match StringMap.find_opt var !usage_map with
      | Some info -> info
      | None -> 
          let new_info = { count = 0; reg = None } in
          usage_map := StringMap.add var new_info !usage_map;
          new_info
    in
    info.count <- info.count + 1
  in
  
  (* 处理操作数 *)
  let process_operand = function
    | Reg name | Var name -> record name
    | Imm _ -> ()
  in
  
  (* 分析指令 *)
  List.iter (fun inst ->
    match inst with
    | Binop (_, dst, src1, src2) ->
        (match dst with 
         | Reg name | Var name -> record name
         | _ -> ());
        process_operand src1;
        process_operand src2
    | Unop (_, dst, src) ->
        (match dst with 
         | Reg name | Var name -> record name
         | _ -> ());
        process_operand src
    | Assign (dst, src) ->
        (match dst with 
         | Reg name | Var name -> record name
         | _ -> ());
        process_operand src
    | Call (dst, _, args) ->
        (match dst with 
         | Reg name | Var name -> record name
         | _ -> ());
        List.iter process_operand args
    | Load (dst, src) ->
        (match dst with 
         | Reg name | Var name -> record name
         | _ -> ());
        process_operand src
    | Store (dst, src) ->
        process_operand dst;
        process_operand src
    | IfGoto (cond, _) ->
        process_operand cond
    | Ret (Some op) ->
        process_operand op
    | _ -> ()
  ) insts;
  
  !usage_map

(* 分配寄存器给变量 *)
let allocate_registers (usage_map : var_usage StringMap.t) : unit =
  let vars = 
    StringMap.bindings usage_map
    |> List.filter (fun (_, info) -> info.count > 1)  (* 只为多次使用的变量分配 *)
    |> List.sort (fun (_, info1) (_, info2) -> 
        compare info2.count info1.count)  (* 使用频率降序 *)
  in
  
  let rec assign reg_list = function
    | [] -> ()
    | (_, info) :: rest ->  (* 使用下划线避免未使用变量警告 *)
        match reg_list with
        | [] -> assign [] rest  (* 没有更多寄存器 *)
        | reg :: regs ->
            info.reg <- Some reg;
            assign regs rest
  in
  
  assign available_registers vars

(* 获取变量的寄存器 *)
let get_register (usage_map : var_usage StringMap.t) (var : string) : string option =
  match StringMap.find_opt var usage_map with
  | Some info -> info.reg
  | None -> None

(* 为函数的指令序列分配寄存器 *)
let allocate_func (func : ir_func) : var_usage StringMap.t =
  let usage_map = analyze_usage func.body in
  allocate_registers usage_map;
  usage_map

(* 为优化的基本块分配寄存器 *)
let allocate_block (block : ir_block) : var_usage StringMap.t =
  let usage_map = analyze_usage block.insts in
  allocate_registers usage_map;
  usage_map