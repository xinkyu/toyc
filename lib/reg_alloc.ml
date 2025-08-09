open Ir

(* 可用的寄存器列表 (t3-t6, s0-s11) *)
let available_registers = [
  "t3"; "t4"; "t5"; "t6";
  "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; 
  "s6"; "s7"; "s8"; "s9"; "s10"; "s11"
]

(* 变量使用信息 *)
type var_info = {
  mutable use_count: int;       (* 使用次数 *)
  mutable last_use: int;        (* 最后一次使用的位置 *)
  mutable reg: string option;   (* 分配的寄存器 *)
  mutable in_stack: bool;       (* 是否也在栈上 *)
}

module StringMap = Map.Make(String)

(* 分析基本块中的变量使用情况 *)
let analyze_block_usage (block : ir_inst list) : var_info StringMap.t =
  let var_map = ref StringMap.empty in
  let inst_index = ref 0 in
  
  (* 获取或创建变量信息 *)
  let get_var_info var =
    match StringMap.find_opt var !var_map with
    | Some info -> info
    | None -> 
        let info = { use_count = 0; last_use = 0; reg = None; in_stack = true } in
        var_map := StringMap.add var info !var_map;
        info
  in
  
  (* 记录变量使用 *)
  let record_use var =
    let info = get_var_info var in
    info.use_count <- info.use_count + 1;
    info.last_use <- !inst_index
  in
  
  (* 记录操作数使用 *)
  let record_operand = function
    | Reg name | Var name -> record_use name
    | Imm _ -> ()
  in
  
  (* 分析指令 *)
  List.iter (fun inst ->
    incr inst_index;
    match inst with
    | Binop (_, dst, src1, src2) ->
        (match dst with Reg name | Var name -> record_use name | _ -> ());
        record_operand src1;
        record_operand src2
    | Unop (_, dst, src) ->
        (match dst with Reg name | Var name -> record_use name | _ -> ());
        record_operand src
    | Assign (dst, src) ->
        (match dst with Reg name | Var name -> record_use name | _ -> ());
        record_operand src
    | Call (dst, _, args) ->
        (match dst with Reg name | Var name -> record_use name | _ -> ());
        List.iter record_operand args
    | Load (dst, src) ->
        (match dst with Reg name | Var name -> record_use name | _ -> ());
        record_operand src
    | Store (addr, value) ->
        record_operand addr;
        record_operand value
    | IfGoto (cond, _) ->
        record_operand cond
    | Ret (Some op) ->
        record_operand op
    | _ -> ()
  ) block;
  
  !var_map

(* 分配寄存器 *)
let allocate_block_registers (var_map : var_info StringMap.t) : unit =
  (* 按使用频率排序变量 *)
  let vars = 
    StringMap.bindings var_map
    |> List.filter (fun (_, info) -> info.use_count > 1) (* 只为多次使用的变量分配寄存器 *)
    |> List.sort (fun (_, info1) (_, info2) -> 
        compare info2.use_count info1.use_count) (* 使用频率从高到低 *)
  in
  
  (* 分配寄存器 *)
  let rec allocate reg_list = function
    | [] -> ()
    | (_, info) :: rest ->  (* 修改这里，使用下划线忽略未使用的变量 *)
        match reg_list with
        | [] -> 
            (* 没有更多寄存器可用 *)
            allocate [] rest
        | reg :: regs ->
            (* 分配寄存器 *)
            info.reg <- Some reg;
            allocate regs rest
  in
  
  allocate available_registers vars

(* 分析整个函数的变量使用 *)
let analyze_func_usage (func : ir_func) : var_info StringMap.t =
  analyze_block_usage func.body

(* 为整个函数分配寄存器 *)
let allocate_func_registers (func : ir_func) : var_info StringMap.t =
  let var_map = analyze_func_usage func in
  allocate_block_registers var_map;
  var_map

(* 为基本块分配寄存器 *)
let allocate_block_regs (block : ir_block) : var_info StringMap.t =
  let var_map = analyze_block_usage block.insts in
  allocate_block_registers var_map;
  var_map

(* 查询变量对应的物理寄存器 *)
let get_var_register (var_map : var_info StringMap.t) (var : string) : string option =
  match StringMap.find_opt var var_map with
  | Some info -> info.reg
  | None -> None