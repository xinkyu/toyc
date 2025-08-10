(* cse.ml - Common Subexpression Elimination *)
open Ir

(* 用于CSE的表达式签名 *)
type expr_signature =
  | BinopSig of string * operand * operand  (* op, lhs, rhs *)
  | UnopSig of string * operand             (* op, src *)

(* 创建表达式签名 *)
let make_signature = function
  | Binop (op, _, lhs, rhs) -> Some (BinopSig (op, lhs, rhs))
  | Unop (op, _, src) -> Some (UnopSig (op, src))
  | _ -> None

(* 检查指令是否有副作用 *)
let has_side_effects = function
  | Call _ | Load _ | Store _ -> true
  | _ -> false

(* 从操作数获取名称 *)
let get_reg_name = function
  | Reg r | Var r -> r
  | _ -> ""

(* 比较两个操作数是否是相同的寄存器/变量 *)
let same_reg op1 op2 =
  match (op1, op2) with
  | (Reg r1 | Var r1), (Reg r2 | Var r2) -> r1 = r2
  | _ -> false

(* 检查操作数是否是立即数 *)
let is_imm = function
  | Imm _ -> true
  | _ -> false

(* 安全的CSE实现 - 只处理最简单和最安全的情况 *)
let apply_cse (block : ir_block) : ir_block =
  (* 收集已经定义的寄存器名称 *)
  let defined_regs = Hashtbl.create 50 in
  
  (* 为了安全起见，先收集所有被定义的寄存器 *)
  List.iter (fun inst ->
    match inst with
    | Binop (_, dst, _, _) 
    | Unop (_, dst, _)
    | Assign (dst, _)
    | Call (dst, _, _)
    | Load (dst, _) ->
        (match dst with
        | Reg r | Var r -> Hashtbl.replace defined_regs r ()
        | _ -> ())
    | _ -> ()
  ) block.insts;
  
  (* 检查寄存器是否已定义 *)
  let is_defined = function
    | Reg r | Var r -> Hashtbl.mem defined_regs r
    | Imm _ -> true
  in
  
  (* 收集基本表达式 - 只考虑简单的二元运算和一元运算 *)
  let expr_map = Hashtbl.create 50 in
  
  (* 第一遍：收集所有表达式 *)
  List.iter (fun inst ->
    match inst with
    | Binop (_, dst, lhs, rhs) when is_defined lhs && is_defined rhs ->
        let sig_opt = make_signature inst in
        (match sig_opt with
        | Some signature -> Hashtbl.replace expr_map signature dst
        | None -> ())
    | Unop (_, dst, src) when is_defined src ->
        let sig_opt = make_signature inst in
        (match sig_opt with
        | Some signature -> Hashtbl.replace expr_map signature dst
        | None -> ())
    | _ -> ()
  ) block.insts;
  
  (* 第二遍：应用优化，但只对安全的情况 *)
  let process_inst inst =
    match inst with
    | Binop (_, dst, lhs, rhs) as binop when is_defined lhs && is_defined rhs ->
        let sig_opt = make_signature binop in
        (match sig_opt with
        | Some signature ->
            (match Hashtbl.find_opt expr_map signature with
            | Some existing_reg when is_defined existing_reg && not (same_reg existing_reg dst) ->
                (* 已存在相同表达式，用Assign替代，但只有当existing_reg和dst不同时 *)
                Assign (dst, existing_reg)
            | _ -> inst)
        | None -> inst)
    | Unop (_, dst, src) as unop when is_defined src ->
        let sig_opt = make_signature unop in
        (match sig_opt with
        | Some signature ->
            (match Hashtbl.find_opt expr_map signature with
            | Some existing_reg when is_defined existing_reg && not (same_reg existing_reg dst) ->
                (* 已存在相同表达式，用Assign替代，但只有当existing_reg和dst不同时 *)
                Assign (dst, existing_reg)
            | _ -> inst)
        | None -> inst)
    | inst when has_side_effects inst ->
        (* 对于有副作用的指令，清空表达式映射 *)
        Hashtbl.clear expr_map;
        inst
    | _ -> inst
  in
  
  (* 处理所有指令 *)
  let new_insts = List.map process_inst block.insts in
  { block with insts = new_insts }

(* 对所有基本块应用CSE *)
let common_subexpr_elimination (blocks : ir_block list) : ir_block list =
  List.map apply_cse blocks
