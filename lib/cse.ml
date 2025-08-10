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

(* 对基本块应用CSE *)
let apply_cse (block : ir_block) : ir_block =
  (* 表达式到结果变量的映射 *)
  let expr_map = Hashtbl.create 50 in
  
  (* 处理单条指令 *)
  let process_inst inst acc =
    match inst with
    | Binop (_, dst, _, _) as binop ->
        let sig_opt = make_signature binop in
        (match sig_opt with
        | Some signature ->
            (match Hashtbl.find_opt expr_map signature with
            | Some existing_reg ->
                (* 已存在相同表达式，用Assign替代 *)
                let assign = Assign (dst, existing_reg) in
                assign :: acc
            | None ->
                (* 新表达式，记录并保留 *)
                Hashtbl.add expr_map signature dst;
                binop :: acc)
        | None -> binop :: acc)
    
    | Unop (_, dst, _) as unop ->
        let sig_opt = make_signature unop in
        (match sig_opt with
        | Some signature ->
            (match Hashtbl.find_opt expr_map signature with
            | Some existing_reg ->
                (* 已存在相同表达式，用Assign替代 *)
                let assign = Assign (dst, existing_reg) in
                assign :: acc
            | None ->
                (* 新表达式，记录并保留 *)
                Hashtbl.add expr_map signature dst;
                unop :: acc)
        | None -> unop :: acc)
    
    | inst when has_side_effects inst ->
        (* 有副作用的指令会使表达式失效 *)
        Hashtbl.clear expr_map;
        inst :: acc
    
    | _ -> inst :: acc
  in
  
  (* 处理基本块中的所有指令 *)
  let new_insts = List.fold_right process_inst block.insts [] in
  { block with insts = new_insts }

(* 对所有基本块应用CSE *)
let common_subexpr_elimination (blocks : ir_block list) : ir_block list =
  List.map apply_cse blocks
