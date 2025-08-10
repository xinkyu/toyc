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

(* 表达式赋值记录 *)
type expr_entry = {
  result: operand;
  orig_expr: ir_inst;
}

(* 检查表达式是否可能被修改 *)
let invalidates expr inst =
  let invalidated_by_write dst =
    match expr, dst with
    | BinopSig(_, Reg r1, _), Reg r2 
    | BinopSig(_, _, Reg r1), Reg r2
    | BinopSig(_, Var r1, _), Var r2
    | BinopSig(_, _, Var r1), Var r2
    | UnopSig(_, Reg r1), Reg r2
    | UnopSig(_, Var r1), Var r2 -> r1 = r2
    | _ -> false
  in
  match inst with
  | Binop(_, dst, _, _)
  | Unop(_, dst, _)
  | Assign(dst, _)
  | Call(dst, _, _)
  | Load(dst, _) -> invalidated_by_write dst
  | Store(_, _) -> true  (* 保守处理，任何内存写操作都可能影响其他值 *)
  | _ -> false

(* 检查操作数是否是临时寄存器 *)
let is_temp = function
  | Reg r -> String.length r > 0 && r.[0] = 't'
  | _ -> false

(* 更高效的CSE实现 *)
let apply_cse (block : ir_block) : ir_block =
  (* 表达式 -> 结果寄存器 映射 *)
  let expr_table = Hashtbl.create 50 in
  
  (* 处理单个指令 *)
  let rec process_insts acc insts =
    match insts with
    | [] -> List.rev acc
    
    | (Binop(op, dst, lhs, rhs) as expr) :: rest ->
        let sig_opt = Some (BinopSig(op, lhs, rhs)) in
        (match sig_opt with
        | Some signature ->
            (match Hashtbl.find_opt expr_table signature with
            | Some entry ->
                (* 找到了相同的表达式，用已有结果替代 *)
                let new_inst = Assign(dst, entry.result) in
                process_insts (new_inst :: acc) rest
            | None ->
                (* 记录新表达式 *)
                Hashtbl.add expr_table signature {result = dst; orig_expr = expr};
                process_insts (expr :: acc) rest)
        | None -> process_insts (expr :: acc) rest)
    
    | (Unop(op, dst, src) as expr) :: rest ->
        let sig_opt = Some (UnopSig(op, src)) in
        (match sig_opt with
        | Some signature ->
            (match Hashtbl.find_opt expr_table signature with
            | Some entry ->
                (* 找到了相同的表达式，用已有结果替代 *)
                let new_inst = Assign(dst, entry.result) in
                process_insts (new_inst :: acc) rest
            | None ->
                (* 记录新表达式 *)
                Hashtbl.add expr_table signature {result = dst; orig_expr = expr};
                process_insts (expr :: acc) rest)
        | None -> process_insts (expr :: acc) rest)
    
    | (Call _ | Store _) :: rest ->
        (* 对于有副作用的指令，清空表达式表 *)
        Hashtbl.clear expr_table;
        process_insts (List.hd insts :: acc) rest
        
    | inst :: rest ->
        (* 检查指令是否使表达式表中的任何条目失效 *)
        Hashtbl.filter_map_inplace (fun key entry ->
            if invalidates key inst then None else Some entry
        ) expr_table;
        process_insts (inst :: acc) rest
  in
  
  (* 处理所有指令 *)
  let new_insts = process_insts [] block.insts in
  { block with insts = new_insts }

(* 对所有基本块应用CSE，并多次应用以捕获更多优化机会 *)
let common_subexpr_elimination (blocks : ir_block list) : ir_block list =
  (* 多次应用CSE以获得更好的结果 *)
  let rec optimize_blocks blocks iterations =
    if iterations = 0 then blocks
    else
      let optimized = List.map apply_cse blocks in
      optimize_blocks optimized (iterations - 1)
  in
  optimize_blocks blocks 2  (* 应用两轮CSE *)