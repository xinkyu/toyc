(* file: lib/cse.ml *)

open Ir

(* --- 新增：添加缺失的 string_of_operand 辅助函数 --- *)
let string_of_operand = function
  | Reg name -> name
  | Imm i -> string_of_int i
  | Var name -> name

(* CSE表达式的“签名”，用于唯一标识一个计算 *)
type expr_signature =
  | BinopSig of string * operand * operand
  | UnopSig of string * operand

(* 创建表达式签名，但做规范化处理：(a+b) 和 (b+a) 应有相同签名 *)
let make_signature inst =
  match inst with
  | Binop (op, _, lhs, rhs) ->
      (* 对于可交换的运算符，将操作数排序以保证唯一性 *)
      if op = "+" || op = "*" || op = "==" || op = "!=" then
        if string_of_operand lhs > string_of_operand rhs then
          Some (BinopSig (op, rhs, lhs))
        else
          Some (BinopSig (op, lhs, rhs))
      else
        Some (BinopSig (op, lhs, rhs))
  | Unop (op, _, src) -> Some (UnopSig (op, src))
  | _ -> None

(* 获取指令定义的目标寄存器名 *)
let get_dst_name = function
  | Binop (_, dst, _, _) | Unop (_, dst, _) | Assign (dst, _)
  | Call (dst, _, _) | Load (dst, _) ->
      (match dst with
      | Reg r | Var r -> Some r
      | _ -> None)
  | _ -> None

(* 核心：对单个基本块应用安全的局部CSE *)
let apply_cse_to_block (block: ir_block) : ir_block =
  (* Hashtbl: expr_signature -> operand (存储了该表达式结果的临时变量) *)
  let available_exprs = Hashtbl.create 50 in
  let new_insts = ref [] in

  List.iter (fun inst ->
    let signature = make_signature inst in
    let is_eliminated = ref false in

    (* 1. 检查当前指令是否可以被已有的公共子表达式替换 *)
    (match signature with
    | Some sig_val ->
        (match Hashtbl.find_opt available_exprs sig_val with
        | Some saved_operand ->
            (* 找到了！用一个Assign指令替换当前指令 *)
            (match get_dst_name inst with
            | Some dst_name ->
                new_insts := Assign (Var dst_name, saved_operand) :: !new_insts;
                is_eliminated := true
            | None -> ());
        | None -> ())
    | None -> ());

    if not !is_eliminated then
      begin
        (* 2. 如果指令没有被替换，那么它就是一个新的“定义” *)
        (* 首先，这个新定义可能会使之前的一些可用表达式失效 *)
        (match get_dst_name inst with
        | Some dst_name ->
            Hashtbl.iter (fun sig_val _ ->
              match sig_val with
              | BinopSig (_, op1, op2) ->
                  if string_of_operand op1 = dst_name || string_of_operand op2 = dst_name then
                    Hashtbl.remove available_exprs sig_val
              | UnopSig (_, op1) ->
                  if string_of_operand op1 = dst_name then
                    Hashtbl.remove available_exprs sig_val
            ) available_exprs
        | None -> ());

        (* 其次，将当前指令加入可用表达式池 *)
        (match signature with
        | Some sig_val ->
            (match get_dst_name inst with
            | Some dst_name -> Hashtbl.add available_exprs sig_val (Var dst_name)
            | None -> ())
        | None -> ());
        
        new_insts := inst :: !new_insts
      end
  ) block.insts;

  { block with insts = List.rev !new_insts }

(* 对程序中所有函数的所有基本块应用CSE *)
let common_subexpr_elimination (blocks: ir_block list) : ir_block list =
  List.map apply_cse_to_block blocks