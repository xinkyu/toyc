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

(* 提取操作数中的所有寄存器/变量 *)
let extract_regs op =
  match op with
  | Reg r | Var r -> [r]
  | _ -> []

(* 安全的CSE实现 - 更加保守的方法 *)
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
  
  (* 表达式到寄存器的映射 *)
  let expr_map = Hashtbl.create 50 in
  
  (* 更加安全的CSE - 跟踪活跃的寄存器 *)
  let live_regs = Hashtbl.create 50 in
  List.iter (fun r -> Hashtbl.add live_regs r ()) 
    (List.fold_left (fun acc inst ->
      match inst with
      | Binop (_, _, lhs, rhs) -> 
          acc @ (extract_regs lhs) @ (extract_regs rhs)
      | Unop (_, _, src) -> 
          acc @ (extract_regs src)
      | Assign (_, src) ->
          acc @ (extract_regs src)
      | _ -> acc
    ) [] block.insts);
  
  (* 处理单个指令 *)
  let process_inst inst =
    match inst with
    | Binop (_, dst, lhs, rhs) as binop ->
        (* 只考虑两个操作数都是已定义寄存器或立即数的情况 *)
        (match (lhs, rhs) with
        | (Reg l | Var l), (Reg r | Var r) 
            when Hashtbl.mem live_regs l && Hashtbl.mem live_regs r ->
            let sig_opt = make_signature binop in
            (match sig_opt with
            | Some signature ->
                (match Hashtbl.find_opt expr_map signature with
                | Some existing_reg when Hashtbl.mem live_regs (get_reg_name existing_reg) ->
                    (* 使用已有表达式替代 *)
                    Assign (dst, existing_reg)
                | _ ->
                    (* 记录新表达式 *)
                    (match dst with
                    | Reg d | Var d -> 
                        Hashtbl.replace live_regs d ();
                        (match sig_opt with
                        | Some s -> Hashtbl.replace expr_map s dst
                        | None -> ())
                    | _ -> ());
                    inst)
            | None -> inst)
        | _ -> inst)
        
    | Unop (_, dst, src) as unop ->
        (* 只考虑操作数是已定义寄存器的情况 *)
        (match src with
        | Reg s | Var s when Hashtbl.mem live_regs s ->
            let sig_opt = make_signature unop in
            (match sig_opt with
            | Some signature ->
                (match Hashtbl.find_opt expr_map signature with
                | Some existing_reg when Hashtbl.mem live_regs (get_reg_name existing_reg) ->
                    (* 使用已有表达式替代 *)
                    Assign (dst, existing_reg)
                | _ ->
                    (* 记录新表达式 *)
                    (match dst with
                    | Reg d | Var d -> 
                        Hashtbl.replace live_regs d ();
                        (match sig_opt with
                        | Some s -> Hashtbl.replace expr_map s dst
                        | None -> ())
                    | _ -> ());
                    inst)
            | None -> inst)
        | _ -> inst)
        
    | Assign (dst, _) ->
        (* 更新活跃寄存器表 *)
        (match dst with
        | Reg d | Var d -> Hashtbl.replace live_regs d ()
        | _ -> ());
        inst
        
    | Call _ ->
        (* 对于函数调用，清空表达式映射（保守处理） *)
        Hashtbl.clear expr_map;
        (match inst with
        | Call (dst, _, _) ->
            (match dst with
            | Reg d | Var d -> Hashtbl.replace live_regs d ()
            | _ -> ())
        | _ -> ());
        inst
        
    | _ -> inst
  in
  
  (* 处理所有指令 *)
  let new_insts = List.map process_inst block.insts in
  { block with insts = new_insts }

(* 对所有基本块应用CSE *)
let common_subexpr_elimination (blocks : ir_block list) : ir_block list =
  List.map apply_cse blocks