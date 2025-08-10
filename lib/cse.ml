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

(* 获取操作数名称 *)
let get_operand_name = function
  | Reg r | Var r -> r
  | _ -> ""

(* 检查操作数是否是寄存器或变量 *)
let is_reg_or_var = function
  | Reg _ | Var _ -> true
  | _ -> false

(* 对基本块应用CSE *)
let apply_cse (block : ir_block) : ir_block =
  (* 表达式到结果变量的映射 *)
  let expr_map = Hashtbl.create 50 in
  
  (* 已定义的寄存器集合 *)
  let defined_regs = Hashtbl.create 50 in
  
  (* 添加一个寄存器到已定义集合 *)
  let add_defined_reg = function
    | Reg r | Var r -> Hashtbl.replace defined_regs r ()
    | _ -> ()
  in
  
  (* 检查寄存器是否已定义 *)
  let is_defined_reg = function
    | Reg r | Var r -> Hashtbl.mem defined_regs r
    | _ -> true (* 立即数总是已定义的 *)
  in
  
  (* 首先收集所有在基本块中定义的寄存器 *)
  List.iter (fun inst ->
    match inst with
    | Binop (_, dst, _, _) 
    | Unop (_, dst, _)
    | Assign (dst, _)
    | Call (dst, _, _)
    | Load (dst, _) -> add_defined_reg dst
    | _ -> ()
  ) block.insts;
  
  (* 处理单条指令 *)
  let process_inst inst acc =
    match inst with
    | Binop (_, dst, lhs, rhs) as binop ->
        (* 只有当操作数都是已定义的寄存器或立即数时才尝试CSE *)
        if is_defined_reg lhs && is_defined_reg rhs then
          let sig_opt = make_signature binop in
          (match sig_opt with
          | Some signature ->
              (match Hashtbl.find_opt expr_map signature with
              | Some existing_reg when is_defined_reg existing_reg ->
                  (* 已存在相同表达式且结果寄存器已定义，用Assign替代 *)
                  let assign = Assign (dst, existing_reg) in
                  add_defined_reg dst;
                  Hashtbl.add expr_map signature dst;
                  assign :: acc
              | _ ->
                  (* 新表达式，记录并保留 *)
                  add_defined_reg dst;
                  Hashtbl.add expr_map signature dst;
                  binop :: acc)
          | None -> 
              add_defined_reg dst;
              binop :: acc)
        else
          (* 如果有操作数未定义，不应用CSE *)
          add_defined_reg dst;
          binop :: acc
    
    | Unop (_, dst, src) as unop ->
        (* 只有当操作数是已定义的寄存器或立即数时才尝试CSE *)
        if is_defined_reg src then
          let sig_opt = make_signature unop in
          (match sig_opt with
          | Some signature ->
              (match Hashtbl.find_opt expr_map signature with
              | Some existing_reg when is_defined_reg existing_reg ->
                  (* 已存在相同表达式且结果寄存器已定义，用Assign替代 *)
                  let assign = Assign (dst, existing_reg) in
                  add_defined_reg dst;
                  Hashtbl.add expr_map signature dst;
                  assign :: acc
              | _ ->
                  (* 新表达式，记录并保留 *)
                  add_defined_reg dst;
                  Hashtbl.add expr_map signature dst;
                  unop :: acc)
          | None -> 
              add_defined_reg dst;
              unop :: acc)
        else
          (* 如果有操作数未定义，不应用CSE *)
          add_defined_reg dst;
          unop :: acc
    
    | Assign (dst, src) ->
        (* 对于赋值，我们只需要追踪目标寄存器 *)
        add_defined_reg dst;
        inst :: acc
    
    | inst when has_side_effects inst ->
        (* 有副作用的指令会使表达式失效 *)
        Hashtbl.clear expr_map;
        (match inst with
        | Call (dst, _, _) 
        | Load (dst, _) -> add_defined_reg dst
        | _ -> ());
        inst :: acc
    
    | _ -> inst :: acc
  in
  
  (* 处理基本块中的所有指令 *)
  let new_insts = List.fold_right process_inst block.insts [] in
  { block with insts = new_insts }

(* 对所有基本块应用CSE *)
let common_subexpr_elimination (blocks : ir_block list) : ir_block list =
  List.map apply_cse blocks
