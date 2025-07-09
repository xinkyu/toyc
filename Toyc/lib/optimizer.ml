open Ir

(* 为进一步优化添加的工具函数 *)

(* 检查表达式是否可以进行常量折叠 *)
let is_constant_foldable op op1 op2 =
  match (op1, op2) with
  | Imm _, Imm _ -> true
  | _ -> false

(* 计算常量折叠后的值 *)
let fold_constant op op1 op2 =
  match (op1, op2) with
  | Imm a, Imm b ->
      match op with
      | "+" -> Imm (a + b)
      | "-" -> Imm (a - b)
      | "*" -> Imm (a * b)
      | "/" when b <> 0 -> Imm (a / b)
      | "%" when b <> 0 -> Imm (a mod b)
      | "==" -> Imm (if a = b then 1 else 0)
      | "!=" -> Imm (if a <> b then 1 else 0)
      | "<" -> Imm (if a < b then 1 else 0)
      | "<=" -> Imm (if a <= b then 1 else 0)
      | ">" -> Imm (if a > b then 1 else 0)
      | ">=" -> Imm (if a >= b then 1 else 0)
      | "&&" -> Imm (if a <> 0 && b <> 0 then 1 else 0)
      | "||" -> Imm (if a <> 0 || b <> 0 then 1 else 0)
      | _ -> failwith ("Unknown binary operator: " ^ op)
  | _ -> failwith "Non-constant operands"

(* 强度削减优化 *)
let strength_reduction op dst op1 op2 =
  match (op, op1, op2) with
  | "*", op1, Imm 2 -> Binop ("+", dst, op1, op1)  (* x*2 => x+x *)
  | "*", op1, Imm i when i > 0 && i land (i - 1) = 0 ->
      (* 使用 slli 指令，但在 IR 层面仍然使用乘法，在 IrToAsm 中进行转换 *)
      Binop ("*", dst, op1, op2)
  | "/", op1, Imm 2 -> 
      (* 使用 srai 指令，但在 IR 层面仍然使用除法，在 IrToAsm 中进行转换 *)
      Binop ("/", dst, op1, op2)
  | "/", op1, Imm i when i > 0 && i land (i - 1) = 0 ->
      (* 使用 srai 指令，但在 IR 层面仍然使用除法，在 IrToAsm 中进行转换 *)
      Binop ("/", dst, op1, op2)
  | _ -> Binop (op, dst, op1, op2)

(* 优化指令 *)
let optimize_inst = function
  | Binop (op, dst, op1, op2) when is_constant_foldable op op1 op2 ->
      Assign (dst, fold_constant op op1 op2)
  | Binop (op, dst, op1, op2) ->
      strength_reduction op dst op1 op2
  | Unop (op, dst, Imm i) ->
      let res = match op with
        | "+" -> Imm i
        | "-" -> Imm (-i)
        | "!" -> Imm (if i = 0 then 1 else 0)
        | _ -> failwith ("Unknown unary operator: " ^ op)
      in
      Assign (dst, res)
  | inst -> inst

(* 检查是否是冗余的加载/存储 *)
let is_redundant_load_store prev_insts inst =
  match inst with
  | Load (dst1, src1) ->
      List.exists (function
        | Store (src2, val2) when src1 = src2 -> true  (* 加载刚刚存储的值 *)
        | _ -> false
      ) prev_insts
  | _ -> false

(* 公共子表达式消除 *)
let eliminate_common_subexpressions insts =
  let expr_table = Hashtbl.create 100 in
  let optimized_insts = ref [] in
  
  List.iter (fun inst ->
    match inst with
    | Binop (op, dst, op1, op2) ->
        let key = (op, op1, op2) in
        if Hashtbl.mem expr_table key then
          (* 找到了公共子表达式 *)
          let existing_var = Hashtbl.find expr_table key in
          optimized_insts := Assign (dst, existing_var) :: !optimized_insts
        else begin
          (* 新的表达式，添加到表中 *)
          Hashtbl.add expr_table key dst;
          optimized_insts := inst :: !optimized_insts
        end
    | _ ->
        optimized_insts := inst :: !optimized_insts
  ) insts;
  
  List.rev !optimized_insts

(* 死代码消除 *)
let eliminate_dead_code insts =
  (* 识别哪些变量是活跃的 *)
  let rec find_live_vars insts =
    let live_vars = Hashtbl.create 100 in
    
    (* 标记使用了的变量 *)
    let mark_used = function
      | Reg r | Var r -> Hashtbl.replace live_vars r true
      | _ -> ()
    in
    
    (* 倒序遍历指令 *)
    let rec process_insts = function
      | [] -> live_vars
      | inst :: rest ->
          match inst with
          | Binop (_, dst, op1, op2) ->
              (match dst with
               | Reg r | Var r ->
                   (* 如果这个变量后续没被使用，它是死代码 *)
                   if not (Hashtbl.mem live_vars r) then
                     process_insts rest  (* 跳过这条指令 *)
                   else begin
                     (* 否则，标记操作数为活跃 *)
                     mark_used op1;
                     mark_used op2;
                     process_insts rest
                   end
               | _ -> process_insts rest)
          | Unop (_, dst, op) ->
              (match dst with
               | Reg r | Var r ->
                   if not (Hashtbl.mem live_vars r) then
                     process_insts rest
                   else begin
                     mark_used op;
                     process_insts rest
                   end
               | _ -> process_insts rest)
          | Assign (dst, src) ->
              (match dst with
               | Reg r | Var r ->
                   if not (Hashtbl.mem live_vars r) then
                     process_insts rest
                   else begin
                     mark_used src;
                     process_insts rest
                   end
               | _ -> process_insts rest)
          | _ -> process_insts rest
    in
    
    process_insts (List.rev insts)
  in
  
  let live_vars = find_live_vars insts in
  
  (* 过滤死代码 *)
  List.filter (function
    | Binop (_, dst, _, _)
    | Unop (_, dst, _)
    | Assign (dst, _) ->
        (match dst with
         | Reg r | Var r -> Hashtbl.mem live_vars r
         | _ -> true)
    | _ -> true
  ) insts

(* 窥孔优化 - 查找并替换指令模式 *)
let peephole_optimize insts =
  let rec optimize acc = function
    | [] -> List.rev acc
    | inst1 :: inst2 :: rest ->
        (match (inst1, inst2) with
         | Assign (dst1, src1), Assign (dst2, src2) when dst1 = src2 && dst2 = src1 ->
             (* 识别形如: t1 = t2; t2 = t1 的无用赋值 *)
             optimize (inst1 :: acc) rest
         | Binop ("+", dst, src, Imm 0), _ ->
             (* x + 0 = x *)
             optimize (Assign (dst, src) :: acc) (inst2 :: rest)
         | Binop ("*", dst, src, Imm 1), _ ->
             (* x * 1 = x *)
             optimize (Assign (dst, src) :: acc) (inst2 :: rest)
         | Binop ("*", dst, _, Imm 0), _ ->
             (* x * 0 = 0 *)
             optimize (Assign (dst, Imm 0) :: acc) (inst2 :: rest)
         | _ ->
             optimize (inst1 :: acc) (inst2 :: rest))
    | [inst] -> List.rev (inst :: acc)
  in
  optimize [] insts

(* 主优化函数 *)
let optimize_ir_program program =
  match program with
  | Ir_funcs funcs ->
      let optimized_funcs =
        List.map (fun func ->
          let optimized_body =
            func.body
            |> List.map optimize_inst  (* 常量折叠和强度削减 *)
            |> eliminate_common_subexpressions  (* 消除公共子表达式 *)
            |> eliminate_dead_code  (* 消除死代码 *)
            |> peephole_optimize  (* 窥孔优化 *)
          in
          { func with body = optimized_body }
        ) funcs
      in
      Ir_funcs optimized_funcs
      
  | Ir_funcs_o funcs_o ->
      let optimized_funcs =
        List.map (fun func ->
          let optimized_blocks =
            List.map (fun block ->
              let optimized_insts =
                block.insts
                |> List.map optimize_inst
                |> eliminate_common_subexpressions
                |> eliminate_dead_code
                |> peephole_optimize
              in
              { block with insts = optimized_insts }
            ) func.blocks
          in
          { func with blocks = optimized_blocks }
        ) funcs_o
      in
      Ir_funcs_o optimized_funcs
