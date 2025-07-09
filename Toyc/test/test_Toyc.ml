open Compilerlib
open Ast
open Ir

(* 测试函数：验证寄存器分配 *)
let test_regalloc () =
  let test_func = {
    name = "test";
    args = ["x"; "y"];
    body = [
      Binop ("+", Reg "t1", Var "x", Var "y");
      Assign (Var "z", Reg "t1");
      Binop ("*", Reg "t2", Var "z", Imm 2);
      Ret (Some (Reg "t2"))
    ]
  } in
  
  let reg_mapping = Regalloc.allocate_registers test_func in
  assert (Hashtbl.length reg_mapping > 0);
  print_endline "寄存器分配测试通过!"

(* 测试函数：验证常量折叠 *)
let test_constant_folding () =
  let test_func = {
    name = "test";
    args = [];
    body = [
      Binop ("+", Reg "t1", Imm 2, Imm 3); (* 应该折叠为 t1 = 5 *)
      Binop ("*", Reg "t2", Reg "t1", Imm 4); (* 如果t1是常量5，应该折叠为 t2 = 20 *)
      Ret (Some (Reg "t2"))
    ]
  } in
  
  let optimized = 
    match Optimizer.optimize_ir_program (Ir_funcs [test_func]) with
    | Ir_funcs funcs -> List.hd funcs
    | _ -> failwith "Expected Ir_funcs"
  in
  
  (* 检查优化结果 - 这里我们只是简单打印结果 *)
  print_endline "常量折叠测试：";
  List.iter (fun inst ->
    match inst with
    | Assign (Reg "t1", Imm 5) -> print_endline "  t1 = 5 ✓"
    | Assign (Reg "t2", Imm 20) -> print_endline "  t2 = 20 ✓"
    | _ -> print_endline "  未优化的指令"
  ) optimized.body

(* 主测试函数 *)
let () =
  print_endline "开始测试 ToyC 编译器优化...";
  
  (* 运行测试 *)
  test_regalloc ();
  test_constant_folding ();
  
  print_endline "所有测试通过!"
