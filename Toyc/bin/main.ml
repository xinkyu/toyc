open Compilerlib
open Ast

let parse_program (s : string) : func_def list =
  let lexbuf = Lexing.from_string s in
  try Parser.comp_unit Lexer.token lexbuf
  with Parsing.Parse_error ->
    let pos = lexbuf.Lexing.lex_curr_p in
    let line = pos.Lexing.pos_lnum in
    let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
    let token = Lexing.lexeme lexbuf in
    Printf.eprintf "Syntax error at line %d, column %d: unexpected token '%s'\n"
      line col token;
    exit 1

let () =
  Printexc.record_backtrace true;

  (* 支持从 stdin 读取所有输入 *)
  let read_all_input () =
    let rec aux acc =
      try
        let line = input_line stdin in
        aux (line :: acc)
      with End_of_file -> String.concat "\n" (List.rev acc)
    in
    aux []
  in

  (* 处理命令行参数 *)
  let args = Array.to_list Sys.argv |> List.tl in
  let option_flags = [ "-print_ast"; "-print_ir"; "-block-ir"; "-opt" ] in
  let print_ast = List.exists (( = ) "-print_ast") args in
  let print_ir = List.exists (( = ) "-print_ir") args in
  let block_ir = List.exists (( = ) "-block-ir") args in
  let opt_flag = List.exists (( = ) "-opt") args in
  let opt_flag = block_ir || opt_flag in

  (* 读取 stdin 输入 *)
  let input = read_all_input () in

  (* 解析 AST *)
  let ast = parse_program input in

  if print_ast then
    Printf.printf "AST:\n\n%s\n\n" (Print_ast.string_of_comp_unit ast);

  (* 生成中间代码 *)
  let ir = AstToIR.program_ir ast true in

  (* 应用优化 *)
  let ir = 
    if opt_flag then 
      Optimizer.optimize_ir_program ir
    else
      ir
  in

  if print_ir then begin 
    Printf.printf "IR:\n\n";
    Print_ir.print_ir_program ir;
  end;

  let asm = IrToAsm.com_pro ir in

  Printf.printf "\n\n%s\n" asm