(* file: lib/astToIR.ml *)

open Ast
open Ir

module Env = Map.Make (String)

module Envs = struct
  type t = operand Env.t list
  let empty : t = [Env.empty]
  let enter (stk : t) : t = Env.empty :: stk
  let exit = function
    | _ :: tl -> tl
    | [] -> failwith "EnvStack.exit: empty stack"
  let add name v = function
    | top :: tl -> Env.add name v top :: tl
    | [] -> failwith "EnvStack.add: empty stack"
  let rec lookup name = function
    | [] -> failwith ("unbound variable: " ^ name)
    | m :: ms -> (match Env.find_opt name m with Some v -> v | None -> lookup name ms)
end

type context = {
  env_stack : Envs.t ref;
  break_lbl : string option;
  continue_lbl : string option;
}

let tempid = ref 0
let ftemp () =
  let id = !tempid in
  incr tempid;
  Reg ("t" ^ string_of_int id)

let nameid = ref 0
let fname base = let id = !nameid in incr nameid; base ^ "_" ^ string_of_int id

let labelid = ref 0
let flabel () =
  let id = !labelid in
  incr labelid;
  "L" ^ string_of_int id

(* New function to generate unique block labels with context *)
let block_label_map = ref (Hashtbl.create 50)
let get_unique_label label =
  match Hashtbl.find_opt !block_label_map label with
  | Some existing -> existing
  | None ->
      let unique = label ^ "_" ^ string_of_int !labelid in
      incr labelid;
      Hashtbl.add !block_label_map label unique;
      unique

let string_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Eq -> "==" | Neq -> "!=" | Less -> "<" | Leq -> "<="
  | Greater -> ">" | Geq -> ">=" | Land -> "&&" | Lor -> "||"

let string_unop = function Not -> "!" | Plus -> "+" | Minus -> "-"

type stmt_res = Normal of ir_inst list | Returned of ir_inst list
let flatten = function Normal code | Returned code -> code
let ends insts = match List.rev insts with Goto _ :: _ -> true | Ret _ :: _ -> true | _ -> false

let rec expr_ir (ctx : context) (e : expr) : operand * ir_inst list =
  match e with
  | Number n -> (Imm n, [])
  | ID name -> (Envs.lookup name !(ctx.env_stack), [])
  | Unop (op, e1) -> (
      let operand, code = expr_ir ctx e1 in
      match operand with
      | Imm n ->
          let folded = match op with
            | Plus -> Imm n | Minus -> Imm (-n) | Not -> Imm (if n = 0 then 1 else 0)
          in (folded, code)
      | _ -> let res = ftemp () in (res, code @ [ Unop (string_unop op, res, operand) ]))
  | Binop (op, e1, e2) -> (
      let lhs, c1 = expr_ir ctx e1 in
      let rhs, c2 = expr_ir ctx e2 in
      match (lhs, rhs) with
      | Imm a, Imm b ->
          let folded = match op with
            | Add -> Imm (a + b) | Sub -> Imm (a - b) | Mul -> Imm (a * b)
            | Div -> Imm (a / b) | Mod -> Imm (a mod b) | Eq -> Imm (if a = b then 1 else 0)
            | Neq -> Imm (if a <> b then 1 else 0) | Less -> Imm (if a < b then 1 else 0)
            | Leq -> Imm (if a <= b then 1 else 0) | Greater -> Imm (if a > b then 1 else 0)
            | Geq -> Imm (if a >= b then 1 else 0) | Lor | Land -> Imm 0
          in (folded, c1 @ c2)
      | _ -> let dst = ftemp () in (dst, c1 @ c2 @ [ Binop (string_binop op, dst, lhs, rhs) ]))
  | Call (f, args) ->
      let codes, oprs =
        List.fold_left
          (fun (acc_code, acc_opr) arg -> let opr, code = expr_ir ctx arg in (acc_code @ code, acc_opr @ [ opr ]))
          ([], []) args
      in
      let ret = ftemp () in (ret, codes @ [ Call (ret, f, oprs) ])

let rec dstmt = function
  | If (cond, then_b, Some else_b) ->
      let ands = Ast.split_and cond in
      if List.length ands > 1 then
        let rec nand = function
          | [x] -> If(x, then_b, Some else_b) | hd::tl -> If(hd, Block [nand tl], Some else_b) | [] -> Block []
        in dstmt (nand ands)
      else
      let ors = Ast.split_or cond in
      if List.length ors > 1 then
        let rec nor = function
          | [x] -> If(x, then_b, Some else_b) | hd::tl -> If(hd, then_b, Some (nor tl)) | [] -> Block []
        in dstmt (nor ors)
      else If(cond, dstmt then_b, Some (dstmt else_b))
  | If(cond, then_b, None) ->
      let ands = Ast.split_and cond in
      if List.length ands > 1 then
        let rec nand = function
          | [x] -> If(x, then_b, None) | hd::tl -> If(hd, Block [nand tl], None) | [] -> Block []
        in dstmt (nand ands)
      else
      let ors = Ast.split_or cond in
      if List.length ors > 1 then
        let rec nor = function
          | [x] -> If(x, then_b, None) | hd::tl -> If(hd, then_b, Some (nor tl)) | [] -> Block []
        in dstmt (nor ors)
      else If(cond, dstmt then_b, None)
  | While(cond, body) -> While(cond, dstmt body)
  | Block ss -> Block(List.map dstmt ss)
  | other -> other

let rec stmt_res (ctx : context) (s : stmt) : stmt_res =
  match s with
  | Empty -> Normal []
  | ExprStmt e -> let _, code = expr_ir ctx e in Normal code
  | Decl (x, None) -> let new_name = fname x in ctx.env_stack := Envs.add x (Var new_name) !(ctx.env_stack); Normal []
  | Decl (x, Some e) -> let v, c = expr_ir ctx e in let new_name = fname x in ctx.env_stack := Envs.add x (Var new_name) !(ctx.env_stack); Normal (c @ [ Assign (Var new_name, v) ])
  | Assign (x, e) -> let v, c = expr_ir ctx e in let var = Envs.lookup x !(ctx.env_stack) in Normal (c @ [ Assign (var, v) ])
  | Return None -> Returned [ Ret None ]
  | Return (Some e) -> let v, c = expr_ir ctx e in Returned (c @ [ Ret (Some v) ])
  | If (cond, tstmt, Some fstmt) -> (
      let cnd, cc = expr_ir ctx cond in
      let lthen = flabel () and lelse = flabel () and lend = flabel () in
      let then_res = stmt_res ctx (dstmt tstmt) and else_res = stmt_res ctx (dstmt fstmt) in
      let raw_then = flatten then_res in let then_code = if ends raw_then then raw_then else raw_then @ [ Goto lend ] in
      let raw_else = flatten else_res in let else_code = if ends raw_else then raw_else else raw_else @ [ Goto lend ] in
      let code = cc @ [ IfGoto (cnd, lthen); Goto lelse ] @ [ Label lthen ] @ then_code @ [ Label lelse ] @ else_code @ [ Label lend ] in
      match (then_res, else_res) with | Returned _, _ | _, Returned _ -> Returned code | _ -> Normal code)
  | If (cond, tstmt, None) ->
      let cnd, cc = expr_ir ctx cond in
      let lthen = flabel () and lskip = flabel () in
      let then_res = stmt_res ctx (dstmt tstmt) in let then_code = flatten then_res in
      let code = cc @ [ IfGoto (cnd, lthen); Goto lskip ] @ [ Label lthen ] @ then_code @ [ Label lskip ] in Normal code
  | While (cond, body) ->
      let lcond = flabel () and lbody = flabel () and lend = flabel () in
      let ctx_loop = { ctx with break_lbl = Some lend; continue_lbl = Some lcond } in
      let cnd, ccode = expr_ir ctx_loop cond in
      let body_res = stmt_res ctx_loop (dstmt body) in let bcode = flatten body_res in
      let code = [ Goto lcond; Label lcond ] @ ccode @ [ IfGoto (cnd, lbody); Goto lend ] @ [ Label lbody ] @ bcode @ [ Goto lcond; Label lend ] in Normal code
  | Break -> (match ctx.break_lbl with Some lbl -> Normal [ Goto lbl ] | None -> failwith "break")
  | Continue -> (match ctx.continue_lbl with Some lbl -> Normal [ Goto lbl ] | None -> failwith "continue")
  | Block stmts ->
      ctx.env_stack := Envs.enter !(ctx.env_stack);
      let rec loop acc = function | [] -> Normal acc | hd::tl -> (match stmt_res ctx hd with | Returned c -> Returned (acc @ c) | Normal c -> loop (acc @ c) tl)
      in let res = loop [] stmts in ctx.env_stack := Envs.exit !(ctx.env_stack); res

let func_ir (f : func_def) : ir_func =
  let des_body = match dstmt (Block f.body) with Block ss -> ss | _ -> f.body in
  let f' = { f with body = des_body } in
  let init_env = List.fold_left (fun m x -> Env.add x (Var x) m) Env.empty f'.params in
  let ctx0 = { env_stack = ref [init_env]; break_lbl = None; continue_lbl = None } in
  let body_res = stmt_res ctx0 (Block f'.body) in let raw_code = flatten body_res in
  let bodycode = match List.rev raw_code with | Label _ :: rest_rev -> List.rev rest_rev | _ -> raw_code in
  { name = f'.func_name; args = f'.params; body = bodycode }

(* Improved pblocks function that prevents duplicate labels *)
let pblocks (insts : ir_inst list) : ir_block list =
  (* Reset the label map for each function *)
  block_label_map := Hashtbl.create 50;
  
  (* Ensure we start with a label *)
  let insts_with_entry = match insts with
    | Label _ :: _ -> insts
    | _ -> Label (get_unique_label "entry") :: insts
  in
  
  (* First pass: Find all label names and assign unique IDs *)
  let label_map = Hashtbl.create 50 in
  let _ = List.fold_left (fun _ inst ->
      match inst with
      | Label l -> 
          if not (Hashtbl.mem label_map l) then
            Hashtbl.add label_map l (get_unique_label l)
      | _ -> ()
    ) () insts_with_entry
  in
  
  (* Replace labels in instructions *)
  let replace_label l =
    match Hashtbl.find_opt label_map l with
    | Some unique -> unique
    | None -> 
        let unique = get_unique_label l in
        Hashtbl.add label_map l unique;
        unique
  in
  
  let remap_inst inst =
    match inst with
    | Label l -> Label (replace_label l)
    | Goto l -> Goto (replace_label l)
    | IfGoto (cond, l) -> IfGoto (cond, replace_label l)
    | _ -> inst
  in
  
  let remapped_insts = List.map remap_inst insts_with_entry in
  
  (* Group instructions by labels *)
  let rec group_blocks acc current_label current_insts = function
    | [] -> 
        (* Add the last block *)
        if current_insts = [] then acc
        else (current_label, List.rev current_insts) :: acc
    | (Label l) :: rest ->
        (* When we find a new label, finish the current block and start a new one *)
        let new_acc = 
          if current_insts = [] then acc 
          else (current_label, List.rev current_insts) :: acc 
        in
        group_blocks new_acc l [] rest
    | inst :: rest ->
        (* Add instruction to current block *)
        group_blocks acc current_label (inst :: current_insts) rest
  in
  
  (* Get initial blocks - grouped by labels *)
  let initial_blocks = match remapped_insts with
    | Label first_label :: rest -> 
        group_blocks [] first_label [] rest
    | _ -> failwith "pblocks: expected Label after remapping"
  in
  
  (* Convert blocks to ir_block records *)
  let blocks = List.rev initial_blocks in
  
  (* Process blocks to determine terminators and successors *)
  let rec process_blocks acc = function
    | [] -> List.rev acc
    | (label, insts) :: rest ->
        let next_label = match rest with
          | (next_l, _) :: _ -> Some next_l
          | [] -> None
        in
        
        (* Determine terminator based on last instruction *)
        let (terminator, final_insts) = match List.rev insts with
          | Ret op :: remaining -> (TermRet op, List.rev remaining)
          | Goto target :: remaining -> (TermGoto target, List.rev remaining)
          | IfGoto (cond, target) :: remaining ->
              (match next_label with
               | Some next -> (TermIf (cond, target, next), List.rev remaining)
               | None -> failwith "pblocks: IfGoto at end with no next block")
          | _ -> 
              (match next_label with
               | Some next -> (TermSeq next, insts)
               | None -> (TermRet None, insts)) (* Default terminator for last block *)
        in
        
        let block = {
          label;
          insts = final_insts;
          terminator;
          preds = [];
          succs = [];
          def = StringSet.empty;
          use = StringSet.empty;
          live_in = StringSet.empty;
          live_out = StringSet.empty
        } in
        
        (* Determine successors based on terminator *)
        let succs = match terminator with
          | TermGoto l -> [l]
          | TermSeq l -> [l] 
          | TermIf (_, l1, l2) -> [l1; l2]
          | TermRet _ -> []
        in
        
        let block_with_succs = {block with succs} in
        process_blocks (block_with_succs :: acc) rest
  in
  
  let blocks_with_succs = process_blocks [] blocks in
  
  (* Final pass: Fill in predecessors *)
  let block_map = List.fold_left (fun map b -> 
      StringMap.add b.label b map
  ) StringMap.empty blocks_with_succs in
  
  List.iter (fun b ->
      List.iter (fun succ_label ->
          match StringMap.find_opt succ_label block_map with
          | Some succ_block -> 
              succ_block.preds <- b.label :: succ_block.preds
          | None -> ()
      ) b.succs
  ) blocks_with_succs;
  
  blocks_with_succs

let func_iro (f : func_def) : allocated_func =
  labelid := 0;
  let init_map = List.fold_left (fun m name -> Env.add name (Var name) m) Env.empty f.params in
  let ctx0 = { env_stack = ref [init_map]; break_lbl = None; continue_lbl = None } in
  let bodycode = stmt_res ctx0 (Block f.body) |> flatten in
  let raw_blocks = pblocks bodycode in
  let opt_blocks = Cfg.optimize raw_blocks in
  let alloc_map, spill_size = Regalloc.run opt_blocks in
  { name = f.func_name;
    args = f.params;
    blocks = opt_blocks;
    alloc_map = alloc_map;
    stack_size = abs spill_size;
  }

let program_ir (cu : comp_unit) (optimize_flag : bool) : ir_program =
  if optimize_flag then
    Ir_funcs_alloc (List.map func_iro cu)
  else
    Ir_funcs (List.map func_ir cu)