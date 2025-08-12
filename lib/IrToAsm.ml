(* IrToAsm.ml *)
open Ir

(* A new register allocator for per-basic-block code generation.
  It manages a set of physical temporary registers (t0-t5).
  - It uses a simple Least-Recently-Used (LRU) policy for spilling.
  - At the end of each basic block, all allocated registers are spilled
    back to their stack slots to ensure correctness across blocks.
*)
module Regs = struct
  let temp_regs = [ "t0"; "t1"; "t2"; "t3"; "t4"; "t5" ]
  let num_regs = List.length temp_regs
  (* For operations that need an extra temporary register without disrupting allocation *)
  let scratch_reg = "t6"

  (* Maps a virtual variable name (from IR) to an assigned physical register *)
  let var_to_reg_map = Hashtbl.create num_regs
  (* Maps a physical register to the virtual variable name it currently holds *)
  let reg_to_var_map = Hashtbl.create num_regs
  (* A queue to track the usage of registers for the LRU policy.
     The head of the list is the least recently used. *)
  let lru_queue = ref []

  (* Resets the state of the allocator. Called at the start of each basic block. *)
  let reset () =
    Hashtbl.clear var_to_reg_map;
    Hashtbl.clear reg_to_var_map;
    lru_queue := []

  (* Marks a register as "used", moving it to the end of the LRU queue. *)
  let touch_reg reg =
    lru_queue := List.filter (fun r -> r <> reg) !lru_queue @ [ reg ]

  (* Spills the least recently used register and returns the spill code and the freed register name *)
  let spill_lru get_stack_offset =
    match !lru_queue with
    | [] -> failwith "No registers to spill"
    | lru_reg :: rest ->
        let var_to_spill = Hashtbl.find reg_to_var_map lru_reg in
        let offset = get_stack_offset var_to_spill in
        let spill_code = Printf.sprintf "\tsw %s, %d(sp)\n" lru_reg offset in
        Hashtbl.remove var_to_reg_map var_to_spill;
        Hashtbl.remove reg_to_var_map lru_reg;
        lru_queue := rest;
        (spill_code, lru_reg)

  (* Finds a free physical register or spills one if none are free. *)
  let find_free_reg get_stack_offset =
    match List.find_opt (fun r -> not (Hashtbl.mem reg_to_var_map r)) temp_regs with
    | Some r -> ("", r)
    | None -> spill_lru get_stack_offset

  (* Ensures a variable is in a register, loading it from the stack if necessary.
     Returns the setup code and the physical register name. *)
  let ensure_var_in_reg get_stack_offset var_name =
    if Hashtbl.mem var_to_reg_map var_name then
      let reg = Hashtbl.find var_to_reg_map var_name in
      touch_reg reg;
      ("", reg)
    else
      let offset = get_stack_offset var_name in
      let spill_code, reg = find_free_reg get_stack_offset in
      let load_code = Printf.sprintf "\tlw %s, %d(sp)\n" reg offset in
      Hashtbl.add var_to_reg_map var_name reg;
      Hashtbl.add reg_to_var_map reg var_name;
      touch_reg reg;
      (spill_code ^ load_code, reg)

  (* Allocates a register for a destination variable. *)
  let alloc_reg_for_var get_stack_offset var_name =
     if Hashtbl.mem var_to_reg_map var_name then
      let reg = Hashtbl.find var_to_reg_map var_name in
      touch_reg reg;
      ("", reg)
    else
      let spill_code, reg = find_free_reg get_stack_offset in
      Hashtbl.add var_to_reg_map var_name reg;
      Hashtbl.add reg_to_var_map reg var_name;
      touch_reg reg;
      (spill_code, reg)
      
  (* Generates code to spill all currently active registers to the stack. *)
  let spill_all_active_regs get_stack_offset =
    Hashtbl.fold (fun var reg acc ->
      let offset = get_stack_offset var in
      acc ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg offset
    ) var_to_reg_map ""
end

(* --- Main Code Generation Logic --- *)

let stack_offset = ref 0
let v_env = Hashtbl.create 1600

let get_sto var =
  try Hashtbl.find v_env var
  with Not_found -> failwith ("Unknown variable: " ^ var)

let all_st var =
  try get_sto var
  with _ ->
    stack_offset := !stack_offset + 4;
    Hashtbl.add v_env var !stack_offset;
    !stack_offset

(* Get the name of a destination operand, which must be a register or variable *)
let get_dst_name = function
  | Reg r | Var r -> r
  | _ -> failwith "Destination of instruction must be a variable or register"

(* Generate code for a single IR instruction *)
let com_inst (inst : ir_inst) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_name = get_dst_name dst in
      let code_lhs, r_lhs = Regs.ensure_var_in_reg all_st (match lhs with Reg r | Var r -> r | _ -> failwith "LHS must be a var") in
      let code_rhs, r_rhs = Regs.ensure_var_in_reg all_st (match rhs with Reg r | Var r -> r | _ -> failwith "RHS must be a var") in
      let code_dst, r_dst = Regs.alloc_reg_for_var all_st dst_name in
      
      let op_code = match op with
        | "+" -> Printf.sprintf "\tadd %s, %s, %s\n" r_dst r_lhs r_rhs
        | "-" -> Printf.sprintf "\tsub %s, %s, %s\n" r_dst r_lhs r_rhs
        | "*" -> Printf.sprintf "\tmul %s, %s, %s\n" r_dst r_lhs r_rhs
        | "/" -> Printf.sprintf "\tdiv %s, %s, %s\n" r_dst r_lhs r_rhs
        | "%" -> Printf.sprintf "\trem %s, %s, %s\n" r_dst r_lhs r_rhs
        | "==" -> Printf.sprintf "\tsub %s, %s, %s\n\tseqz %s, %s\n" r_dst r_lhs r_rhs r_dst r_dst
        | "!=" -> Printf.sprintf "\tsub %s, %s, %s\n\tsnez %s, %s\n" r_dst r_lhs r_rhs r_dst r_dst
        | "<=" -> Printf.sprintf "\tsgt %s, %s, %s\n\txori %s, %s, 1\n" r_dst r_lhs r_rhs r_dst r_dst
        | ">=" -> Printf.sprintf "\tslt %s, %s, %s\n\txori %s, %s, 1\n" r_dst r_lhs r_rhs r_dst r_dst
        | "<" -> Printf.sprintf "\tslt %s, %s, %s\n" r_dst r_lhs r_rhs
        | ">" -> Printf.sprintf "\tsgt %s, %s, %s\n" r_dst r_lhs r_rhs
        | "&&" -> Printf.sprintf "\tsnez %s, %s\n\tsnez %s, %s\n\tand %s, %s, %s\n" Regs.scratch_reg r_lhs r_dst r_rhs r_dst Regs.scratch_reg r_dst
        | "||" -> Printf.sprintf "\tor %s, %s, %s\n\tsnez %s, %s\n" r_dst r_lhs r_rhs r_dst r_dst
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      code_lhs ^ code_rhs ^ code_dst ^ op_code

  | Unop (op, dst, src) ->
      let dst_name = get_dst_name dst in
      let code_src, r_src =
        match src with
        | Imm i -> 
            let c_spill, r = Regs.find_free_reg all_st in
            (c_spill ^ Printf.sprintf "\tli %s, %d\n" r i, r)
        | Reg r | Var r -> Regs.ensure_var_in_reg all_st r
      in
      let code_dst, r_dst = Regs.alloc_reg_for_var all_st dst_name in
      let op_code =
        match op with
        | "-" -> Printf.sprintf "\tneg %s, %s\n" r_dst r_src
        | "!" -> Printf.sprintf "\tseqz %s, %s\n" r_dst r_src
        | "+" -> if r_dst <> r_src then Printf.sprintf "\tmv %s, %s\n" r_dst r_src else ""
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      code_src ^ code_dst ^ op_code
      
  | Assign (dst, src) ->
      let dst_name = get_dst_name dst in
      let code_dst, r_dst = Regs.alloc_reg_for_var all_st dst_name in
      let assign_code =
        match src with
        | Imm i -> Printf.sprintf "\tli %s, %d\n" r_dst i
        | Reg r | Var r ->
            let code_src, r_src = Regs.ensure_var_in_reg all_st r in
            code_src ^ (if r_dst <> r_src then Printf.sprintf "\tmv %s, %s\n" r_dst r_src else "")
      in
      code_dst ^ assign_code

  | Call (dst, fname, args) ->
      let spill_code = Regs.spill_all_active_regs all_st in
      Regs.reset ();

      let args_code =
        List.mapi (fun i arg ->
            let (setup_code, src_reg) = 
                match arg with
                | Imm v -> (Printf.sprintf "\tli %s, %d\n" Regs.scratch_reg v, Regs.scratch_reg)
                | Reg r | Var r ->
                    let offset = get_sto r in
                    (Printf.sprintf "\tlw %s, %d(sp)\n" Regs.scratch_reg offset, Regs.scratch_reg)
            in
            if i < 8 then
              setup_code ^ Printf.sprintf "\tmv a%d, %s\n" i src_reg
            else
              let stack_arg_offset = -1600 - (4 * (i - 8)) in
              setup_code ^ Printf.sprintf "\tsw %s, %d(sp)\n" src_reg stack_arg_offset
          ) args |> String.concat ""
      in
      let dst_name = get_dst_name dst in
      let code_dst, r_dst = Regs.alloc_reg_for_var all_st dst_name in
      let call_code = Printf.sprintf "\tcall %s\n" fname in
      let get_ret = Printf.sprintf "\tmv %s, a0\n" r_dst in
      spill_code ^ args_code ^ code_dst ^ call_code ^ get_ret

  | _ -> "nop (* unsupported inst *)\n"

(* Generate code for a basic block's terminator instruction *)
let com_terminator (term : ir_term) : string =
  let handle_ret op_opt =
    let load_code =
      match op_opt with
      | None -> ""
      | Some op ->
          match op with
          | Imm i -> Printf.sprintf "\tli a0, %d\n" i
          | Reg r | Var r ->
              let code, r_name = Regs.ensure_var_in_reg all_st r in
              code ^ Printf.sprintf "\tmv a0, %s\n" r_name
    in
    let ra_offset = get_sto "ra" in
    load_code ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 800\n\taddi sp,sp,800\n\tret\n" ra_offset
  in
  let spill_code = Regs.spill_all_active_regs all_st in
  match term with
  | TermGoto label -> spill_code ^ Printf.sprintf "\tj %s\n" label
  | TermIf (cond, l_true, l_false) ->
      let cond_code, r_cond =
        match cond with
        | Imm i -> Printf.sprintf "\tli %s, %d\n" Regs.scratch_reg i, Regs.scratch_reg
        | Reg r | Var r -> Regs.ensure_var_in_reg all_st r
      in
      let branch_code = Printf.sprintf "\tbne %s, x0, %s\n" r_cond l_true in
      let fall_code = Printf.sprintf "\tj %s\n" l_false in
      cond_code ^ spill_code ^ branch_code ^ fall_code
  | TermRet op -> spill_code ^ handle_ret op
  | TermSeq label -> spill_code ^ Printf.sprintf "\tj %s\n" label

(* Generate code for a single basic block *)
let com_block (blk : ir_block) : string =
  Regs.reset (); (* Start fresh for each block *)
  let label_code = Printf.sprintf "%s:\n" blk.label in
  let insts_code = blk.insts |> List.map com_inst |> String.concat "" in
  let terminator_code = com_terminator blk.terminator in
  label_code ^ insts_code ^ terminator_code

(* Generate code for an optimized function *)
let com_func_o (f : ir_func_o) : string =
  Hashtbl.clear v_env;
  stack_offset := 0;

  (* Allocate stack space for all parameters *)
  List.iter (fun name -> ignore (all_st name)) f.args;
  (* Allocate space for RA *)
  ignore (all_st "ra");

  (* Generate code to save parameters from registers/caller stack to our stack frame *)
  let pae_set =
    List.mapi (fun i name ->
        let off = get_sto name in
        if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
        else
          let caller_stack_offset = 1600 + (4 * (i - 8)) in
          Printf.sprintf "\tlw %s, %d(sp)\n\tsw %s, %d(sp)\n" Regs.scratch_reg caller_stack_offset Regs.scratch_reg off
      ) f.args
    |> String.concat ""
  in

  (* Save return address *)
  let pae_set = pae_set ^ Printf.sprintf "\tsw ra, %d(sp)\n" (get_sto "ra") in
  
  let body_code = f.blocks |> List.map com_block |> String.concat "" in
  let func_label = f.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  let epilogue = "" (* Epilogue is now handled by Ret terminators *) in

  prologue ^ pae_set ^ body_code ^ epilogue

(* Generate code for a whole program *)
let com_pro (prog : ir_program) : string =
  let prologue = ".text\n.global main\n" in
  let body_asm =
    match prog with
    | Ir_funcs _ -> failwith "Register allocation only supported for optimized IR (Ir_funcs_o)"
    | Ir_funcs_o funcs_o -> List.map com_func_o funcs_o |> String.concat "\n"
  in
  prologue ^ body_asm