(* Add to top of file *)
open Regalloc

(* Modify com_func to use register allocation *)
let com_func (f : ir_func) : string =
  (* Clear existing state *)
  Hashtbl.clear v_env;
  stack_offset := 0;
  
  (* Get register allocation information *)
  let reg_alloc = allocate_registers f in
  
  (* Build register and spill location lookup tables *)
  let reg_map = Hashtbl.create 100 in
  let spill_map = Hashtbl.create 100 in
  List.iter (fun (var, reg_opt, spill_opt) ->
    (match reg_opt with 
     | Some reg -> Hashtbl.add reg_map var reg
     | None -> ());
    (match spill_opt with
     | Some loc -> 
         let offset = 400 + (loc * 4) in (* Choose an appropriate offset scheme *)
         Hashtbl.add v_env var offset;
         Hashtbl.add spill_map var offset
     | None -> ())
  ) reg_alloc;
  
  (* Track which registers need to be saved/restored *)
  let used_callee_saved = Hashtbl.create 16 in
  Hashtbl.iter (fun _ reg ->
    if List.mem reg callee_saved then
      Hashtbl.replace used_callee_saved reg ()
  ) reg_map;
  
  (* Process arguments - map them to a0-a7 or spill locations *)
  List.iteri (fun i name ->
    if i < 8 then begin
      (* Function arguments are in a0-a7 *)
      let arg_reg = Printf.sprintf "a%d" i in
      if Hashtbl.mem reg_map name then begin
        let assigned_reg = Hashtbl.find reg_map name in
        if assigned_reg <> arg_reg then
          (* Need to move from arg reg to assigned reg *)
          Printf.sprintf "\tmv %s, %s\n" assigned_reg arg_reg
        else ""
      end else if Hashtbl.mem spill_map name then begin
        (* Spill argument to stack *)
        let offset = Hashtbl.find spill_map name in
        Printf.sprintf "\tsw a%d, %d(sp)\n" i offset
      end else begin
        (* Default case - just spill *)
        stack_offset := !stack_offset + 4;
        Hashtbl.add v_env name !stack_offset;
        Printf.sprintf "\tsw a%d, %d(sp)\n" i !stack_offset
      end
    end else begin
      (* Arguments beyond 8 are already on stack *)
      if not (Hashtbl.mem reg_map name) && not (Hashtbl.mem spill_map name) then begin
        stack_offset := !stack_offset + 4;
        Hashtbl.add v_env name !stack_offset;
      end
    end
  ) f.args;
  
  (* Save ra *)
  stack_offset := !stack_offset + 4;
  Hashtbl.add v_env "ra" !stack_offset;
  let ra_save = Printf.sprintf "\tsw ra, %d(sp)\n" !stack_offset in
  
  (* Save used callee-saved registers *)
  let callee_saves = 
    Hashtbl.fold (fun reg _ acc ->
      stack_offset := !stack_offset + 4;
      let offset = !stack_offset in
      Printf.sprintf "\tsw %s, %d(sp)\n" reg offset ^ acc
    ) used_callee_saved ""
  in
  
  (* Modified operand handling functions *)
  let get_operand_reg op =
    match op with
    | Reg r | Var r -> 
        (try Hashtbl.find reg_map r 
         with Not_found -> "t0") (* Default temp if no reg assigned *)
    | Imm _ -> "t0" (* Immediates loaded into t0 *)
  in
  
  let load_operand dst_reg op =
    match op with
    | Imm i -> Printf.sprintf "\tli %s, %d\n" dst_reg i
    | Reg r | Var r ->
        if Hashtbl.mem reg_map r then
          let src_reg = Hashtbl.find reg_map r in
          if src_reg = dst_reg then ""
          else Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
        else
          let offset = 
            try Hashtbl.find v_env r
            with Not_found -> failwith ("Unknown variable: " ^ r)
          in
          Printf.sprintf "\tlw %s, %d(sp)\n" dst_reg offset
  in
  
  let store_to_var var src_reg =
    if Hashtbl.mem reg_map var then
      let dst_reg = Hashtbl.find reg_map var in
      if dst_reg = src_reg then ""
      else Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg
    else
      let offset = 
        try Hashtbl.find v_env var
        with Not_found -> failwith ("Unknown variable: " ^ var)
      in
      Printf.sprintf "\tsw %s, %d(sp)\n" src_reg offset
  in
  
  (* Generate code for each instruction *)
  let gen_inst inst =
    match inst with
    | Binop (op, dst, lhs, rhs) ->
        let dst_var = match dst with Reg r | Var r -> r | _ -> failwith "Bad dst" in
        let dst_reg = get_operand_reg dst in
        let lhs_code = load_operand "t1" lhs in
        let rhs_code = load_operand "t2" rhs in
        
        let op_code =
          match op with
          | "+" -> Printf.sprintf "\tadd %s, t1, t2\n" dst_reg
          | "-" -> Printf.sprintf "\tsub %s, t1, t2\n" dst_reg
          | "*" -> Printf.sprintf "\tmul %s, t1, t2\n" dst_reg
          | "/" -> Printf.sprintf "\tdiv %s, t1, t2\n" dst_reg
          | "%" -> Printf.sprintf "\trem %s, t1, t2\n" dst_reg
          | "==" -> Printf.sprintf "\tsub %s, t1, t2\n\tseqz %s, %s\n" dst_reg dst_reg dst_reg
          | "!=" -> Printf.sprintf "\tsub %s, t1, t2\n\tsnez %s, %s\n" dst_reg dst_reg dst_reg
          | "<=" -> Printf.sprintf "\tsgt %s, t1, t2\n\txori %s, %s, 1\n" dst_reg dst_reg dst_reg
          | ">=" -> Printf.sprintf "\tslt %s, t1, t2\n\txori %s, %s, 1\n" dst_reg dst_reg dst_reg
          | "<" -> Printf.sprintf "\tslt %s, t1, t2\n" dst_reg
          | ">" -> Printf.sprintf "\tsgt %s, t1, t2\n" dst_reg
          | "&&" -> Printf.sprintf "\tand %s, t1, t2\n" dst_reg
          | "||" -> Printf.sprintf "\tor %s, t1, t2\n" dst_reg
          | _ -> failwith ("Unknown binop: " ^ op)
        in
        
        (* For spilled variables, we need to store the result back to memory *)
        let store_code = 
          if not (Hashtbl.mem reg_map dst_var) then
            let offset = try Hashtbl.find v_env dst_var
                         with Not_found -> failwith ("Unknown variable: " ^ dst_var) in
            Printf.sprintf "\tsw %s, %d(sp)\n" dst_reg offset
          else ""
        in
        
        lhs_code ^ rhs_code ^ op_code ^ store_code
        
    (* Similar modifications for other instruction types... *)
    (* For brevity, I'll skip the rest of the instruction handlers, but they would follow the same pattern *)
    
    | _ -> com_inst inst  (* Fall back to original implementation for other instructions *)
  in
  
  let body_code = f.body |> List.map gen_inst |> String.concat "" in
  
  (* Generate function epilogue - restore saved registers *)
  let restore_code =
    let ra_restore = Printf.sprintf "\tlw ra, %d(sp)\n" (Hashtbl.find v_env "ra") in
    let callee_restores = 
      Hashtbl.fold (fun reg _ acc ->
        let offset = try Hashtbl.find v_env reg with Not_found -> failwith "Register not saved" in
        Printf.sprintf "\tlw %s, %d(sp)\n" reg offset ^ acc
      ) used_callee_saved ""
    in
    ra_restore ^ callee_restores ^ "\taddi sp, sp, 1600\n\tret\n"
  in
  
  (* Check if function ends with return *)
  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code ^ restore_code
    else body_code
  in
  
  (* Generate function prologue *)
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" f.name in
  prologue ^ ra_save ^ callee_saves ^ body_code