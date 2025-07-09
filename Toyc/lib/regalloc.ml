(* 寄存器分配模块 *)

(* 寄存器信息 *)
type reg_info = {
  name: string;         (* 寄存器名称，如 "t0", "a0" *)
  allocated: bool ref;  (* 是否已分配 *)
  mutable var_name: string option; (* 当前保存的变量名，None表示未使用 *)
}

(* RISC-V寄存器集合 *)
let available_regs = [
  (* 临时寄存器 *)
  { name = "t0"; allocated = ref false; var_name = None };
  { name = "t1"; allocated = ref false; var_name = None };
  { name = "t2"; allocated = ref false; var_name = None };
  { name = "t3"; allocated = ref false; var_name = None };
  { name = "t4"; allocated = ref false; var_name = None };
  { name = "t5"; allocated = ref false; var_name = None };
  { name = "t6"; allocated = ref false; var_name = None };
  
  (* 参数寄存器，可用于临时计算 *)
  { name = "a0"; allocated = ref false; var_name = None };
  { name = "a1"; allocated = ref false; var_name = None };
  { name = "a2"; allocated = ref false; var_name = None };
  { name = "a3"; allocated = ref false; var_name = None };
  { name = "a4"; allocated = ref false; var_name = None };
  { name = "a5"; allocated = ref false; var_name = None };
  { name = "a6"; allocated = ref false; var_name = None };
  { name = "a7"; allocated = ref false; var_name = None };
]

(* 变量到寄存器的映射表 *)
let var_to_reg = Hashtbl.create 100

(* 分配寄存器 *)
let allocate_register var =
  try
    (* 检查变量是否已经分配了寄存器 *)
    Some (Hashtbl.find var_to_reg var)
  with Not_found ->
    (* 尝试分配一个未使用的寄存器 *)
    let rec find_free regs =
      match regs with
      | [] -> None (* 没有空闲寄存器 *)
      | reg :: rest ->
          if not !(reg.allocated) then (
            reg.allocated := true;
            reg.var_name <- Some var;
            Hashtbl.add var_to_reg var reg;
            Some reg
          ) else
            find_free rest
    in
    find_free available_regs

(* 释放寄存器 *)
let free_register reg =
  reg.allocated := false;
  match reg.var_name with
  | Some var -> Hashtbl.remove var_to_reg var; reg.var_name <- None
  | None -> ()

(* 释放所有寄存器 *)
let free_all_registers () =
  List.iter (fun reg -> 
    reg.allocated := false;
    match reg.var_name with
    | Some var -> Hashtbl.remove var_to_reg var; reg.var_name <- None
    | None -> ()
  ) available_regs;
  Hashtbl.clear var_to_reg

(* 获取变量的寄存器，如果已分配 *)
let get_register var =
  try
    Some (Hashtbl.find var_to_reg var)
  with Not_found ->
    None

(* 溢出寄存器到栈上 *)
let spill_register reg _var stack_offset =
  Printf.sprintf "\tsw %s, %d(sp)\n" reg.name stack_offset

(* 从栈加载变量到寄存器 *)
let load_from_stack reg _var stack_offset =
  Printf.sprintf "\tlw %s, %d(sp)\n" reg.name stack_offset

(* 选择一个寄存器进行溢出 *)
let select_register_to_spill () =
  (* 简单策略：选择第一个已分配的寄存器 *)
  let rec find_allocated regs =
    match regs with
    | [] -> None
    | reg :: rest ->
        if !(reg.allocated) then Some reg
        else find_allocated rest
  in
  find_allocated available_regs
