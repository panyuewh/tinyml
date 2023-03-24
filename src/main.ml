open Ast
open Llvm
open Llprint

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

(** Helper function for llvm. *)
let add_target_triple triple llm =
  Llvm_X86.initialize ();
  let lltarget  = Llvm_target.Target.by_triple triple in
  let llmachine = Llvm_target.TargetMachine.create ~triple:triple lltarget in
  let lldly     = Llvm_target.TargetMachine.data_layout llmachine in

  set_target_triple (Llvm_target.TargetMachine.triple llmachine) llm ;
  set_data_layout (Llvm_target.DataLayout.as_string lldly) llm ;
  (* Printf.printf "lltarget: %s\n" (Llvm_target.Target.name lltarget); *)
  (* Printf.printf "llmachine: %s\n" (Llvm_target.TargetMachine.triple llmachine); *)
  (* Printf.printf "lldly: %s\n" (Llvm_target.DataLayout.as_string lldly) ; *)
  ()

let ctx = global_context () 
let i32_t = i32_type ctx 
let i1_t = i1_type ctx 
let true_v = const_int i1_t 1
let false_v = const_int i1_t 0 

let builder = builder ctx

(** [Env] is module to help with environments, which 
    are maps that have strings as keys. *)
module Env = Map.Make(String)

(** [llenv] is the type of an environment, which maps
    a string to a llvalue. *)
type llenv = llvalue Env.t

(** The error message produced if a variable is unbound. *)
let unbound_var_err = "Unbound variable"

(** The error message produced if binary operators and their
    operands do not have the correct types. *)
let bop_err = "Operator and operand type mismatch"

(** The error message produced if the [then] and [else] branches
    of an [if] do not have the same type. *)
let if_branch_err = "Branches of if must have same type"

(** The error message produced if the guard
    of an [if] does not have type [bool]. *)
let if_guard_err = "Guard of if must have type bool"

(** The error message produced if the guard
    of an [app] does not have type [Closure]. *)
let app_guard_err = "Guard of app must have type closure"

(** The error message produced if the guard
    of an [fst], [snd] does not have type [Pair]. *)
let pair_guard_err = "Guard of fst, snd must have type pair"

(** The error message produced if the guard
    of an [match] does not have type [Left] or [Right]. *)
let match_guard_err = "Guard of match must have type Left or Right"

(** The error message produced if the guard
    of an [app] is not found in [env]. *)
let func_not_found_err = "Function is not found"

(** The error message produced if the guard
    of an [var] does not have type [pointer] or [integer]. *)
let var_not_support_err = "Var types other than pointer or integer are not supported"

(** The error message produced if the guard
    of an [var] of [pointer] doesnot have element type [function] or [integer]. *)
let pointer_not_support_err = "Pointer element types other than function or integer are not supported"

type scope_rule = Lexical | Dynamic
let scope = Lexical

(** [eval env e] is the [<env, e> ==> v] relation. *)
let rec codegen_expr builder (env: llenv) = function
  | Int i -> print_string "Int "; print_endline (string_of_int i); const_int i32_t i
  | Bool b -> print_string "Bool "; print_endline (string_of_bool b); if b then true_v else false_v
  | Var x -> print_string "Var "; print_endline x; codegen_var builder env x
  | App (e1, e2) -> print_endline "App"; codegen_app builder env e1 e2
  | Fun (x, t, e) -> print_string "Fun "; print_endline x; codegen_fun builder env x t e
  | Binop (bop, e1, e2) -> print_endline "Binop"; codegen_bop builder env bop e1 e2
  | If (e1, e2, e3) -> codegen_if builder env e1 e2 e3
  | Let (x, e1, e2) -> print_string "Let "; print_endline x; codegen_let builder env x e1 e2

(** [eval_var env x] is the [v] such that [<env, x> ==> v]. *)
and codegen_var builder env x = 
  let v = match Env.find_opt x env with
    | None -> failwith unbound_var_err
    (* Load the value *)
    | Some vx -> print_val vx; print_endline ""; let ty = type_of vx in   
        (match classify_type ty with 
          | TypeKind.Pointer -> (match classify_type (element_type ty) with 
              | TypeKind.Function -> vx
              | TypeKind.Integer -> build_load vx x builder 
              | _ -> failwith pointer_not_support_err)
          | TypeKind.Integer -> vx
          | _ -> failwith var_not_support_err) in
  v

(** [eval_app env e1 e2] is the [v] such that [<env, e1 e2> ==> v]. *)
and codegen_app builder env e1 e2 = 
  let mdl = global_parent (block_parent (insertion_block builder)) in
  let v2 = codegen_expr builder env e2 in 
  (* let base_env_for_body = 
    match scope with
    | Lexical -> defenv
    | Dynamic -> env in
  let env_for_body = Env.add x v2 base_env_for_body in *)
  let fun_name = codegen_expr builder env e1 in 
  match lookup_function (value_name fun_name) mdl with
  | None -> failwith func_not_found_err 
  | Some callee -> build_call callee [|v2|] "calltmp" builder

(** [eval_fun env x t e] is the [v] such that [<env, x t e> ==> v]. *)
and codegen_fun builder env x t e = 
  let mdl = global_parent (block_parent (insertion_block builder)) in
  let inty = match t with
  | "bool" -> i1_t 
  | "int" | _ -> i32_t in
  (* Firstly, use an temporal function to find the return type *)
  let ft_temp = function_type i32_t [|inty|] in
  let fn_temp = define_function "lambda_temp" ft_temp mdl in
  (* Create a new basic block to start insertion into. *)
  let bb_temp = entry_block fn_temp in
  position_at_end bb_temp builder ;
  (* Add all arguments to the symbol table and create their allocas. *)
  let env'_temp = Env.add x (params fn_temp).(0) env in 
  (* Get the return type. *)
  let return_val = codegen_expr builder env'_temp e in
  let outty = type_of return_val in
  (* As the return type is known, the temporal function is deleted*)
  remove_block bb_temp;
  delete_function fn_temp;
  (* Secondly, define and implement the final function*)
  let ft = function_type outty [|inty|] in
  let fn = define_function "lambda" ft mdl in
  let bb = entry_block fn in
  position_at_end bb builder ;
  (* Add all arguments to the symbol table and create their allocas. *)
  let env' = Env.add x (params fn).(0) env in 
  (* Finish off the function. *)
  let return_val = codegen_expr builder env' e in
  build_ret return_val builder |> ignore;
  print_val return_val;
  (* Validate the generated code, checking for consistency. *)
  ( match Llvm_analysis.verify_function fn with
    | true -> ()
    | false ->
      Printf.printf "invalid function generated\n%s\n"
        (string_of_llvalue fn) ;
      Llvm_analysis.assert_valid_function fn ) ;
  fn

(** [eval_bop env bop e1 e2] is the [v] such that 
    [<env, e1 bop e2> ==> v]*)
and codegen_bop builder env bop e1 e2 =
  let e1_val = codegen_expr builder env e1 in 
  let e2_val = codegen_expr builder env e2 in
  match bop with
  | Add-> build_add e1_val e2_val "addtmp" builder
  | Mult -> build_mul e1_val e2_val "multmp" builder
  | Leq -> build_icmp Icmp.Sle e1_val e2_val "cmptmp" builder

(** [eval_if env e1 e2 e3] is the [v] such that
    [<env, if e1 then e2 else e3> ==> v]. *)
and codegen_if builder env e1 e2 e3 = 
  let ctx = module_context (global_parent (block_parent (insertion_block builder))) in
  let cond = codegen_expr builder env e1 in
  (* Convert condition to a bool by comparing equal to 0.0 *)
  let cond_val = build_icmp Icmp.Eq cond true_v "ifcond" builder in
  (* Grab the first block so that we might later add the conditional branch
  * to it at the end of the function. *)
  let start_bb = insertion_block builder in
  let the_function = block_parent start_bb in
  let then_bb = append_block ctx "then" the_function in
  (* Emit 'then' value. *)
  position_at_end then_bb builder ;
  let then_val = codegen_expr builder env e2 in
  (* Codegen of 'then' can change the current block, update then_bb for the
  * phi. We create a new name because one is used for the phi node, and the
  * other is used for the conditional branch. *)
  let new_then_bb = insertion_block builder in
  (* Emit 'else' value. *)
  let else_bb = append_block ctx "else" the_function in
  position_at_end else_bb builder ;
  let else_val = codegen_expr builder env e3 in
  (* Codegen of 'else' can change the current block, update else_bb for the
  * phi. *)
  let new_else_bb = insertion_block builder in
  (* Emit merge block. *)
  let merge_bb = append_block ctx "ifcont" the_function in
  position_at_end merge_bb builder ;
  let incoming = [(then_val, new_then_bb); (else_val, new_else_bb)] in
  let phi = build_phi incoming "iftmp" builder in
  (* Return to the start block to add the conditional branch. *)
  position_at_end start_bb builder ;
  build_cond_br cond_val then_bb else_bb builder |> ignore ;
  (* Set a unconditional branch at the end of the 'then' block and the
  * 'else' block to the 'merge' block. *)
  position_at_end new_then_bb builder ;
  build_br merge_bb builder |> ignore ;
  position_at_end new_else_bb builder ;
  build_br merge_bb builder |> ignore ;
  (* Finally, set the builder to the end of the merge block. *)
  position_at_end merge_bb builder ;
  phi

(** [eval_let env x e1 e2] is the [v] such that
    [<env, let x = e1 in e2> ==> v]. *)
and codegen_let builder env x e1 e2 =
  (* keep the position*)
  let bb = insertion_block builder in
  (* evaluate e1 firstly*)
  let v1 = codegen_expr builder env e1 in 
  (* restore position in case v1 is a function*)
  position_at_end bb builder ;
  let vx = match classify_type (element_type (type_of v1)) with 
      | TypeKind.Function -> v1
      | _ ->  
          let alloca = build_alloca (type_of v1) x builder in
          build_store v1 alloca builder |> ignore;
          alloca
    in
  (* print_val vx; *)
  (* evaluate e2 secondly in the new environment combined with x*)
  let env' = Env.add x vx env in 
  codegen_expr builder env' e2 

(** [interp s] interprets [s] by parsing
    and evaluating it with the big-step model,
    starting with the empty environment. *)
let compile builder (s : string) : llvalue =
  s |> parse |> codegen_expr builder Env.empty

let initialize_module = fun () ->
  let mdl = create_module ctx "tinyml" in
  add_target_triple "x86_64" mdl |> ignore;
  let fty = function_type i32_t [| |] in
  let f = define_function "main" fty mdl in 
  position_at_end (entry_block f) builder; 
  mdl

let codegen ?(fname="") s  = 
  let mdl = initialize_module () in 
  let ret = compile builder s in
  let printf_ty = var_arg_function_type i32_t [| pointer_type (i8_type ctx) |] in
  let printf = declare_function "printf" printf_ty mdl in
   let nounwind = attr_of_repr ctx (AttrRepr.Enum ((enum_attr_kind "nounwind"), 0L)) in  
  let nocapture = attr_of_repr ctx (AttrRepr.Enum ((enum_attr_kind "nocapture"), 0L)) in  
  add_function_attr printf nounwind AttrIndex.Function;
  add_function_attr printf nocapture (AttrIndex.Param 0);
  let tmpl = build_global_stringptr "=%d\n" "" builder in
  (* try commenting these two lines and compare the result *)
  (* let zero = const_int i32_t 0 in *)
  (* let tmpl = build_in_bounds_gep tmpl [| zero |] "" builder in *)
  let _ = build_call printf [| tmpl; ret |] "" builder in
  build_ret (const_int i32_t 0) builder |> ignore;
  if (String.length fname) = 0 
  then (print_endline ""; dump_module mdl)
  else print_module fname mdl |> ignore; 
  dispose_module mdl;
  ()

let interp (s: string) = 
  let mdl = initialize_module () in 
  let res = compile builder s in
  build_ret res builder |> ignore;
  let exec_eng =
    ( match Llvm_executionengine.initialize () with
    | true -> ()
    | false -> failwith "failed to initialize") ;
    Llvm_executionengine.create mdl in
  Llvm_executionengine.add_module mdl exec_eng ;
  print_endline ""; dump_module mdl;
  let fp =
    Llvm_executionengine.get_function_address "main"
      (Foreign.funptr Ctypes.(void @-> returning int))
      exec_eng
  in
  let ret = fp () in
  Llvm_executionengine.remove_module mdl exec_eng;
  Llvm_executionengine.dispose exec_eng;
  dispose_module mdl;
  ret
