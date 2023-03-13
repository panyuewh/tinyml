open Ast

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

(** [Env] is module to help with environments, which 
    are maps that have strings as keys. *)
module Env = Map.Make(String)

(** [env] is the type of an environment, which maps
    a string to a value. *)
type env = value Env.t

(** [value] is the type of a lambda calculus value.
    In the environment model, that is a closure. *)
and value = 
  | Closure of string * expr * env
  | VInt of int
  | VBool of bool

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

type scope_rule = Lexical | Dynamic
let scope = Lexical

(** [eval env e] is the [<env, e> ==> v] relation. *)
let rec eval (env : env) (e : expr) : value = match e with
  | Int i -> VInt i 
  | Bool b -> VBool b
  | Var x -> eval_var env x
  | App (e1, e2) -> eval_app env e1 e2
  | Fun (x, e) -> Closure (x, e, env)
  | Binop (bop, e1, e2) -> eval_bop env bop e1 e2
  | If (e1, e2, e3) -> eval_if env e1 e2 e3
  | Let (x, e1, e2) -> eval_let env x e1 e2

(** [eval_var env x] is the [v] such that [<env, x> ==> v]. *)
and eval_var env x = 
  try Env.find x env 
  with Not_found -> failwith unbound_var_err

(** [eval_app env e1 e2] is the [v] such that [<env, e1 e2> ==> v]. *)
and eval_app env e1 e2 = 
  match eval env e1 with
  | Closure (x, e, defenv) -> begin
      let v2 = eval env e2 in
      let base_env_for_body = 
        match scope with
        | Lexical -> defenv
        | Dynamic -> env in
      let env_for_body = Env.add x v2 base_env_for_body in
      eval env_for_body e
    end
  | _ -> failwith app_guard_err

(** [eval_bop env bop e1 e2] is the [v] such that 
    [<env, e1 bop e2> ==> v]*)
and eval_bop env bop e1 e2 = match bop, eval env e1, eval env e2 with
  | Add, VInt a, VInt b -> VInt (a + b)
  | Mult, VInt a, VInt b -> VInt (a * b)
  | Leq, VInt a, VInt b -> VBool (a <= b)
  | _ -> failwith bop_err

(** [eval_if env e1 e2 e3] is the [v] such that
    [<env, if e1 then e2 else e3> ==> v]. *)
and eval_if env e1 e2 e3 = match eval env e1 with
  | VBool true -> eval env e2 
  | VBool false -> eval env e3 
  | _ -> failwith if_guard_err 

(** [eval_let env x e1 e2] is the [v] such that
    [<env, let x = e1 in e2> ==> v]. *)
and eval_let env x e1 e2 =
  let v1 = eval env e1 in 
  let env' = Env.add x v1 env in 
  eval env' e2 

(** [interp s] interprets [s] by parsing
    and evaluating it with the big-step model,
    starting with the empty environment. *)
let interp (s : string) : value =
  s |> parse |> eval Env.empty
