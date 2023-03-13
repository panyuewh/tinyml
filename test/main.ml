open OUnit2
open Interp
open Ast
open Main

let code_part = function
  | Closure (x, e, _) -> Fun (x, e)
  | VInt i -> Int i
  | VBool b -> Bool b

(** [make n s1 s2] makes an OUnit test named [n] that expects
    [s2] to evalute to [s1]. *)
let make n s1 s2 =
  n >:: (fun _ -> assert_equal (parse s1) (s2 |> interp |> code_part))

(** [make_i n i s] makes an OUnit test named [n] that expects
    [s] to evalute to [Int i]. *)
let make_i n i s =
  n >:: (fun _ -> assert_equal (VInt i) (interp s))

(** [make_b n b s] makes an OUnit test named [n] that expects
    [s] to evalute to [Bool b]. *)
let make_b n b s =
  n >:: (fun _ -> assert_equal (VBool b) (interp s))

(** [make_t n s] makes an OUnit test named [n] that expects
    [s] to fail type checking with error string [s']. *)
let make_t n s' s =
  n >:: (fun _ -> assert_raises (Failure s') (fun () -> interp s))

(** [make_unbound_err n s] makes an OUnit test named [n] that
    expects [s] to produce an unbound variable error. *)
(* let make_unbound_err n s =
  n >:: (fun _ -> assert_raises (Failure unbound_var_err) (fun () -> interp s)) *)

(** This test suite is imperfect in that it only checks the code
    part of closures, not the environment part, for correctness. *)
let tests = [
  make "reduce correct"
    "fun y -> y"
    "(fun x -> x) (fun y -> y)";
  make "scope correct" (* lexical scope *)
    "(fun b -> b)"
    (* this is the example from the notes, but with
       - [fun a -> a] in place of [0]
       - [fun b -> b] in place of [1],
       - [fun c -> c] in place of [2];
       and with the [let] expressions desugared to functions. *)
    "(fun x -> \
     (fun f -> \
     (fun x -> \
     f (fun a -> a)) \
     (fun c -> c)) \
     (fun y -> x)) \
     (fun b -> b)";
  make_i "int" 22 "22";
  make_i "add" 22 "11+11";
  make_i "adds" 22 "(10+1)+(5+6)";
  make_i "let" 22 "let x=22 in x";
  make_i "lets" 22 "let x = 0 in let x = 22 in x";
  make_i "mul1" 22 "2*11";
  make_i "mul2" 22 "2+2*10";
  make_i "mul3" 14 "2*2+10";
  make_i "mul4" 40 "2*2*10";
  make_i "if1" 22 "if true then 22 else 0";
  make_b "true" true "true";
  make_b "leq" true "1<=1";
  make_i "if2" 22 "if 1+2 <= 3+4 then 22 else 0";
  make_i "if3" 22 "if 1+2 <= 3*4 then let x = 22 in x else 0";
  make_i "letif" 22 "let x = 1+2 <= 3*4 in if x then 22 else 0";
  make_t "ty plus" bop_err "1 + true";
  make_t "ty mult" bop_err "1 * false";
  make_t "ty leq" bop_err "true <= 1";
  make_t "if guard" if_guard_err "if 1 then 2 else 3";
  (* make_t "if branch" if_branch_err "if true then 2 else false"; *)
  make_t "unbound" unbound_var_err "x";
]

let _ = run_test_tt_main ("suite" >::: tests)
