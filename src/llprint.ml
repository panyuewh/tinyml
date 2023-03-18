open Llvm

let rec print_type llty =
  let ty = classify_type llty in
  match ty with
  | TypeKind.Integer  -> Printf.printf "  integer\n"
  | TypeKind.Function -> Printf.printf "  function\n"
  | TypeKind.Array    -> Printf.printf "  array of" ; print_type (element_type llty)
  | TypeKind.Pointer  -> Printf.printf "  pointer to" ; print_type (element_type llty)
  | TypeKind.Vector   -> Printf.printf "  vector of" ; print_type (element_type llty)
  | _                      -> Printf.printf "  other type\n"

let print_val lv =
  Printf.printf "Value\n" ;
  Printf.printf "  name %s\n" (value_name lv) ;
  let llty = type_of lv in
  Printf.printf "  type %s\n" (string_of_lltype llty) ;
  print_type llty ;
  ()

let print_fun lv =
  iter_blocks
    (fun llbb ->
      Printf.printf "  bb: %s\n" (value_name (value_of_block (llbb))) ;
      iter_instrs
        (fun lli ->
          Printf.printf "    instr: %s\n" (string_of_llvalue lli)
        )
        llbb
    )
    lv
