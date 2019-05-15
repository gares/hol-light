(* ========================================================================= *)
(* ML code needed for HOL-Elpi that do not depend on Elpi.                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Custom printer for hiding coercions.                                      *)
(* ------------------------------------------------------------------------- *)

let hide_coercions : bool ref = ref true;;

let the_coercions : (string * (hol_type * hol_type * term)) list ref =
  ref [];;

let add_coercion tm =
  if not(is_const(tm)) then failwith "add_coercion: Not a constant" else
  let s,ty = dest_const tm in
  try let ty1,ty2 = dest_fun_ty ty in
      the_coercions := (s,(ty1,ty2,tm)) :: !the_coercions
  with Failure _ -> failwith "add_coercion: not a function";; 

let find_coercion s = assoc s !the_coercions;;

let is_coercion s = can find_coercion s;;

let print_hide_coercions fmt tm =
  if not(!hide_coercions) then fail() else
  let ftm,xtm = dest_comb tm in
  let s,ty = dest_const ftm in
  if not(is_coercion s) then failwith "print_hide_coercions" else
  pp_print_term fmt xtm;;

(* ------------------------------------------------------------------------- *)
(* Minimal set of coercions.                                                 *)
(* ------------------------------------------------------------------------- *)

add_coercion `real_of_num`;;
add_coercion `int_of_num`;;

(* ------------------------------------------------------------------------- *)
(* Install the parser.                                                       *)
(* ------------------------------------------------------------------------- *)

install_user_printer("hide_coercions",print_hide_coercions);;

(* ------------------------------------------------------------------------- *)
(* Some tests.                                                               *)
(* ------------------------------------------------------------------------- *)

(*
print_hide_coercions std_formatter `&0`;;

delete_user_printer "hide_coercions";;

try_user_printer std_formatter `&0`;;

`&0`;;
*)
