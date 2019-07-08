(* ========================================================================= *)
(* ML code needed for HOL-Elpi that do not depend on Elpi.                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Custom printer for hiding coercions.                                      *)
(* ------------------------------------------------------------------------- *)

let hide_coercions : bool ref = ref true;;

let the_coercions : (string * (hol_type * term)) list ref =
  ref [];;

let add_coercion tm =
  if not(is_const(tm)) then failwith "add_coercion: Not a constant" else
  let s,ty = dest_const tm in
  if not(can dest_fun_ty ty)
  then failwith "add_coercion: not a function"
  else the_coercions := (s,(ty,tm)) :: !the_coercions;;

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

(*add_coercion `real_of_num`;;*)
add_coercion `int_of_num`;;
add_coercion `real_of_int`;;
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

(* ------------------------------------------------------------------------- *)
(* Unsafe translation from preterm to terms.  Introduces an ad hoc constant  *)
(* for "casting" a subterm as needed term.  Never fails.                     *)
(* ------------------------------------------------------------------------- *)

new_constant ("unsafe_cast", `:A -> B`);;

let unsafe_cast_tm ty ty' = mk_mconst("unsafe_cast",mk_fun_ty ty ty');;

let unsafe_mk_comb (tm1,tm2) =
  try mk_comb(tm1,tm2) with Failure _ ->
  let ty1 = type_of tm1
  and ty2 = type_of tm2 in
  try let ty2' = fst(dest_fun_ty ty1) in
      let tm2' = mk_comb(unsafe_cast_tm ty2 ty2',tm2) in
      mk_comb(tm1,tm2')
  with Failure _ ->
    let ty1' = mk_fun_ty ty2 ty1 in
    let tm1' = mk_comb(unsafe_cast_tm ty1 ty1',tm1) in
    mk_comb(tm1',tm2);;

let unsafe_term_of_preterm =
  let xty = mk_vartype "??" in
  let rec unsafe ptm =
    try term_of_preterm ptm with Failure _ ->
    match ptm with
      Varp(s,pty) | Constp(s,pty) -> mk_var(s,xty)
    | Combp(l,r) -> unsafe_mk_comb(unsafe l,unsafe r)
    | Absp(v,bod) -> mk_gabs(unsafe v,unsafe bod)
    | Typing(ptm,pty) -> unsafe ptm in
  unsafe;;
