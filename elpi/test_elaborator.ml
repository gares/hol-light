(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

needs "elpi/make.ml";;

unset_jrh_lexer;;

(* Quick hack to compare terms upto renaming in type variables. *)
let term_eq tm1 tm2 =
  try let (e,vinst,tinst) = term_match [] tm1 tm2 in
      e = [] &&
      forall (is_var o fst) vinst &&
      forall (is_vartype o fst) tinst
  with Failure _ -> false;;

type_invention_warning := false;;
unreserve_words ["^"];; (* "^" is used for antiquotation *)

(* Load the program *)
let prg = ref (Hol_elpi.hol());;

(* Run the query. *)
let elaborate (ptm : preterm) : term =
  let ptm = Hol_elpi.elaborate_preterm_with !prg ptm in
  term_of_preterm ptm;;

type elaboration_comparison =
  | ElabSame of string * Hol.term
  | ElabDiffer of string * Hol.term * Hol.term option

let compare_elaboration (str,ptm,tm,st) =
  set_hol_status st;
  try
    let qtm = elaborate ptm in
    if term_eq tm qtm then ElabSame (str, tm)
    else ElabDiffer (str, tm, Some qtm)
  with Failure _ -> ElabDiffer (str, tm, None);;
  
(* Returns true if the elaborator fails or returns a different term. *)
  let term_elab_neq x =
    match compare_elaboration x with
    | ElabDiffer _ -> true
    | ElabSame _ -> false
;;

set_jrh_lexer;;
