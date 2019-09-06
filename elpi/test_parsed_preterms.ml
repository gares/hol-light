(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Quick hack to compare terms upto renaming in type variables. *)
let term_eq tm1 tm2 =
  try let (e,vinst,tinst) = term_match [] tm1 tm2 in
      e = [] &&
      forall (is_var o fst) vinst &&
      forall (is_vartype o fst) tinst
  with Failure _ -> false;;

(* Variant of the above. *)
(*
let rec term_eq tm1 tm2 =
  match tm1,tm2 with
    Var(s1,_), Var(s2,_)
  | Const(s1,_), Const(s2,_) -> s1 = s2
  | Comb(f1,x1), Comb(f2,x2) -> term_eq f1 f2 && term_eq x1 x2
  | Abs(Var(s1,_),b1), Abs(Var(s2,_),b2) -> s1 = s2 && term_eq b1 b2
  | _ -> false;;
*)

(* ------------------------------------------------------------------------- *)
(* Setup.                                                                    *)
(* ------------------------------------------------------------------------- *)

type_invention_warning := false;;
unreserve_words ["^"];; (* "^" is used for antiquotation *)

(* Load the program *)
let prg = ref (Hol_elpi.hol());;

(* Use one of the following. *)
let pterms = load_parsed_terms "elpi/CORE.bin";;
let pterms = load_parsed_terms "elpi/MULTIVARIATE.bin";;
let pterms = load_parsed_terms "elpi/COMPLEX.bin";;
let pterms = load_parsed_terms "elpi/HYPERCOMPLEX.bin";;

(* Number of terms. *)
length pterms;;

(* ------------------------------------------------------------------------- *)
(* Example tests.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Returns true only if Noparse is raised. *)
let term_noparse (s,ptm,tm,st) =
  let p = parse_preterm o lex o explode in
  try set_hol_status st;
      ignore(p s);
      false
  with Failure _ -> false
     | Noparse -> true;;

let ko_terms = filter_progress term_noparse pterms;;
length ko_terms;;

let elaborate (ptm : preterm) : term =
  let ptm = Hol_elpi.elaborate_preterm_with !prg ptm in
  term_of_preterm ptm;;

(* Returns true if the elaborator fails (including GABS). *)
let term_noelab (_,ptm,tm,st) =
  set_hol_status st;
  not (can elaborate ptm);;

(* Same as above, excluding GABS. *)
let term_noelab (_,ptm,tm,st) =
  if contains_gabs tm then false else
  begin
    set_hol_status st;
    not (can elaborate ptm)
  end;;

let ko_terms = filter_progress term_noelab pterms;;
length ko_terms;;
(* Run 2019-08-30: All terms in CORE pass this test with elaborate. *)
(* Run 2019-08-22: All terms without GABS in CORE pass this test with elab. *)

(* Returns true if the elaborator returns a different term. *)
(* NB2: (Also return true if the elaborator fails.) *)
let term_elab_neq (_,ptm,tm,st) =
  set_hol_status st;
  try let qtm = elaborate ptm in
      not (term_eq tm qtm)
  with Failure _ -> true;;

(* Same as above, excluding GABS. *)
let term_elab_neq (_,ptm,tm,st) =
  if contains_gabs tm then false else
  begin
    set_hol_status st;
    try let qtm = Hol_elpi.elaborate ptm in
        not (term_eq tm qtm)
    with Failure _ -> true
  end;;

let ko_terms = filter_progress term_elab_neq pterms;;
length ko_terms;;

(* ------------------------------------------------------------------------- *)
(*                HIC SUNT LEONES!!!                                         *)
(* ------------------------------------------------------------------------- *)

(* Useful snippets. *)
prg := Hol_elpi.hol();;

!Hol_elpi.elab_predicate;;
Hol_elpi.elab_predicate := "elab";;
Hol_elpi.elab_predicate := "elaborate";;

length pterms;;

length ko_terms;;

let ko_terms = filter_progress term_noelab (take 200 pterms);;

map (fun str,ptm,tm,st -> tm) ko_terms;;

let ko_terms2 = filter_progress term_noelab ko_terms;;
length ko_terms2;;

let str,ptm,tm,st = hd (ko_terms);;
set_hol_status st;;
let ptm' = Hol_elpi.elaborate_preterm ptm;;
let tm' = term_of_preterm ptm';;


Hol_elpi.elaborate_preterm ptm;;
(Hol_elpi.elaborate_preterm o fst o parse_preterm o lex o explode) "coprime";;

filter_progress
    (fun (_,_,tm,_,_,_) ->
        not(exists (fun c -> name_of c = "GABS") (term_constants tm)))
    ko_terms;;

let parsing_fail s =
  try [] != (parse_preterm o lex o explode) s
  with Failure _ -> false
     | Noparse -> true;;

let ptm = parse_term "{x | P x}";;
let qtm = Hol_elpi.quotation "{x | P x}";;

term_eq ptm qtm;;
