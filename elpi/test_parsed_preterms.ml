loads "elpi/test_elaborator.ml";;

(* ------------------------------------------------------------------------- *)
(* Setup.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Use one of the following. *)
let pterms = load_parsed_terms "elpi/CORE.bin";;
let pterms = load_parsed_terms "elpi/MULTIVARIATE.bin";;
let pterms = load_parsed_terms "elpi/COMPLEX.bin";;
let pterms = load_parsed_terms "elpi/HYPERCOMPLEX.bin";;

(* Number of terms. *)
length pterms;;

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

map (fun str,ptm,tm,st -> tm) ko_terms;;

let ko_terms2 = filter_progress term_noelab ko_terms;;
length ko_terms2;;

let str,ptm,tm,st = hd ko_terms;;
tm;;
report str;;
set_hol_status st;;
let ptm' = Hol_elpi.elaborate_preterm_with !prg ptm;;
let tm' = term_of_preterm ptm';;
term_eq tm tm';;



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

let ptm1 = (fst o parse_preterm o lex o explode) "IN m {m:num | m | < m n}";;
(* let ptm1 = (fst o parse_preterm o lex o explode) "{m:num | m | < m n}";; *)
let tm1 = term_of_preterm (retypecheck [] ptm1);;
(map dest_var o variables) tm1;;
let ptm1' = Hol_elpi.elaborate_preterm_with !prg ptm1;;
let tm1' = term_of_preterm ptm1';;
(map dest_var o variables) tm1';;
term_eq tm1 tm1';;
