(* ========================================================================= *)
(* Framework for tracing parsed terms.                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Usage.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* How to trace and save the parsed terms:

   1. add to hol.ml after line

        loads "parser.ml";;     (* Lexer and parser *)

      the following two lines:

        loads "elpi/trace_parsed_terms.ml";;
      trace_parsed_terms := true;; 
      
   2. add to fusion.ml inside module signature
        module type Hol_kernel =
          sig

      the following two lines:

        val the_type_constants : (string * int) list ref
        val the_term_constants : (string * hol_type) list ref
                                                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Status of the system.                                                     *)
(* ------------------------------------------------------------------------- *)

type hol_status = {
  hol_type_constants : (string * int) list;
  hol_term_constants : (string * hol_type) list;
  hol_interface      : (string * (string * hol_type)) list
};;

let get_hol_status () = {
  hol_term_constants = !the_term_constants;
  hol_type_constants = !the_type_constants;
  hol_interface      = !the_interface
};;

let set_hol_status s =
  the_type_constants := s.hol_type_constants;
  the_term_constants := s.hol_term_constants;
  the_interface      := s.hol_interface;;

(* ------------------------------------------------------------------------- *)
(* Store parsed terms.                                                       *)
(* ------------------------------------------------------------------------- *)

let trace_parsed_terms = ref false;;

(* (s, ptm, tm, ctms, itf) *)
(* s = String of the concrete representation of the term; *)
(* ptm = preterm term obtained by the HOL parser; *)
(* tm = term obtained by the HOL parser; *)
(* ctms = constants; *)
(* ctys = type constants; *)
(* ift = interface; *)
let parsed_terms :
      (string * preterm * term * hol_status) list ref =
  ref [];;

let register_parsed_term str ptm tm =
  parsed_terms :=
    (str,ptm,tm,get_hol_status()) :: !parsed_terms;;

(* ------------------------------------------------------------------------- *)
(* Variant of parse_term for tracing all terms parsed.                       *)
(* ------------------------------------------------------------------------- *)

(* Verbatim copy of parse_term from parse.ml. *)
let parse_term_notrace s =
  let ptm,l = (parse_preterm o lex o explode) s in
  if l = [] then
   (term_of_preterm o (retypecheck [])) ptm
  else failwith "Unparsed input following term";;

(* Variant of the above that also returns the associated preterm. *)
let parse_term_preterm_notrace s =
  let ptm,l = (parse_preterm o lex o explode) s in
  if l = [] then
    let tm = (term_of_preterm o (retypecheck [])) ptm in
    ptm,tm
  else failwith "Unparsed input following term";;

let parse_term_trace (s : string) : term =
  let ptm,tm = parse_term_preterm_notrace s in
  register_parsed_term s ptm tm;
  tm;;

let parse_term (s:string) : term =
  if !trace_parsed_terms
  then parse_term_trace s
  else parse_term_notrace s;;

(* ------------------------------------------------------------------------- *)
(* Marshaling and unmarshaling of parsed terms.                              *)
(* ------------------------------------------------------------------------- *)

let save_parsed_terms pathfile
      (ptml : (string * preterm * term * hol_status) list) : unit =
  let oc = open_out pathfile in
  Marshal.to_channel oc ptml [];
  close_out oc;;

let load_parsed_terms pathfile :
      (string * preterm * term * hol_status) list =
  let ic = open_in pathfile in
  Marshal.from_channel ic;;

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Take at least n element from a list. *)
let rec take n =
  function
    h :: t when n > 0 -> h :: take (n-1) t
  | _ -> [];;

(* Drop at least n element from a list. *)
let rec drop n =
  function
    h :: t when n > 0 -> drop (n-1) t
  | l -> l;;

let filter_progress : ('a -> bool) -> 'a list -> 'a list =
  let report_num n = report ("Item: "^string_of_int n) in
  let rec filt n f = function
      [] -> report ("Done: "^string_of_int n); []
    | h :: t ->
        report_num n;
        let n' = n+1 in
        if f h then h :: filt n' f t else filt n' f t in
  filt 0;;

(* Constants occuring in a term. *)
let term_constants =
  let rec consts tm =
    if is_const tm then [tm] else
    if is_var tm then [] else
    if is_abs tm then consts (body tm) else
    consts (rator tm) @ consts (rand tm) in
  fun tm -> setify (consts tm);;

(* Quick hack to compare terms upto renaming in type variables. *)
let term_eq tm1 tm2 =
  let (e,vinst,tinst) = term_match [] tm1 tm2 in
  e = [] &&
  forall (is_var o fst) vinst &&
  forall (is_vartype o fst) tinst;;

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
(* Ready to copy/paste instructions for building the traces.                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Core *)
(*
Gc.compact();;
length !parsed_terms;;
(* val it : int = 9746 *)
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;
(* val it : int = 4696 *)

let pathfile = "elpi/CORE.bin";;
save_parsed_terms pathfile !parsed_terms;;
assert (load_parsed_terms pathfile = !parsed_terms);;
*)

(* ------------------------------------------------------------------------- *)
(* Multivariate *)
(*
unreserve_words ["^"];;
parsed_terms := [];;
Gc.compact();;
time loadt "Multivariate/make.ml";;
length !parsed_terms;;
(* val it : int = 70150 *)
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;
(* val it : int = 45153 *)

let pathfile = "elpi/MULTIVARIATE.bin";;
save_parsed_terms pathfile !parsed_terms;;
*)

(* ------------------------------------------------------------------------- *)
(* Complex *)
(*
parsed_terms := [];;
Gc.compact();;
loadt "Library/binomial.ml";;
loadt "Multivariate/complexes.ml";;
loadt "Multivariate/canal.ml";;
loadt "Multivariate/transcendentals.ml";;
loadt "Multivariate/realanalysis.ml";;
loadt "Multivariate/moretop.ml";;
loadt "Multivariate/cauchy.ml";;
loadt "Multivariate/complex_database.ml";;

length !parsed_terms;;
(* val it : int = 17661 *)
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;
(* val it : int = 11852 *)

let pathfile = "elpi/COMPLEX.bin";;
save_parsed_terms pathfile !parsed_terms;;
*)

(* ------------------------------------------------------------------------- *)
(* Hypercomplex *)
(*
parsed_terms := [];;
loadt "Quaternions/make.ml";;
length !parsed_terms;;
(* val it : int = 588 *)
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;
(* val it : int = 539 *)

let pathfile = "elpi/HYPERCOMPLEX.bin";;
save_parsed_terms pathfile !parsed_terms;;
*)
