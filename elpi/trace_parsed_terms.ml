(* ========================================================================= *)
(* Framework for tracing parsed terms.                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Usage: Add to hol.ml after line

     loads "parser.ml";;     (* Lexer and parser *)

   the following two lines:

     loads "elpi/trace_parsed_terms.ml";;
     trace_parsed_terms := true;;                                            *)
(* ------------------------------------------------------------------------- *)

let trace_parsed_terms = ref false;;

let parsed_terms :
      (string * term * (string * (string * hol_type)) list) list ref =
  ref [];;

let register_parsed_term str tm =
  parsed_terms := (str,tm,!the_interface) :: !parsed_terms;;

(* ------------------------------------------------------------------------- *)
(* Variant of parse_term for tracing all terms parsed.                       *)
(* ------------------------------------------------------------------------- *)

(* Verbatim copy of parse_term from parse.ml. *)
let parse_term_notrace s =
  let ptm,l = (parse_preterm o lex o explode) s in
  if l = [] then
   (term_of_preterm o (retypecheck [])) ptm
  else failwith "Unparsed input following term";;

let parse_term_trace (s : string) : term =
  let tm = parse_term s in
  register_parsed_term s tm;
  tm

let parse_term (s:string) : term =
  if !trace_parsed_terms
  then parse_term_trace s
  else parse_term_notrace s;;

(* ------------------------------------------------------------------------- *)
(* Marshaling and unmarshaling of parsed terms.                              *)
(* ------------------------------------------------------------------------- *)

let save_parsed_terms pathfile
      (ptml : (string * term * (string*(string*hol_type))list)list) : unit =
  let oc = open_out pathfile in
  Marshal.to_channel oc ptml [];
  close_out oc;;

let load_parsed_terms pathfile :
      (string * term * (string * (string * hol_type)) list) list =
  let ic = open_in pathfile in
  Marshal.from_channel ic;;

(*
length !parsed_terms;;
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;

let pathfile = "CORE.bin";;
save_parsed_terms pathfile !parsed_terms;;
assert (load_parsed_terms pathfile = !parsed_terms);;

time loadt "Multivariate/make.ml";;
length !parsed_terms;;
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;

let pathfile = "MULTIVARIATE.bin";;
save_parsed_terms pathfile !parsed_terms;;

loadt "Library/binomial.ml";;
loadt "Multivariate/complexes.ml";;
loadt "Multivariate/canal.ml";;
loadt "Multivariate/transcendentals.ml";;
loadt "Multivariate/realanalysis.ml";;
loadt "Multivariate/moretop.ml";;
loadt "Multivariate/cauchy.ml";;
loadt "Multivariate/complex_database.ml";;
Gc.compact();;

length !parsed_terms;;
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;

let pathfile = "COMPLEX.bin";;
save_parsed_terms pathfile !parsed_terms;;

loadt "Quaternions/make.ml";;
length !parsed_terms;;
parsed_terms := setify !parsed_terms;;
length !parsed_terms;;

let pathfile = "HYPERCOMPLEX.bin";;
save_parsed_terms pathfile !parsed_terms;;
*)

(* ------------------------------------------------------------------------- *)
(*                HIC SUNT LEONES!!!                                         *)
(* ------------------------------------------------------------------------- *)

(* Compare two terms ignoring types. *)
let rec term_eq tm1 tm2 =
  match tm1,tm2 with
    Var(s1,_), Var(s2,_)
  | Const(s1,_), Const(s2,_) -> s1 = s2
  | Comb(f1,x1), Comb(f2,x2) -> term_eq f1 f2 && term_eq x1 x2
  | Abs(Var(s1,_),b1), Abs(Var(s2,_),b2) -> s1 = s2 && term_eq b1 b2
  | _ -> false;;

let check_pterm (stm,ptm,itf) =
  try the_interface := itf;
      let qtm = Hol_elpi.quotation stm in
      term_eq ptm qtm
  with _ -> false;;

let count = ref 0;;

let bad_term x =
  report (string_of_int !count);
  incr count;
  not (check_pterm x);;

(*
type_invention_warning := false;;
let pterm_fail =
  count := 0;
  filter bad_term pterms;;
 *)

let rec take n l =
  match l with
    h :: t when n > 0 -> h :: take (n-1) t
  | _ -> [];;

(*
let bad_pterms =
  count := 0;
  filter bad_term pterms;;

let bad_pterms_400 =
  count := 0;
  filter bad_term (take 400 pterms);;

length bad_pterms_400;;
map (fun (s,_,_) -> s) bad_pterms_400;;
*)

let parsing_fail s =
  try [] != (snd o parse_preterm o lex o explode) s
  with _ -> true;;

let pterms_noparse =
  map (fun (s,_,_) -> s)
    (filter (fun (s,_,_) -> parsing_fail s)
       (take 400 pterms));;

let ptm = parse_term "{x | P x}";;
let qtm = Hol_elpi.quotation "{x | P x}";;

term_eq ptm qtm;;