(* ========================================================================= *)
(* Framework for tracing parsed terms.                                       *)
(* ========================================================================= *)

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