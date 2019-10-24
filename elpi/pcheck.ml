needs "tactics.ml";;

(* ------------------------------------------------------------------------- *)
(* TODO: I the first argument of "Pimp_r of  preterm * proof" needed?        *)
(* ------------------------------------------------------------------------- *)

type ('individual,'formula) proof =
   | Pand_l    of  'formula * 'formula * ('individual,'formula) proof
   | Pand_r    of  ('individual,'formula) proof * ('individual,'formula) proof
   | Por_l     of  'formula * 'formula * ('individual,'formula) proof * ('individual,'formula) proof
   | Por1_r    of  ('individual,'formula) proof
   | Por2_r    of  ('individual,'formula) proof
   | Porc_r    of  ('individual,'formula) proof
   | Pex_falso
   | Pinitial  of  'formula
   | Pimp_l    of  'formula * 'formula * ('individual,'formula) proof * ('individual,'formula) proof
   | Pimp_r    of   ('individual,'formula) proof
   | Pforall_l of  'individual * 'formula * ('individual,'formula) proof
   | Pforall_r of  'individual * 'formula * ('individual,'formula) proof
   | Pexists_l of  'individual * 'formula * ('individual,'formula) proof
   | Pexists_r of  'individual * ('individual,'formula) proof
   | Pall;;
let pcheck x = assert false (*
let rec pcheck = function
  | Pinitial a -> (*
      ACCEPT_TAC (ASSUME (term_of_preterm a))*) assert false
  | Pand_l(a,b,p') -> (*
      CONJUNCTS_THEN ASSUME_TAC
        (ASSUME (mk_conj (term_of_preterm a, term_of_preterm b))) THEN
      pcheck p'*) assert false
  | Pand_r(p,q) ->
      CONJ_TAC THENL [pcheck p; pcheck q]
  | Pimp_r(p) ->
      DISCH_TAC THEN pcheck p
  | Por1_r(p) ->
      DISJ1_TAC THEN pcheck p
  | Por2_r(p) ->
      DISJ2_TAC THEN pcheck p
  | Por_l(a,b,p,q) ->
      let tma = term_of_preterm a
      and tmb = term_of_preterm b in
      let tm = mk_disj(tma,tmb) in
      let th = (ASSUME tm) in
      DISJ_CASES_THEN2
        (fun th -> ASSUME_TAC th THEN pcheck p)
        (fun th -> ASSUME_TAC th THEN pcheck q)
        th
  | Pex_falso -> FIRST_ASSUM CONTR_TAC
  | Pimp_l(a,b,p,q) ->
      let tma = term_of_preterm a
      and tmb = term_of_preterm b in
      let tm = mk_imp(tma,tmb) in
      let th = ASSUME tm in
      SUBGOAL_THEN tma (ASSUME_TAC o MP th) THENL [pcheck p; pcheck q]
  | Pforall_l(x,qf,p) ->
      let tmx = term_of_preterm x
      and tmqf = term_of_preterm qf in
      let th = ASSUME tmqf in
      ASSUME_TAC (SPEC tmx th) THEN pcheck p
  | Pforall_r (x,_,p) ->
      let tmx = term_of_preterm x in
      X_GEN_TAC tmx THEN pcheck p
  | Pexists_l(x,a,p) ->
      let tmx = term_of_preterm x
      and tma = term_of_preterm a in
      let th = ASSUME (mk_exists(tmx,tma)) in
      X_CHOOSE_TAC tmx th THEN pcheck p
  | Pexists_r(a,p) ->
       let tmx = term_of_preterm a in
       EXISTS_TAC tmx THEN pcheck p
  | Pall -> ALL_TAC
  | _ -> failwith "Not implemented yet"
;;
*)
(* ------------------------------------------------------------------------ *)
(* Tests                                                                    *)
(* ------------------------------------------------------------------------ *)
(*
let ptma = preterm_of_term `a:bool`
and ptmb = preterm_of_term `b:bool`;;

(* Test 1 *)
g `a /\ b ==> a`;;
e DISCH_TAC;;
let prf1 = Pand_l(ptma,ptmb,Pinitial ptma);;
e (pcheck prf1);;
top_thm();;

(* Test 2 *)
g `a /\ b ==> a`;;
let prf2 = Pimp_r(ptma,prf1);;
e (pcheck prf2);;
top_thm();;

(* Test 3 *)
g `a ==> a \/ b`;;
let prf = Pimp_r(ptma,(Por1_r(ptma,Pinitial ptma)));;
e (pcheck prf);;
top_thm();;

(* Test 4 *)
g `b ==> a \/ b`;;
let prf = Pimp_r(ptma,(Por2_r(ptma,Pinitial ptmb)));;
e (pcheck prf);;
top_thm();;

(* Test 5 *)
g `a \/ a ==> a`;;
let prf = Pimp_r(ptma,Por_l(ptma,ptma,Pinitial ptma,Pinitial ptma));;
e (pcheck prf);;
top_thm();;

(* Test 6 *)
g `F ==> a`;;
let prf = Pimp_r(ptma,Pex_falso);;
e (pcheck prf);;
top_thm();;

(* Test 6 *)
let ptmab = preterm_of_term `a ==> b`;;
g `a /\ (a ==> b) ==> b`;;
let prf = Pimp_r(ptma,Pand_l(ptma,ptmab,Pimp_l(ptma,ptmb,Pinitial ptma,Pinitial ptmb)));;
e (pcheck prf);;
top_thm();;

(* Test 7 *)
g `!a. F ==> a`;;
let prf = Pforall_r(ptma,ptma,Pimp_r(ptma,Pex_falso));;
e (pcheck prf);;
top_thm();;

(* Test 8 *)
g `(?u:A. F) ==> a`;;
let ptmu = preterm_of_term `u:A`;;
let ptmff = preterm_of_term `F`;;
let prf = Pimp_r(ptma,Pexists_l(ptmu,ptmff,Pex_falso));;
e (pcheck prf);;
top_thm();;

(* Test 9 *)
g `?a:bool. a ==> b`;;
let prf = Pexists_r(ptmff,Pimp_r(ptma,Pex_falso));;
e (pcheck prf);;
top_thm();;


(*
let DISJLIST = new_definition
  `DISJLIST l <=> ?p. MEM p l /\ p`;;

let CPROVE_TAC : tactic =
  fun (_,w) -> reconstract (search w);;
*)
*)