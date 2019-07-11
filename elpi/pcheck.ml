(* ------------------------------------------------------------------------- *)
(* TODO: I the first argument of "Pimp_r of  preterm * proof" neede?         *)
(* ------------------------------------------------------------------------- *)

type proof =
   | Pand_l    of  preterm * preterm * proof
   | Pand_r    of  proof * proof
   | Por_l     of  preterm * preterm * proof * proof
   | Por1_r    of  preterm * proof
   | Por2_r    of  preterm * proof
   | Porc_r    of  proof
   | Pex_falso
   | Pinitial  of  preterm
   | Pimp_l    of  preterm * preterm * proof * proof
   | Pimp_r    of  preterm * proof
   | Pforall_l of  preterm * preterm * proof
   | Pforall_r of  preterm * preterm * proof
   | Pexists_l of  preterm * preterm * proof
   | Pexists_r of  preterm * proof
   | Pall;;

let rec pcheck : proof -> tactic =
  function
    Pinitial a ->
      ACCEPT_TAC (ASSUME (term_of_preterm a))
  | Pand_l(a,b,p') ->
      CONJUNCTS_THEN ASSUME_TAC
        (ASSUME (mk_conj (term_of_preterm a, term_of_preterm b))) THEN
      pcheck p'
  | Pand_r(p,q) ->
      CONJ_TAC THENL [pcheck p; pcheck q]
  | Pimp_r(_,p) ->
      DISCH_TAC THEN pcheck p
  | Por1_r(_,p) ->
      DISJ1_TAC THEN pcheck p
  | Por2_r(_,p) ->
      DISJ2_TAC THEN pcheck p
  | Por_l(a,b,p,q) ->
      let tma = term_of_preterm a
      and tmb = term_of_preterm b in
      let tm = mk_disj(tma,tmb) in
      let th = ASSUME tm in
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
  | Pforall_l(x,a,p) ->
      let tmx = term_of_preterm x
      and tma = term_of_preterm a in
      let th = ASSUME tma in
      ASSUME_TAC (SPEC tmx th)
  | Pforall_r (x,_,p) ->
      let tmx = term_of_preterm x in
      X_GEN_TAC tmx THEN pcheck p

(*
   | Pexists_l of  preterm * preterm * proof
   | Pexists_r of  preterm * proof;;
*)

  | Pall -> ALL_TAC
  | _ -> failwith "Not implemented yet"
;;


(* Test 1 *)
let ptma = preterm_of_term `a:bool`
and ptmb = preterm_of_term `b:bool`;;
let prf1 = Pand_l(ptma,ptmb,Pinitial ptma);;

g `a /\ b ==> a`;;
e DISCH_TAC;;
e (pcheck prf1);;

(* Test 2 *)
let prf2 = Pimp_r(ptma,prf1);;
g `a /\ b ==> a`;;
e (pcheck prf2);;

(* Test 3 *)
g `a ==> a \/ b`;;
let prf = Pimp_r(ptma,(Por1_r(ptma,Pinitial ptma)));;
e (pcheck prf);;

(* Test 4 *)
g `b ==> a \/ b`;;
let prf = Pimp_r(ptma,(Por2_r(ptma,Pinitial ptmb)));;
e (pcheck prf);;

(* Test 5 *)
g `a \/ a ==> a`;;
let prf = Pimp_r(ptma,Por_l(ptma,ptma,Pinitial ptma,Pinitial ptma));;
e (pcheck prf);;

(* Test 6 *)
g `F ==> a`;;
let prf = Pimp_r(ptma,Pex_falso);;
e (pcheck prf);;

(* Test 6 *)
let ptmab = preterm_of_term `a ==> b`;;
g `a /\ (a ==> b) ==> b`;;
let prf = Pimp_r(ptma,Pand_l(ptma,ptmab,Pimp_l(ptma,ptmb,Pinitial ptma,Pinitial ptmb)));;
e (pcheck prf);;

(* Test 7 *)
g `!a. F ==> a`;;
let prf = Pforall_r(ptma,ptma,Pimp_r(ptma,Pex_falso));;
e (pcheck prf);;


(*
let DISJLIST = new_definition
  `DISJLIST l <=> ?p. MEM p l /\ p`;;

let CPROVE_TAC : tactic =
  fun (_,w) -> reconstract (search w);;
*)
