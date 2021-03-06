(* ========================================================================= *)
(* Pascal's hexagon theorem for projective and affine planes.                *)
(* ========================================================================= *)

needs "Multivariate/cross.ml";;

(* ------------------------------------------------------------------------- *)
(* A lemma we want to justify some of the axioms.                            *)
(* ------------------------------------------------------------------------- *)

let NORMAL_EXISTS = prove
 (`!u v:real^3. ?w. ~(w = vec 0) /\ orthogonal u w /\ orthogonal v w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
  MP_TAC(ISPEC `{u:real^3,v}` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; DIMINDEX_3] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `CARD {u:real^3,v}` THEN CONJ_TAC THEN
  SIMP_TAC[DIM_LE_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Type of directions.                                                       *)
(* ------------------------------------------------------------------------- *)

let direction_tybij = new_type_definition "direction" ("mk_dir","dest_dir")
 (MESON[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] `?x:real^3. ~(x = vec 0)`);;

parse_as_infix("||",(11,"right"));;
parse_as_infix("_|_",(11,"right"));;

let perpdir = new_definition
 `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;

let pardir = new_definition
 `x || y <=> (dest_dir x) cross (dest_dir y) = vec 0`;;

let DIRECTION_CLAUSES = prove
 (`((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))`,
  MESON_TAC[direction_tybij]);;

let [PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS] = (CONJUNCTS o prove)
 (`(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)`,
  REWRITE_TAC[pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;

let PARDIR_EQUIV = prove
 (`!x y. ((||) x = (||) y) <=> x || y`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS]);;

let DIRECTION_AXIOM_1 = prove
 (`!p p'. ~(p || p') ==> ?l. p _|_ l /\ p' _|_ l /\
                             !l'. p _|_ l' /\ p' _|_ l' ==> l' || l`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real^3`; `p':real^3`] NORMAL_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;

let DIRECTION_AXIOM_2 = prove
 (`!l l'. ?p. p _|_ l /\ p _|_ l'`,
  REWRITE_TAC[perpdir; DIRECTION_CLAUSES] THEN
  MESON_TAC[NORMAL_EXISTS; ORTHOGONAL_SYM]);;

let DIRECTION_AXIOM_3 = prove
 (`?p p' p''.
        ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
        ~(?l. p _|_ l /\ p' _|_ l /\ p'' _|_ l)`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN MAP_EVERY
   (fun t -> EXISTS_TAC t THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH])
   [`basis 1 :real^3`; `basis 2 : real^3`; `basis 3 :real^3`] THEN
  VEC3_TAC);;

let DIRECTION_AXIOM_4_WEAK = prove
 (`!l. ?p p'. ~(p || p') /\ p _|_ l /\ p' _|_ l`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 2) l /\
    ~((l cross basis 1) cross (l cross basis 2) = vec 0) \/
    orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 1) cross (l cross basis 3) = vec 0) \/
    orthogonal (l cross basis 2) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 2) cross (l cross basis 3) = vec 0)`
  MP_TAC THENL [POP_ASSUM MP_TAC THEN VEC3_TAC; MESON_TAC[CROSS_0]]);;

let ORTHOGONAL_COMBINE = prove
 (`!x a b. a _|_ x /\ b _|_ x /\ ~(a || b)
           ==> ?c. c _|_ x /\ ~(a || c) /\ ~(b || c)`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `a + b:real^3` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;

let DIRECTION_AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
                  p _|_ l /\ p' _|_ l /\ p'' _|_ l`,
  MESON_TAC[DIRECTION_AXIOM_4_WEAK; ORTHOGONAL_COMBINE]);;

let line_tybij = define_quotient_type "line" ("mk_line","dest_line") `(||)`;;

let PERPDIR_WELLDEF = prove
 (`!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;

let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;

let line_lift_thm = lift_theorem line_tybij
 (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;

let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;

let point_tybij = new_type_definition "point" ("mk_point","dest_point")
 (prove(`?x:line. T`,REWRITE_TAC[]));;

parse_as_infix("on",(11,"right"));;

let on = new_definition `p on l <=> perpl (dest_point p) l`;;

let POINT_CLAUSES = prove
 (`((p = p') <=> (dest_point p = dest_point p')) /\
   ((!p. P (dest_point p)) <=> (!l. P l)) /\
   ((?p. P (dest_point p)) <=> (?l. P l))`,
  MESON_TAC[point_tybij]);;

let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;

let AXIOM_1 = prove
 (`!p p'. ~(p = p') ==> ?l. p on l /\ p' on l /\
          !l'. p on l' /\ p' on l' ==> (l' = l)`,
  POINT_TAC LINE_AXIOM_1);;

let AXIOM_2 = prove
 (`!l l'. ?p. p on l /\ p on l'`,
  POINT_TAC LINE_AXIOM_2);;

let AXIOM_3 = prove
 (`?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p on l /\ p' on l /\ p'' on l)`,
  POINT_TAC LINE_AXIOM_3);;

let AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l`,
  POINT_TAC LINE_AXIOM_4);;

(* ------------------------------------------------------------------------- *)
(* Mappings from vectors in R^3 to projective lines and points.              *)
(* ------------------------------------------------------------------------- *)

let projl = new_definition
 `projl x = mk_line((||) (mk_dir x))`;;

let projp = new_definition
 `projp x = mk_point(projl x)`;;

(* ------------------------------------------------------------------------- *)
(* Mappings in the other direction, to (some) homogeneous coordinates.       *)
(* ------------------------------------------------------------------------- *)

let PROJL_TOTAL = prove
 (`!l. ?x. ~(x = vec 0) /\ l = projl x`,
  GEN_TAC THEN
  SUBGOAL_THEN `?d. l = mk_line((||) d)` (CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[fst line_tybij; snd line_tybij];
    REWRITE_TAC[projl] THEN EXISTS_TAC `dest_dir d` THEN
    MESON_TAC[direction_tybij]]);;

let homol = new_specification ["homol"]
  (REWRITE_RULE[SKOLEM_THM] PROJL_TOTAL);;

let PROJP_TOTAL = prove
 (`!p. ?x. ~(x = vec 0) /\ p = projp x`,
  REWRITE_TAC[projp] THEN MESON_TAC[PROJL_TOTAL; point_tybij]);;

let homop_def = new_definition
 `homop p = homol(dest_point p)`;;

let homop = prove
 (`!p. ~(homop p = vec 0) /\ p = projp(homop p)`,
  GEN_TAC THEN REWRITE_TAC[homop_def; projp; MESON[point_tybij]
   `p = mk_point l <=> dest_point p = l`] THEN
  MATCH_ACCEPT_TAC homol);;

(* ------------------------------------------------------------------------- *)
(* Key equivalences of concepts in projective space and homogeneous coords.  *)
(* ------------------------------------------------------------------------- *)

let parallel = new_definition
 `parallel x y <=> x cross y = vec 0`;;

let ON_HOMOL = prove
 (`!p l. p on l <=> orthogonal (homop p) (homol l)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [homop; homol] THEN
  REWRITE_TAC[on; projp; projl; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[GSYM perpl_th; perpdir] THEN BINOP_TAC THEN
  MESON_TAC[homol; homop; direction_tybij]);;

let EQ_HOMOL = prove
 (`!l l'. l = l' <=> parallel (homol l) (homol l')`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [homol] THEN
  REWRITE_TAC[projl; MESON[fst line_tybij; snd line_tybij]
   `mk_line((||) l) = mk_line((||) l') <=> (||) l = (||) l'`] THEN
  REWRITE_TAC[PARDIR_EQUIV] THEN REWRITE_TAC[pardir; parallel] THEN
  MESON_TAC[homol; direction_tybij]);;

let EQ_HOMOP = prove
 (`!p p'. p = p' <=> parallel (homop p) (homop p')`,
  REWRITE_TAC[homop_def; GSYM EQ_HOMOL] THEN
  MESON_TAC[point_tybij]);;

(* ------------------------------------------------------------------------- *)
(* A "welldefinedness" result for homogeneous coordinate map.                *)
(* ------------------------------------------------------------------------- *)

let PARALLEL_PROJL_HOMOL = prove
 (`!x. parallel x (homol(projl x))`,
  GEN_TAC THEN REWRITE_TAC[parallel] THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[CROSS_0] THEN MP_TAC(ISPEC `projl x` homol) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [projl] THEN
  DISCH_THEN(MP_TAC o AP_TERM `dest_line`) THEN
  REWRITE_TAC[MESON[fst line_tybij; snd line_tybij]
   `dest_line(mk_line((||) l)) = (||) l`] THEN
  REWRITE_TAC[PARDIR_EQUIV] THEN REWRITE_TAC[pardir] THEN
  ASM_MESON_TAC[direction_tybij]);;

let PARALLEL_PROJP_HOMOP = prove
 (`!x. parallel x (homop(projp x))`,
  REWRITE_TAC[homop_def; projp; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[PARALLEL_PROJL_HOMOL]);;

let PARALLEL_PROJP_HOMOP_EXPLICIT = prove
 (`!x. ~(x = vec 0) ==> ?a. ~(a = &0) /\ homop(projp x) = a % x`,
  MP_TAC PARALLEL_PROJP_HOMOP THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[parallel; CROSS_EQ_0; COLLINEAR_LEMMA] THEN
  GEN_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[homop] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `c:real` THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[homop; VECTOR_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Brackets, collinearity and their connection.                              *)
(* ------------------------------------------------------------------------- *)

let bracket = define
 `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`;;

let COLLINEAR = new_definition
 `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`;;

let COLLINEAR_SINGLETON = prove
 (`!a. COLLINEAR {a}`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[AXIOM_1; AXIOM_3]);;

let COLLINEAR_PAIR = prove
 (`!a b. COLLINEAR{a,b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:point = b` THEN
  ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SINGLETON] THEN
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[AXIOM_1]);;

let COLLINEAR_TRIPLE = prove
 (`!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let COLLINEAR_BRACKET = prove
 (`!p1 p2 p3. COLLINEAR {p1,p2,p3} <=> bracket[p1;p2;p3] = &0`,
  let lemma = prove
   (`!a b c x y.
          x cross y = vec 0 /\ ~(x = vec 0) /\
          orthogonal a x /\ orthogonal b x /\ orthogonal c x
          ==> orthogonal a y /\ orthogonal b y /\ orthogonal c y`,
    REWRITE_TAC[orthogonal] THEN VEC3_TAC) in
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COLLINEAR_TRIPLE; bracket; ON_HOMOL; LEFT_IMP_EXISTS_THM] THEN
    MP_TAC homol THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[DET_3; orthogonal; DOT_3; VECTOR_3; CART_EQ;
              DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ASM_CASES_TAC `p1:point = p2` THENL
     [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_PAIR]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[parallel; COLLINEAR_TRIPLE; bracket; EQ_HOMOP; ON_HOMOL] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `mk_line((||) (mk_dir(homop p1 cross homop p2)))` THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `homop p1 cross homop p2` THEN
    ASM_REWRITE_TAC[ORTHOGONAL_CROSS] THEN
    REWRITE_TAC[orthogonal] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    ONCE_REWRITE_TAC[CROSS_TRIPLE] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    ASM_REWRITE_TAC[DOT_CROSS_DET] THEN
    REWRITE_TAC[GSYM projl; GSYM parallel; PARALLEL_PROJL_HOMOL]]);;

(* ------------------------------------------------------------------------- *)
(* Conics and bracket condition for 6 points to be on a conic.               *)
(* ------------------------------------------------------------------------- *)

let homogeneous_conic = new_definition
 `homogeneous_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^3 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$3 pow 2 +
                         d * x$1 * x$2 + e * x$1 * x$3 + f * x$2 * x$3 = &0}`;;

let projective_conic = new_definition
 `projective_conic con <=>
        ?c. homogeneous_conic c /\ con = {p | (homop p) IN c}`;;

let HOMOGENEOUS_CONIC_BRACKET = prove
 (`!con x1 x2 x3 x4 x5 x6.
        homogeneous_conic con /\
        x1 IN con /\ x2 IN con /\ x3 IN con /\
        x4 IN con /\ x5 IN con /\ x6 IN con
        ==> det(vector[x6;x1;x4]) * det(vector[x6;x2;x3]) *
            det(vector[x5;x1;x3]) * det(vector[x5;x2;x4]) =
            det(vector[x6;x1;x3]) * det(vector[x6;x2;x4]) *
            det(vector[x5;x1;x4]) * det(vector[x5;x2;x3])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homogeneous_conic; EXTENSION] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; DET_3; VECTOR_3] THEN
  CONV_TAC REAL_RING);;

let PROJECTIVE_CONIC_BRACKET = prove
 (`!con p1 p2 p3 p4 p5 p6.
        projective_conic con /\
        p1 IN con /\ p2 IN con /\ p3 IN con /\
        p4 IN con /\ p5 IN con /\ p6 IN con
        ==> bracket[p6;p1;p4] * bracket[p6;p2;p3] *
            bracket[p5;p1;p3] * bracket[p5;p2;p4] =
            bracket[p6;p1;p3] * bracket[p6;p2;p4] *
            bracket[p5;p1;p4] * bracket[p5;p2;p3]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bracket; projective_conic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOGENEOUS_CONIC_BRACKET THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pascal's theorem with all the nondegeneracy principles we use directly.   *)
(* ------------------------------------------------------------------------- *)

let PASCAL_DIRECT = prove
 (`!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x2,x5,x7} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x4,x6} /\
        ~COLLINEAR {x3,x4,x5} /\
        ~COLLINEAR {x1,x5,x7} /\
        ~COLLINEAR {x2,x5,x9} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x3,x6,x8} /\
        ~COLLINEAR {x2,x4,x5} /\
        ~COLLINEAR {x2,x4,x7} /\
        ~COLLINEAR {x2,x6,x8} /\
        ~COLLINEAR {x3,x4,x6} /\
        ~COLLINEAR {x3,x5,x8} /\
        ~COLLINEAR {x1,x3,x5}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e /\ f /\ g /\ h ==> p <=>
                    a /\ b /\ c /\ d /\ e /\ f /\ g ==> h ==> p`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PROJECTIVE_CONIC_BRACKET) THEN
  REWRITE_TAC[COLLINEAR_BRACKET; IMP_IMP; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `!q. (p ==> q) /\ (q ==> r) ==> p ==> r`) THEN
  EXISTS_TAC
   `bracket[x1;x2;x5] * bracket[x1;x3;x6] *
    bracket[x2;x4;x6] * bracket[x3;x4;x5] =
    bracket[x1;x2;x6] * bracket[x1;x3;x5] *
    bracket[x2;x4;x5] * bracket[x3;x4;x6] /\
    bracket[x1;x5;x7] * bracket[x2;x5;x9] =
    --bracket[x1;x2;x5] * bracket[x5;x9;x7] /\
    bracket[x1;x2;x6] * bracket[x3;x6;x8] =
    bracket[x1;x3;x6] * bracket[x2;x6;x8] /\
    bracket[x2;x4;x5] * bracket[x2;x9;x7] =
    --bracket[x2;x4;x7] * bracket[x2;x5;x9] /\
    bracket[x2;x4;x7] * bracket[x2;x6;x8] =
    --bracket[x2;x4;x6] * bracket[x2;x8;x7] /\
    bracket[x3;x4;x6] * bracket[x3;x5;x8] =
    bracket[x3;x4;x5] * bracket[x3;x6;x8] /\
    bracket[x1;x3;x5] * bracket[x5;x8;x7] =
    --bracket[x1;x5;x7] * bracket[x3;x5;x8]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ONCE_REWRITE_TAC[IMP_IMP] THEN
         DISCH_THEN(MP_TAC o MATCH_MP (REAL_RING
          `a = b /\ x:real = y ==> a * x = b * y`))) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BRACKET]) THEN
  REWRITE_TAC[REAL_MUL_AC] THEN ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* With longer but more intuitive non-degeneracy conditions, basically that  *)
(* the 6 points divide into two groups of 3 and no 3 are collinear unless    *)
(* they are all in the same group.                                           *)
(* ------------------------------------------------------------------------- *)

let PASCAL = prove
 (`!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x1,x2,x4} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x1,x3,x4} /\
        ~COLLINEAR {x1,x3,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x3,x4} /\
        ~COLLINEAR {x2,x3,x5} /\
        ~COLLINEAR {x2,x3,x6} /\
        ~COLLINEAR {x4,x5,x1} /\
        ~COLLINEAR {x4,x5,x2} /\
        ~COLLINEAR {x4,x5,x3} /\
        ~COLLINEAR {x4,x6,x1} /\
        ~COLLINEAR {x4,x6,x2} /\
        ~COLLINEAR {x4,x6,x3} /\
        ~COLLINEAR {x5,x6,x1} /\
        ~COLLINEAR {x5,x6,x2} /\
        ~COLLINEAR {x5,x6,x3}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(fun th ->
    MATCH_MP_TAC(TAUT `(~p ==> p) ==> p`) THEN DISCH_TAC THEN
    MP_TAC th THEN MATCH_MP_TAC PASCAL_DIRECT THEN
    ASSUME_TAC(funpow 7 CONJUNCT2 th)) THEN
  REPEAT CONJ_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[COLLINEAR_BRACKET; bracket; DET_3; VECTOR_3] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Homogenization and hence mapping from affine to projective plane.         *)
(* ------------------------------------------------------------------------- *)

let homogenize = new_definition
 `(homogenize:real^2->real^3) x = vector[x$1; x$2; &1]`;;

let projectivize = new_definition
 `projectivize = projp o homogenize`;;

let HOMOGENIZE_NONZERO = prove
 (`!x. ~(homogenize x = vec 0)`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_3;
              homogenize] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conic in affine plane.                                                    *)
(* ------------------------------------------------------------------------- *)

let affine_conic = new_definition
 `affine_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^2 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$1 * x$2 +
                         d * x$1 + e * x$2 + f = &0}`;;

(* ------------------------------------------------------------------------- *)
(* Relationships between affine and projective notions.                      *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_PROJECTIVIZE = prove
 (`!a b c. collinear{a,b,c} <=>
           COLLINEAR{projectivize a,projectivize b,projectivize c}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
  REWRITE_TAC[COLLINEAR_BRACKET; projectivize; o_THM; bracket] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `det(vector[homogenize a; homogenize b; homogenize c]) = &0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homogenize; DOT_2; VECTOR_SUB_COMPONENT; DET_3; VECTOR_3] THEN
    CONV_TAC REAL_RING;
    MAP_EVERY (MP_TAC o C SPEC PARALLEL_PROJP_HOMOP)
     [`homogenize a`; `homogenize b`; `homogenize c`] THEN
    MAP_EVERY (MP_TAC o C SPEC HOMOGENIZE_NONZERO)
     [`a:real^2`; `b:real^2`; `c:real^2`] THEN
    MAP_EVERY (MP_TAC o CONJUNCT1 o C SPEC homop)
     [`projp(homogenize a)`; `projp(homogenize b)`; `projp(homogenize c)`] THEN
    REWRITE_TAC[parallel; cross; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                DET_3; VEC_COMPONENT] THEN
    CONV_TAC REAL_RING]);;

let AFFINE_PROJECTIVE_CONIC = prove
 (`!con. affine_conic con <=> ?con'. projective_conic con' /\
                                     con = {x | projectivize x IN con'}`,
  REWRITE_TAC[affine_conic; projective_conic; homogeneous_conic] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(?con' con a b c d e f. P con' con a b c d e f) <=>
    (?a b d e f c con' con. P con' con a b c d e f)`] THEN
  MAP_EVERY (fun s ->
   AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
   X_GEN_TAC(mk_var(s,`:real`)) THEN REWRITE_TAC[])
   ["a"; "b"; "c"; "d"; "e"; "f"] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[IN_ELIM_THM; projectivize; o_THM] THEN
  BINOP_TAC THENL [CONV_TAC TAUT; AP_TERM_TAC] THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  MP_TAC(SPEC `x:real^2` HOMOGENIZE_NONZERO) THEN
  DISCH_THEN(MP_TAC o MATCH_MP PARALLEL_PROJP_HOMOP_EXPLICIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[homogenize; VECTOR_3] THEN
  UNDISCH_TAC `~(k = &0)` THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Hence Pascal's theorem for the affine plane.                              *)
(* ------------------------------------------------------------------------- *)

let PASCAL_AFFINE = prove
 (`!con x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        ~collinear {x1,x2,x4} /\
        ~collinear {x1,x2,x5} /\
        ~collinear {x1,x2,x6} /\
        ~collinear {x1,x3,x4} /\
        ~collinear {x1,x3,x5} /\
        ~collinear {x1,x3,x6} /\
        ~collinear {x2,x3,x4} /\
        ~collinear {x2,x3,x5} /\
        ~collinear {x2,x3,x6} /\
        ~collinear {x4,x5,x1} /\
        ~collinear {x4,x5,x2} /\
        ~collinear {x4,x5,x3} /\
        ~collinear {x4,x6,x1} /\
        ~collinear {x4,x6,x2} /\
        ~collinear {x4,x6,x3} /\
        ~collinear {x5,x6,x1} /\
        ~collinear {x5,x6,x2} /\
        ~collinear {x5,x6,x3}
        ==> affine_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            collinear {x1,x9,x5} /\
            collinear {x1,x8,x6} /\
            collinear {x2,x9,x4} /\
            collinear {x2,x7,x6} /\
            collinear {x3,x8,x4} /\
            collinear {x3,x7,x5}
            ==> collinear {x7,x8,x9}`,
  REWRITE_TAC[COLLINEAR_PROJECTIVIZE; AFFINE_PROJECTIVE_CONIC] THEN
  REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP PASCAL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Special case of a circle where nondegeneracy is simpler.                  *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_NOT_COCIRCULAR = prove
 (`!r c x y z:real^2.
        dist(c,x) = r /\ dist(c,y) = r /\ dist(c,z) = r /\
        ~(x = y) /\ ~(x = z) /\ ~(y = z)
        ==> ~collinear {x,y,z}`,
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM DOT_EQ_0] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL; DOT_2] THEN
  REWRITE_TAC[dist; NORM_EQ_SQUARE; CART_EQ; DIMINDEX_2; FORALL_2;
              DOT_2; VECTOR_SUB_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let PASCAL_AFFINE_CIRCLE = prove
 (`!c r x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        PAIRWISE (\x y. ~(x = y)) [x1;x2;x3;x4;x5;x6] /\
        dist(c,x1) = r /\ dist(c,x2) = r /\ dist(c,x3) = r /\
        dist(c,x4) = r /\ dist(c,x5) = r /\ dist(c,x6) = r /\
        collinear {x1,x9,x5} /\
        collinear {x1,x8,x6} /\
        collinear {x2,x9,x4} /\
        collinear {x2,x7,x6} /\
        collinear {x3,x8,x4} /\
        collinear {x3,x7,x5}
        ==> collinear {x7,x8,x9}`,
  GEN_TAC THEN GEN_TAC THEN
  MP_TAC(SPEC `{x:real^2 | dist(c,x) = r}` PASCAL_AFFINE) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[PAIRWISE; ALL; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [IMP_IMP] THEN
  DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC COLLINEAR_NOT_COCIRCULAR THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `c:real^2`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[affine_conic; dist; NORM_EQ_SQUARE] THEN
    ASM_CASES_TAC `&0 <= r` THEN ASM_REWRITE_TAC[] THENL
     [MAP_EVERY EXISTS_TAC
       [`&1`; `&1`; `&0`; `-- &2 * (c:real^2)$1`; `-- &2 * (c:real^2)$2`;
        `(c:real^2)$1 pow 2 + (c:real^2)$2 pow 2 - r pow 2`] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      REPLICATE_TAC 5 (EXISTS_TAC `&0`) THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC]]);;
