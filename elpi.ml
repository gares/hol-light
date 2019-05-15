#use "topfind";;
#require "elpi";;
needs "parser.ml";;
needs "pre_elpi.ml";;

module Elpi : sig

  type elpi_code

  (* compile elpi files *)
  val files : string list -> elpi_code
  val hol : unit -> elpi_code

  (* run a query *)
  val query : ?max_steps:int -> elpi_code -> string -> unit

  (* activate debugging, eventually focus on some Elpi predicates *)
  type debug = On of string list | Off
  val debug : debug -> unit

  (* The ``quotation`` calling Elpi's elab predicate *)
  val quotation : string -> term

  (* Rule *)
  val prove : term -> thm

  (* Tactic *)
  val prove_tac : tactic
        
end = struct 

  unset_jrh_lexer;;

  open Elpi_API;;
  module E = Extend;;
  open E.Data;;
  open E.Utils;;
  open C;;

  (* TODO: move to an utils module *)
  let readback_string ~depth t =
    match look ~depth t with
    | CData c when is_string c -> to_string c
    | _ -> type_error "readback_string"
  ;;

(* ============================= data types ============================ *)

(* Each module Hol_datatype.t defines an embed and readback function to be
   used later on to declare built-in predicates. Morally

     type 'a data = {
       embed : 'a -> E.Data.term
       readback : E.Data.term -> 'a
     }

   but since it is handy to have extra info in a state, these two functions
   are also take and return a E.State.t. We use that to store a mapping
   between Elpi's unification variables and HOL-light Stv, for example.

*)

(* --------------------------------------------------------------------- *)

  module Hol_pretype : sig

    val t : pretype E.BuiltInPredicate.data

    (* This API is used by Hol_preterm and Hol_type_schema *)
    module Internal : sig
      val mk_app : string -> E.Data.term list -> E.Data.term
      val appc : E.Data.constant
      val varc : E.Data.constant
    end
  end = struct module Internal = struct

  (* signature *)
  let varc = Constants.from_stringc "tyvar";;
  let appc = Constants.from_stringc "tyapp";;

  (* helpers *)
  let mk_var s = mkApp varc (of_string s) [];;
  let mk_app s l = mkApp appc (of_string s) [list_to_lp_list l];;

  (* State component mapping elpi unification variables to HOL-light's
    invented (system) type variables *)
  let invented_tyvars =
    E.State.declare ~name:"invented-tyvars"
      ~pp:(fun f (_,l) ->
        let pp_elem fmt (ub,(lvl,stvno)) =
          Format.fprintf fmt "(%a,%d)"
            (E.Pp.term lvl) (mkUVar ub lvl 0)
            stvno in
        Format.fprintf f "%a" (E.Pp.list pp_elem ";") l)
      ~compilation_is_over:(fun ~args:_ x -> Some x)
      ~init:(fun () -> -1, [])
  ;;

  let embed ~depth hyps constraints state t =
    let state = ref state in
    let rec aux t =
      match t with (*
      | Ptycon("",[]) ->
          let s, n = E.State.update_return invented_tyvars !state
            (fun (n,l) -> (n-1,l),n) in
          state := s;
          aux (Stv n) *)
      | Ptycon(s,tl) -> mk_app s (List.map aux tl)
      | Utv s -> mk_var s
      | Stv n ->
          let tyvarsno, tyvars = E.State.get invented_tyvars !state in
          try
            let b,(lvl,_) = List.find (fun (_,(_,m)) -> m = n) tyvars in
            E.Data.mkUVar b lvl 0
          with Not_found ->
            let b = E.Data.fresh_uvar_body !state in
            let tyvars = (b, (depth, n)) :: tyvars in
            state := E.State.set invented_tyvars !state (tyvarsno,tyvars);
            aux t
    in
    let t = aux t in
    !state, t, []
  ;;

  let readback ~depth hyps constraints state t =
    let state = ref state in
    let new_Stv ?(r=fresh_uvar_body !state) lvl =
      let s, t = E.State.update_return invented_tyvars !state
        (fun (no,vars) -> (no-1, (r,(lvl,no)):: vars), Stv no) in
      state := s;
      t
      in
    let find_Stv r lvl =
      try
        let _, vars = E.State.get invented_tyvars !state in
        let _, no = List.assq r vars in
        Stv no
      with Not_found -> new_Stv ~r lvl in
    let rec aux t =
      match look ~depth t with
      | App(c, s, [l]) when c == appc ->
          Ptycon(readback_string ~depth s,
                 List.map aux (lp_list_to_list ~depth l))
      | App(c, s, []) when c == varc -> Utv(readback_string ~depth s)
      | Discard -> new_Stv depth
      | (UVar(r,lvl,_) | AppUVar(r,lvl,_)) -> find_Stv r lvl (* NO args? *)
      | _ -> type_error ("Hol_pretype.readback: " ^ E.Pp.Raw.show_term t)
    in
    let t = aux t in
    !state, t
  ;;

  open E.BuiltInPredicate;;

  let t : pretype data = {
    ty = TyName "ty";
    doc = "Preterm.pretype";
    embed = embed;
    readback = readback;
  }

  end include Internal end

(* --------------------------------------------------------------------- *)
  module Hol_preterm : sig

    val t : preterm E.BuiltInPredicate.data

  end = struct module Internal = struct

  let appc = Constants.from_stringc "app"
  let varc = Constants.from_stringc "varb"
  let lamc = Constants.from_stringc "lam"
  let typingc = Constants.from_stringc "typing"
  let constc = Constants.from_stringc "const"

  let mk_app t1 t2 = mkApp appc t1 [t2];;
  let mk_var s ty = mkApp varc (of_string s) [ty];;
  let mk_lam t1 t2 = mkApp lamc t1 [t2];;
  let mk_typing t ty = mkApp typingc t [ty];;
  let mk_const s ty = mkApp constc (of_string s) [ty];;


  let embed ~depth hyps constraints state t =
    let embed_ty s t =
      let s, t, _ = Hol_pretype.t.E.BuiltInPredicate.embed ~depth hyps constraints s t in
      s, t in
    let rec aux state t =
      match t with
      | Varp(s,ty) ->
          let state, ty = embed_ty state ty in
          state, mk_var s ty
      | Constp (s,ty) ->
          let state, ty = embed_ty state ty in
          state, mk_const s ty
      | Combp(t1,t2) ->
          let state, t1 = aux state t1 in
          let state, t2 = aux state t2 in
          state, mk_app t1 t2
      | Absp(t1,t2) ->
          let state, t1 = aux state t1 in
          let state, t2 = aux state t2 in
          state, mk_lam t1 t2
      | Typing(t,ty) ->
          let state, ty = embed_ty state ty in
          let state, t = aux state t in
          state, mk_typing t ty
     in
    let state, t = aux state t in
    state, t, []
  ;;

  let readback ~depth hyps constraints state t =
    let readback_ty state ty =
      Hol_pretype.t.E.BuiltInPredicate.readback ~depth hyps constraints state ty in
    let rec aux state t =
      match look ~depth t with
      | App(c,s,[ty]) when c == varc ->
          let state, ty = readback_ty state ty in
          state, Varp(readback_string ~depth s,ty)
      | App(c,s,[ty]) when c == constc ->
          let state, ty = readback_ty state ty in
          state, Constp(readback_string ~depth s,ty)
      | App(c,t1,[t2]) when c == appc ->
          let state, t1 = aux state t1 in
          let state, t2 = aux state t2 in
          state, Combp(t1, t2)
      | App(c,t1,[t2]) when c == lamc ->
          let state, t1 = aux state t1 in
          let state, t2 = aux state t2 in
          state, Absp(t1, t2)
      | App(c,_,_) when c == typingc ->
          assert false
      | _ -> type_error ("readback_preterm: " ^ E.Pp.Raw.show_term t)
    in
      aux state t
  ;;

  open E.BuiltInPredicate;;

  let t : preterm data = {
    ty = TyName "term";
    doc = "Preterm.preterm";
    embed = embed;
    readback = readback;
  }

  end include Internal end

(* --------------------------------------------------------------------- *)
  module Hol_type_schema : sig

    val t : (hol_type list * hol_type) E.BuiltInPredicate.data

  end = struct

  let monoc = Constants.from_stringc "mono"
  let allc = Constants.from_stringc "all"

  let rec position ~depth x = function
    | [] -> failwith (x ^ " is a free variable")
    | y :: rest when x = y -> List.length rest + depth
    | _ :: xs -> position ~depth x xs
  ;;

  let embed ~depth vars ty =
    let vars = List.map dest_vartype vars in
    let rec embed_mono = function
      | Tyapp(s,l) -> Hol_pretype.Internal.mk_app s (List.map embed_mono l)
      | Tyvar x -> mkConst (position ~depth x vars)
    in
    let rec embed_all = function
      | [] -> mkApp monoc (embed_mono ty) []
      | _ :: xs -> mkApp allc (mkLam (embed_all xs)) []
    in
      embed_all (List.rev vars)
  ;;

  let readback ~depth t =
    let rec readback_mono ~depth subst t =
      match look ~depth t with
      | App(c,s,[args]) when c == Hol_pretype.Internal.appc ->
          mk_type (readback_string ~depth s,
                   List.map (readback_mono ~depth subst) (E.Utils.lp_list_to_list ~depth args))
      | App(c,s,[]) when c == Hol_pretype.Internal.varc -> assert false
      | Const i -> List.assoc i subst
      | _ -> type_error ("readback_mono: " ^ E.Pp.Raw.show_term t)
    in
    let rec readback_all ~depth subst t =
      match look ~depth t with
      | App(c,t,[]) when c == monoc -> readback_mono ~depth subst t
      | App(c,l,[]) when c == allc ->
          begin match look ~depth l with
          | Lam t ->
              readback_all ~depth:(depth+1)
                 ( (depth, mk_vartype (string_of_int depth)) :: subst) t
          | _ -> type_error "readback_all"
          end
      | _ -> type_error "readback_ty_schema"
    in
      readback_all ~depth [] t
  ;;

  open E.BuiltInPredicate;;

  let t = {
    ty = TyName "tys";
    doc = "Fusion.Hol.hol_type";
    embed = (fun ~depth _ _ s (vars,ty) ->
      s, embed ~depth:0 vars ty, []);
    readback = (fun ~depth _ _ s ty ->
      let ty = readback ~depth ty in
      s, (tyvars ty, ty));
  }

  end

  (* ======================= abstract data types ====================== *)

  (* Proof evidence, Elpi program can only pass this around *)
  let thm_cd = E.CData.declare { E.CData.data_name = "Hol.thm";
    data_pp = (fun f t -> Format.fprintf f "<<proof-of %a >>" pp_print_thm t);
    data_eq = equals_thm;
    data_hash = Hashtbl.hash;
    data_hconsed = false;
  }
  ;;

  let thm : thm E.BuiltInPredicate.data =
    E.BuiltInPredicate.cdata ~name:"thm" thm_cd
  ;;

  (* ========================== quotations ========================== *)

  let () = E.Compile.set_default_quotation (fun ~depth st loc txt ->
    let ast, l = parse_preterm (lex (explode txt)) in
    if l <> [] then failwith "Unparsed input in quotation";
    let st, t, l = Hol_preterm.t.E.BuiltInPredicate.embed ~depth [] E.Data.no_constraints st ast in
    assert (l = []);
    st, t)
  ;;

  let () = E.Compile.register_named_quotation "" (fun ~depth st loc txt ->
    let ty = parse_type txt in
    let vars = tyvars ty in
    let st, t, l = Hol_type_schema.t.E.BuiltInPredicate.embed ~depth [] E.Data.no_constraints st (vars,ty) in
    assert (l = []);
    st, t)
  ;;


module Thm = struct
  let thm = E.CData.declare {
      data_name = "Hol.thm";
      data_pp = (fun fmt t ->
        let hyp, concl = Hol.dest_thm t in
        Format.fprintf fmt "<thm: TODO |- %s >" (string_of_term concl));
      data_eq = (fun t1 t2 -> t1 == t2);
      data_hash = (fun t -> Hashtbl.hash t);
      data_hconsed = false;
 }
 let t = E.BuiltInPredicate.cdata ~name:"thm" ~doc:"HOL proof evidence" thm

end

module Tactics = struct
type tactics =
  | Arith of preterm
  | Refl of preterm

let tactics_adt = {
  E.BuiltInPredicate.ADT.ty = TyName "tactic";
  doc = "HOL-light tactics";
  constructors = [
    K("arith","",A(Hol_preterm.t,N),
      (fun t -> Arith t),
      (fun ~ok ~ko -> function Arith t -> ok t | _ -> ko));
    K("refl","",A(Hol_preterm.t,N),
      (fun t -> Arith t),
      (fun ~ok ~ko -> function Arith t -> ok t | _ -> ko)); 

  ]
}
let t = E.BuiltInPredicate.adt tactics_adt

end


(*
  let sequentc = E.Data.Constants.from_stringc "sequent"
  ;;

  let embed_thm ~depth _ { E.Data.state = s } thm =
    let hyps, concl = dest_thm thm in
    s, mkApp sequentc
      (E.Utils.list_to_lp_list (List.map (embed_term ~depth []) hyps))
      [embed_term ~depth [] concl; mkCData (thm_cd.E.CData.cin thm)]
  ;;

  MLTAC( IN(term,OUT(thm))

  match look ~depth p with
  | App(c,t,[]) when c == arithc -> ARITH_RULE (readback_term t)



  let readback_thm ~depth hyps { E.Data.state = s } t =
    match look ~depth t with
    | (UVar _ | AppUVar _) -> s, E.BuiltInPredicate.Flex t
    | Discard -> s, E.BuiltInPredicate.Discard
    | App(c,hyps,[concl]) when c == sequentc ->
        assert false
    | _ -> type_error "readback_thm"
  ;;

  let sequent : thm E.BuiltInPredicate.data = {
    E.BuiltInPredicate.ty = "thm";
    to_term = embed_thm;
    of_term = readback_thm;
  }
  ;;
  *)

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

let elpi_string_of_preterm = string_of_term o unsafe_term_of_preterm;;

  module Builtins = struct

  open E.BuiltInPredicate;;
  open Notation;;

  let declarations = [
    LPDoc "========================== HOL-Light ===========================";

(*
    MLCode (Pred("hol.thm",
      In(string,"thm name",
      Out(sequent,"the sequent",
      Easy("looks up a theorem in the environment"))),
    (fun name _ ~depth ->
       try !: (List.assoc name !theorems)
       with Not_found -> E.Utils.error ("thm "^name^"not found"))),
    DocNext);

*)

    LPDoc "-------------------- environment -----------------------------";

    MLCode (Pred("hol.env",
      In(string,"constant name",
      Out(Hol_type_schema.t, "constant type",
      Easy("lookup the type of known constant"))),
    (fun name _ ~depth:_ ->
       try let ty = get_const_type name in
         !: (tyvars ty, ty)
       with Failure _ -> raise No_clause)),
    DocNext);

    (* TODO:
        - export the_overloaded_skeleton (NO! serve per evitare backtracking)
        - get_var_type (poco usato, per studenti?) *)


    MLCode (Pred("hol.interface",
      In(string,"constant overloaded name",
      Out(list (Elpi_builtin.pair string Hol_pretype.t), "constant name and type",
      Easy("lookup the interpretations of overloaded constant"))),
    (fun name _ ~depth ->
       let l = mapfilter (fun (x,(s,t)) ->
               if x = name then s, pretype_of_type t
               else fail()) !the_interface in
        !: l)),
    DocNext);

    MLCode (Pred("hol.pmk_numeral",
      In(string,"possibly a numeral",
      Out(Hol_preterm.t,"the number",
      Easy "when the given string is a numeral it outputs its preterm")),
    (fun str _ ~depth ->
       if can num_of_string str then !: (pmk_numeral (num_of_string str))
       else raise No_clause)),
    DocNext);

    LPDoc "-------------------- printing -----------------------------";

    MLCode (Pred("hol.term->string",
      In(Hol_preterm.t,"T",
      Out(string,"S",
      Easy "typechecks T and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (elpi_string_of_preterm t)
       with Failure s -> !: ("(illtyped)"^s))),
    DocAbove);

    MLCode (Pred("hol.ty->string",
      In(Hol_pretype.t,"Ty",
      Out(string,"S",
      Easy "typechecks Ty and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (string_of_type (type_of_pretype t))
       with Failure _ -> !: "(illtyped)")),
    DocAbove);

    MLCode (Pred("hol.tys->string",
      In(Hol_type_schema.t,"Tys",
      Out(string,"S",
      Easy "typechecks Tys and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (string_of_type (snd t))
       with Failure _ -> !: "(illtyped)")),
    DocAbove);

    LPDoc "-------------------- kernel rules ----------------------------";

    MLCData (Thm.t, Thm.thm);

    MLCode (Pred("hol.rule.refl",
      In(Hol_preterm.t,"X",
      Out(Thm.t,"P",
      Easy "P is a proof of X = X")),
    (fun x _ ~depth:_ ->
      set_jrh_lexer;
      let rc = Hol.REFL (term_of_preterm x) in
      unset_jrh_lexer;
      !: rc
      )),
    DocAbove);

(*
      val TRANS : thm -> thm -> thm
      val MK_COMB : thm * thm -> thm
      val ABS : term -> thm -> thm
      val BETA : term -> thm
      val ASSUME : term -> thm
      val EQ_MP : thm -> thm -> thm
      val DEDUCT_ANTISYM_RULE : thm -> thm -> thm
      val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
      val INST : (term * term) list -> thm -> thm
*)

    MLADT Tactics.tactics_adt;



  ]
  ;;

  end

  (* Elpi initialization. header holds the contents of hol-builtin.elpi,
     that is Elpi's standard predicates plus the ones in the Builtins module
     above *)
  let header, _ =
    let elpi_flags =
      try
        let ic, _ as p = Unix.open_process "elpi -where 2>/dev/null" in
        let w = input_line ic in
        let _ = Unix.close_process p in ["-I";w]
      with _ -> [] in
    Setup.set_error (fun ?loc:_ s -> failwith ("Elpi: " ^ s));
    Setup.set_anomaly (fun ?loc:_ s -> failwith ("Elpi: anomaly: " ^ s));
    Setup.set_type_error (fun ?loc:_ s -> failwith ("Elpi: type error: " ^ s));
    let builtins_doc_file = "hol-builtin.elpi" in
    let builtins = Elpi_builtin.std_declarations @ Builtins.declarations in
    let fmt = Format.formatter_of_out_channel (open_out builtins_doc_file) in
    E.BuiltInPredicate.document fmt builtins;
    Setup.init
      ~builtins:(E.BuiltInPredicate.builtin_of_declaration
          ~file_name:builtins_doc_file builtins)
      ~basedir:(Sys.getcwd ()) elpi_flags
  ;;

  type elpi_code = Compile.program

  let files fl : elpi_code =
    let p = Parse.program fl in
    Compile.program ~flags:Compile.default_flags header [p]
  ;;

  let hol () = files ["hol.elpi"];;

  type debug = On of string list | Off

  let debugging = ref Off

  let debug = function
   | On preds ->
      let std_opts = [
        "-trace-on";"-trace-at";"run";"1";"999";
        "-trace-only";"run";"-trace-only";"assign";"-trace-only";"select"] in
      let only_preds =
        List.flatten (List.map (fun p -> ["-trace-only-pred";p]) preds) in
      Setup.trace (std_opts @ only_preds);
      debugging := On preds
   | Off ->
      Setup.trace [];
      debugging := Off
  ;;

  let query ?max_steps p s =
    let q = Parse.goal (Ast.Loc.initial "(query)") s in
    let q = Compile.query p q in
    let exe = Compile.link q in
    let _ = Compile.static_check header q in
    match Execute.once ?max_steps exe with
    | Execute.Success { assignments = assignments } ->
        if not (Data.StrMap.is_empty assignments) then
        Format.printf "Assignments: %a\n"
          (Data.StrMap.pp Pp.term) assignments
    | Failure ->
        Format.printf "Failure\n"
    | NoMoreSteps ->
        Format.printf "Timeout\n"
  ;;

  (* This is the entry point predicate for calling the elaborator *)
  let elabc = E.Data.Constants.from_stringc "elab" ;;

  (* This runs the elpi query requesting the elaboration of a given term *)
  let elaborate p =
    let q = E.Compile.query (hol ()) (fun ~depth st ->
      let st, t, _ = Hol_preterm.t.E.BuiltInPredicate.embed ~depth [] E.Data.no_constraints st p in
      let st, x = E.Compile.mk_Arg st ~name:"E" ~args:[] in
      st, (Ast.Loc.initial "(quotation)",mkApp elabc t [x])) in

    (* We disable traces when we typecheck the elpi code (Elpi's type checker
       is an elpi program too) *)
    let are_we_debugging = !debugging in
    Setup.trace [];
    let _ = Compile.static_check header q in
    debug are_we_debugging;

    let exe = Compile.link q in

    match Execute.once exe with
    | Execute.Success { Elpi_API.Data.assignments = a; constraints = c; state = s} ->
        let t = Data.StrMap.find "E" a in
        term_of_preterm (snd (Hol_preterm.t.readback ~depth:0 [] c s (E.Data.of_term t)))
    | Failure -> failwith "elaboration error"
    | NoMoreSteps -> assert false
  ;;

  let quotation s =
    let p, l = parse_preterm (lex (explode s)) in
    if l <> [] then failwith "Unparsed input"
    else elaborate p
  ;;

  let () = Quotation.add "elp" (Quotation.ExStr (fun _ s ->
    "Elpi.quotation \""^String.escaped s^"\""));;


  (* Using an elpi predicate as a rule/tactic *)
  let provec = E.Data.Constants.from_stringc "prove";;

  let prove concl =
    let q = E.Compile.query (hol ()) (fun ~depth st ->
      let concl = preterm_of_term concl in
      let st, concl, _ = Hol_preterm.t.E.BuiltInPredicate.embed ~depth [] E.Data.no_constraints st concl in
      let st, p = E.Compile.mk_Arg st ~name:"P" ~args:[] in
      st, (Ast.Loc.initial "(prove)",mkApp provec concl [p])) in

    (* We disable traces when we typecheck the elpi code (Elpi's type checker
       is an elpi program too) *)
    let are_we_debugging = !debugging in
    Setup.trace [];
    let _ = Compile.static_check header q in
    debug are_we_debugging;

    let exe = Compile.link q in
    match Execute.once exe with
    | Execute.Success { Elpi_API.Data.assignments = a; constraints = c; state = s} ->
        let p = Data.StrMap.find "P" a in
        snd(Thm.t.readback ~depth:0 [] c s (E.Data.of_term p))
    | Failure -> failwith "prover fails"
    | NoMoreSteps -> assert false
  ;;

  set_jrh_lexer;;

  let prove_tac = CONV_TAC prove

end

(* axiom for type error *)
new_constant ("unsafe_cast", `:A -> B`);;
new_constant ("type_error", `:A -> B`);;


(* little test *)
let () = Elpi.query (Elpi.hol ()) "self-test";;

let _ : thm = prove (`0 = 0`, Elpi.prove_tac)
