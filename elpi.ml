#use "topfind";;
#require "elpi";;
needs "pre_elpi.ml";;

unset_jrh_lexer;;

let () = Quotation.add "elp" (Quotation.ExStr (fun _ s ->
  "Elpi.quotation \""^String.escaped s^"\""));;
  
set_jrh_lexer;;

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

  val step : tactic
        
end = struct 

  unset_jrh_lexer;;

  open Elpi_API;;

  (* TODO: move to an utils module *)
  let readback_string ~depth t =
    match RawData.look ~depth t with
    | CData c when RawOpaqueData.is_string c -> RawOpaqueData.to_string c
    | _ -> Utils.type_error "readback_string"
  ;;

(* ============================= data types ============================ *)

(* Each module Hol_datatype.t defines an embed and readback function to be
   used later on to declare built-in predicates. Morally

     type 'a t = {
       embed : 'a -> RawData.term
       readback : RawData.term -> 'a
     }

   but since it is handy to have extra info in a state, these two functions
   also take and return a State.t. We use that to store a mapping
   between Elpi's unification variables and HOL-light Stv, for example.

*)

(* --------------------------------------------------------------------- *)

  module Hol_pretype : sig
    
    val t : pretype Conversion.t

  end = struct
 
    open FlexibleData

    module UV2STV = Map(struct
      type t = int
      let compare x y = x - y
      let pp fmt i = Format.fprintf fmt "%d" i
      let show = string_of_int
    end)

    let stv = ref 0
    let incr_get r = incr r; !r

    let record_Stv k state =
      State.update_return UV2STV.uvmap state (fun m ->
        try m, Stv (UV2STV.host k m)
        with Not_found ->
          let j = incr_get stv in
          UV2STV.add k j m, Stv j)

    let t = AlgebraicData.declare {
      ty = TyName "pretype";
      doc = "The algebraic data type of pretypes";
      pp = (fun fmt t -> Format.fprintf fmt "%s" (string_of_type (type_of_pretype t)));
      constructors = [
        K("uty","User type variable",A(BuiltInData.string,N),
           B (fun s -> Utv s),
           M (fun ~ok ~ko -> function (Utv s) -> ok s | _ -> ko ()));
        K("ptycon","Type constructor",A(BuiltInData.string,C(BuiltInData.list, N)),
           B (fun s l -> Ptycon(s,l)),
           M (fun ~ok ~ko -> function (Ptycon(s,l)) -> ok s l | _ -> ko ()));
        K("sty","System type variable",A(BuiltInData.int,N),
           B (fun i -> Stv i),
           M (fun ~ok ~ko -> function (Stv i) -> ok i | _ -> ko ()));
        K("uvar","",A(uvar,N),
           BS (fun (k,_) state -> record_Stv k state),         
           M (fun ~ok ~ko _ -> ko ()))
      ]
    }

  end

(* --------------------------------------------------------------------- *)
  module Hol_preterm : sig

    val t : preterm Conversion.t
    val elpi_string_of_preterm : preterm -> string

  end = struct

  let appc = RawData.Constants.from_stringc "app"
  let varc = RawData.Constants.from_stringc "varb"
  let lamc = RawData.Constants.from_stringc "lam"
  let typingc = RawData.Constants.from_stringc "typing"
  let constc = RawData.Constants.from_stringc "const"

  let mk_app t1 t2 = RawData.mkApp appc t1 [t2];;
  let mk_var s ty = RawData.mkApp varc (RawOpaqueData.of_string s) [ty];;
  let mk_lam t1 t2 = RawData.mkApp lamc t1 [t2];;
  let mk_typing t ty = RawData.mkApp typingc t [ty];;
  let mk_const s ty = RawData.mkApp constc (RawOpaqueData.of_string s) [ty];;


  let embed ~depth hyps constraints state t =
    let embed_ty s t =
      let s, t, _ = Hol_pretype.t.Conversion.embed ~depth hyps constraints s t in
      s, t in
    let rec aux state t =
      match t with
      | Varp(" elpi ",Ptycon(text,[])) ->
          Quotation.lp ~depth state (Elpi_API.Ast.Loc.initial "(antiquotation") text
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
      Hol_pretype.t.Conversion.readback ~depth hyps constraints state ty in
    let rec aux state t =
      match RawData.look ~depth t with
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
      | _ -> Utils.type_error ("readback_preterm: " ^ RawPp.Debug.show_term t)
    in
      aux state t
  ;;

  open BuiltInPredicate;;
  let elpi_string_of_preterm x = string_of_term (unsafe_term_of_preterm x);;

  let t : preterm Conversion.t = {
    ty = TyName "term";
    pp_doc = (fun fmt () -> Format.fprintf fmt "Preterm.preterm");
    pp = (fun fmt t -> Format.fprintf fmt "%s" (elpi_string_of_preterm t));
    embed = embed;
    readback = readback;
  }

  end

  (* ========================== quotations ========================== *)

  let () = Quotation.set_default_quotation (fun ~depth st loc txt ->
    let ast, l = parse_preterm (lex (explode txt)) in
    if l <> [] then failwith "Unparsed input in quotation";
    let st, t, l = Hol_preterm.t.Conversion.embed ~depth [] RawData.no_constraints st ast in
    assert (l = []);
    st, t)
  ;;

  let () = Quotation.register_named_quotation "" (fun ~depth st loc txt ->
    let ty = parse_type txt in
    let st, t, l = Hol_pretype.t.Conversion.embed ~depth [] RawData.no_constraints st (pretype_of_type ty) in
    assert (l = []);
    st, t)
  ;;

(*)
module Coercion = struct

  type coercion = {
    name : string;
    type_sch : hol_type list * hol_type;
    constant : preterm
  }

  let coercion_adt = {
    Conversion.ADT.ty = TyName "coercion";
    doc = "HOL-light coercion";
    constructors = [
      K("coercion",
        "",
        (A(Conversion.string,
	 A(Hol_type_schema.t,
         A(Hol_preterm.t,
	 N)))),
        (fun s ty ctm ->
	   { name = s;
	     type_sch = ty;
	     constant = ctm
	   }),
        (fun ~ok ~ko ->
           function { name = s; type_sch = ty; constant = ctm } -> ok s ty ctm))
    ]
  }

  let t = Conversion.adt coercion_adt

end
*)

(* ======================= abstract data types ====================== *)

module Thm = struct
  (* Proof evidence, Elpi program can only pass this around *)
  let t = OpaqueData.declare {
    name = "thm";
    doc = "The opaque witness of a theorem";
    pp = (fun f t -> Format.fprintf f "<<proof-of %a >>" pp_print_thm t);
    eq = equals_thm;
    hash = Hashtbl.hash;
    hconsed = false;
    constants = [];
  }

end

module Tactics = struct

type hyp = Hyp of string * preterm * thm
type goal = Goal of hyp list * preterm
type just = Just of (thm list -> thm)
type justification =
  | JML of just
  | JApp of justification * justification
  | JProved of thm
  | JStop

let hyp = AlgebraicData.declare {
  AlgebraicData.ty = TyName "hyp";
  doc = "HOL-light hypothesis";
  pp = (fun fmt h -> Format.fprintf fmt "TODO:hyp");
  constructors = [

    K("hyp","",A(BuiltInData.string, A(Hol_preterm.t, A(Thm.t,N))),
      B (fun s t p -> Hyp(s,t,p)),
      M (fun ~ok ~ko:_ -> function Hyp(s,t,p) -> ok s t p));
  ]
}

let goal = AlgebraicData.declare {
  ty = TyName "goal";
  doc = "HOL-light goal";
  pp = (fun fmt h -> Format.fprintf fmt "TODO:goal");
  constructors = [
    K("goal","",A(BuiltInData.list hyp,A(Hol_preterm.t,N)),
      B (fun h c -> Goal(h,c)),
      M (fun ~ok ~ko:_ -> function Goal(h,c) -> ok h c));
  ]
}

let just = OpaqueData.declare {
      name = "just";
      doc = "A proof step implemented in ML";
      pp = (fun fmt _ -> Format.fprintf fmt "<justification>");
      eq = (fun t1 t2 -> t1 == t2);
      hash = (fun t -> Hashtbl.hash t);
      hconsed = false;
      constants = [];
 }

let justification = AlgebraicData.declare {
  ty = TyName "justification";
  doc = "Elpi tactic justification";
  pp = (fun fmt h -> Format.fprintf fmt "TODO:justification");
  constructors = [
    K("jml","",A(just,N),
      B (fun f -> JML f),
      M (fun ~ok ~ko -> function JML f -> ok f | _ -> ko ()));
    K("japp","",S(S N),
      B (fun f j -> JApp(f,j)),
      M (fun ~ok ~ko -> function JApp(f,j) -> ok f j | _ -> ko ()));
    K("jproved","",A(Thm.t,N),
      B (fun p -> JProved p),
      M (fun ~ok ~ko -> function JProved p -> ok p | _ -> ko ()));
    K("jstop","",N,
      B JStop,
      M (fun ~ok ~ko -> function JStop -> ok | _ -> ko ())); 
  ]
}

let holg2elpig (hyps,concl) =
  let hyps = List.map (fun (s,thm) ->
    Hyp (s,preterm_of_term (Hol.concl thm),thm)) hyps in
  Goal(hyps,preterm_of_term concl)

let elpig2holg (Goal(hyps,g)) =
  let hyps = List.map (fun (Hyp (s,_,thm)) -> s,thm) hyps in
   (hyps, term_of_preterm g)

let rec interp_j = function
  | JML (Just f) -> f
  | JApp (j1,j2) -> fun l -> interp_j j1 [interp_j j2 l]
  | JProved thm -> fun l -> assert(l = []); thm
  | JStop -> (function [t] -> t | _ -> assert false)

end


(*
  let sequentc = E.Data.RawData.Constants.from_stringc "sequent"
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
    | (UVar _ | AppUVar _) -> s, Conversion.Flex t
    | Discard -> s, Conversion.Discard
    | App(c,hyps,[concl]) when c == sequentc ->
        assert false
    | _ -> type_error "readback_thm"
  ;;

  let sequent : thm Conversion.data = {
    Conversion.ty = "thm";
    to_term = embed_thm;
    of_term = readback_thm;
  }
  ;;
  *)


  module Builtins = struct

  open BuiltInPredicate;;
  open Notation;;
  open BuiltIn;;

  let declarations = [
    LPDoc "========================== HOL-Light ===========================";

    MLData Hol_pretype.t;

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
      In(BuiltInData.string,"constant name",
      Out(Hol_pretype.t, "constant type",
      Easy("lookup the type of known constant"))),
    (fun name _ ~depth:_ ->
       try let ty = get_const_type name in
         !: (pretype_of_type ty)
       with Failure _ -> raise No_clause)),
    DocNext);

    (* TODO:
        - export the_overloaded_skeleton (NO! serve per evitare backtracking)
        - get_var_type (poco usato, per studenti?) *)


    MLCode (Pred("hol.interface",
      In(BuiltInData.string,"constant overloaded name",
      Out(BuiltInData.list (Elpi_builtin.pair BuiltInData.string Hol_pretype.t), "constant name and type",
      Easy("lookup the interpretations of overloaded constant"))),
    (fun name _ ~depth ->
       let l = mapfilter (fun (x,(s,t)) ->
               if x = name then s, pretype_of_type t
               else fail()) !the_interface in
        !: l)),
    DocNext);

    MLCode (Pred("hol.pmk_numeral",
      In(BuiltInData.string,"possibly a numeral",
      Out(Hol_preterm.t,"the number",
      Easy "when the given string is a numeral it outputs its preterm")),
    (fun str _ ~depth ->
       if can num_of_string str then !: (pmk_numeral (num_of_string str))
       else raise No_clause)),
    DocNext);
(*)
    MLADT Coercion.coercion_adt;

    MLCode (Pred("hol.coercions",
      Out(list Coercion.t, "coercions",
        Easy("TODO commento")),
      (fun _ ~depth ->
         let l = map (fun (s,(ty,ctm)) ->
                        { Coercion.name = s;
			  type_sch = (tyvars ty,ty);
                          constant = preterm_of_term ctm
                        })
                     !the_coercions in
         !: l)),
      DocNext);
*)
    LPDoc "-------------------- printing -----------------------------";

    MLCode (Pred("hol.term->string",
      In(Hol_preterm.t,"T",
      Out(BuiltInData.string,"S",
      Easy "typechecks T and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (Hol_preterm.elpi_string_of_preterm t)
       with Failure s -> !: ("(illtyped)"^s))),
    DocAbove);

    MLCode (Pred("hol.ty->string",
      In(Hol_pretype.t,"Ty",
      Out(BuiltInData.string,"S",
      Easy "typechecks Ty and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (string_of_type (type_of_pretype t))
       with Failure _ -> !: "(illtyped)")),
    DocAbove);
(*)
    MLCode (Pred("hol.tys->string",
      In(Hol_type_schema.t,"Tys",
      Out(string,"S",
      Easy "typechecks Tys and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (string_of_type (snd t))
       with Failure _ -> !: "(illtyped)")),
    DocAbove);
*)
    LPDoc "-------------------- kernel rules ----------------------------";

    MLData Thm.t;

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

    LPDoc "-------------------- tactics ----------------------------";



    MLData Tactics.hyp;
    MLData Tactics.goal;
    MLData Tactics.just;
    MLData Tactics.justification;

    MLCode (Pred("hol.tac.ap_term_tac",
      In(Tactics.goal,"G",
      Out(BuiltInData.list Tactics.goal,"GS",
      Out(Tactics.justification,"J",
      Easy "congruence"))),
    (fun g _ _ ~depth:_ ->
      set_jrh_lexer;
      let _, gs, j = AP_TERM_TAC (Tactics.elpig2holg g) in
      let gs = List.map Tactics.holg2elpig gs in
      unset_jrh_lexer;
      !: gs +! (Tactics.JML (Tactics.Just (j null_inst)))
    )),
    DocAbove)

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
    BuiltIn.document fmt builtins;
    Setup.init
      ~builtins:(BuiltIn.declare ~file_name:builtins_doc_file builtins)
      ~basedir:(Sys.getcwd ()) elpi_flags
  ;;

  type elpi_code = Compile.program

  let files fl : elpi_code =
    try
      let p = Parse.program fl in
      Compile.program ~flags:Compile.default_flags header [p]
    with Parse.ParseError(loc,msg) ->
      failwith ("elpi: " ^ Elpi_API.Ast.Loc.show loc ^ ": " ^ msg)
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

  let static_check h q =
    if not (Compile.static_check h q) then
      failwith "elpi: type error"
  ;;

  let run_text ?max_steps program query =
    let q = Parse.goal (Ast.Loc.initial "(query)") query in
    let q = Compile.query program q in
    let exe = Compile.link q in
    static_check header q;
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

  let run_predicate ?max_steps program query =
    let q = Query.compile program (Ast.Loc.initial "(run_predicate)") query in

    (* We disable traces when we typecheck the elpi code (Elpi's type checker
       is an elpi program too) *)
    let are_we_debugging = !debugging in
    Setup.trace [];
    static_check header q;
    debug are_we_debugging;

    let exe = Compile.link q in
    match Execute.once exe with
    | Execute.Success s -> s.output
    | Failure -> failwith "elpi finds no solution"
    | NoMoreSteps -> assert false
  ;;

  (* ================================================================ *)
  (* Entry points to call elpi code *)

  let query ?max_steps p s = run_text ?max_steps p s;;

  let prove concl =
    let x, _ = run_predicate (hol ())
      (Query.Query {
        predicate = "prove";
        arguments = D(Hol_preterm.t,preterm_of_term concl,
                    Q(Thm.t,"P",
                    N)) })
    in
    x
  ;;

  let step (goal : goal) : goalstate =
    let goals, (just, _) = run_predicate (hol ())
      (Query.Query {
        predicate = "step";
        arguments = D(Tactics.goal,Tactics.holg2elpig goal,
                    Q(BuiltInData.list Tactics.goal,"Goals",
                    Q(Tactics.justification,"Just",
                    N))) })
    in
    null_meta, List.map Tactics.elpig2holg goals, (fun _ -> Tactics.interp_j just)
  ;;

  (* This runs the elpi query requesting the elaboration of a given term *)
  let elaborate p =
    let elab_p, _ = run_predicate (hol ())
      (Query.Query {
        predicate = "elab";
        arguments = D(Hol_preterm.t,p,
                    Q(Hol_preterm.t,"Elab_p",
                    N)) })
    in
    term_of_preterm elab_p
  ;;

  let quotation s =
    let p, l = parse_preterm (lex (explode s)) in
    if l <> [] then failwith "Unparsed input"
    else elaborate p
  ;;

  set_jrh_lexer;;

  let prove_tac = CONV_TAC prove

end

(* little test *)
let () = Elpi.query (Elpi.hol ()) "self-test";;

let _ : thm = prove (`0 = 0`, Elpi.prove_tac)

(* Antiquotation *)
let () = reserve_words ["^"];;
let () = install_parser ("elpi",(function
  | Resword "^" :: Ident v :: rest ->
      Varp(" elpi ",Ptycon(v,[])), rest
  | _ -> raise Noparse
))
;;
