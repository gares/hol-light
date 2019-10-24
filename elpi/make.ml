(*#use "topfind";;
#require "elpi";;*)
needs "elpi/pre_elpi.ml";;
needs "elpi/pcheck.ml";;
needs "tactics.ml";;

unset_jrh_lexer;;

(* ``quotation`` *)
let () = Quotation.add "elp" (Quotation.ExStr (fun _ s ->
  "Hol_elpi.quotation \""^String.escaped s^"\""));;

(* Antiquotation {{.. ^X .. }} *)
let antiquotation_tag = "_elpi_"
let tag_len = String.length antiquotation_tag

let () = reserve_words ["^"];;
let () = install_parser ("elpi",(function
  | Resword "^" :: Ident v :: rest -> 
       Varp(antiquotation_tag^v,Ptycon("",[])), rest
  | _ -> raise Noparse )) ;;

set_jrh_lexer;;

module Hol_elpi : sig

  type elpi_code

  (* compile elpi compile_files *)
  val compile_files : string list -> elpi_code
  val hol : unit -> elpi_code
  val current : unit -> elpi_code

  (* typecheck *)
  val typecheck : ?code:elpi_code -> unit -> unit
  val print2html : ?code:elpi_code -> unit -> unit

  (* run a query *)
  val query : ?max_steps:int -> ?code:elpi_code -> string -> unit

  (* activate debugging, eventually focus on some Elpi predicates *)
  type debug = On of string list | Off
  val debug : debug -> unit

  (* use [accumulate (__POS_OF__ "text")] *)
  val accumulate : (string * int * int * int) * string -> unit
  val reset_current : unit -> unit
  val typecheck_current : unit -> unit

  (* The ``quotation`` calling Elpi's elab predicate *)
  val quotation : string -> term

  (* Name of the predicate for the elaborator. *)
  val elab_predicate : string ref

  (* The ``elaborator`` calling Elpi's elab predicate *)
  (* NB. reload program automatically at each invocation *)
  val elaborate_preterm : preterm -> preterm

  (* The ``elaborator`` calling Elpi's elab predicate *)
  val elaborate_preterm_with : elpi_code -> preterm -> preterm

  val elaborate : preterm -> term

  (* Rule *)
  val prove : term -> thm

  (* Tactic *)
  val prove_tac : tactic

  val step : tactic

  (* calls cprover *)
  val search : term list -> term -> tactic

end = struct 

  unset_jrh_lexer;;

  open Elpi.API;;

  (* TODO: move to an utils module *)
  let readback_string ~depth t =
    match Elpi.API.RawData.look ~depth t with
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
      type t = string
      let compare x y = String.compare x y
      let pp fmt i = Format.fprintf fmt "%s" i
      let show x = x
    end)

    let stv = ref 0
    let incr_get r = incr r; "?" ^ string_of_int !r

    let record_uvar_Utv k state =
      State.update_return UV2STV.uvmap state (fun m ->
        try m, Utv (UV2STV.host k m)
        with Not_found ->
          let j = incr_get stv in
          UV2STV.add k j m, Utv j)

    let record_Utv_uvar k state =
      try state, RawData.mkUnifVar (UV2STV.elpi k (State.get UV2STV.uvmap state)) ~args:[] state, []
      with Not_found ->
        let state, flex = FlexibleData.Elpi.make state in
        let state = State.update UV2STV.uvmap state (UV2STV.add flex k) in
        state, RawData.mkUnifVar (UV2STV.elpi k (State.get UV2STV.uvmap state)) ~args:[] state, []

    let t = AlgebraicData.declare {
      ty = TyName "pretype";
      doc = "The algebraic data type of pretypes";
      pp = (fun fmt t -> Format.fprintf fmt "%s" (string_of_type (type_of_pretype t)));
      constructors = [
        K("uty","User type variable",A(BuiltInData.string,N),
           B (fun s -> Utv s),
           MS (fun ~ok ~ko -> function
             | (Utv s) -> fun state ->
                 if s.[0] = '?' && s.[1] != '?' then record_Utv_uvar s state
                 else ok s state
             | _ -> ko));
        K("ptycon","Type constructor",A(BuiltInData.string,C(ContextualConversion.(!>>) BuiltInData.list, N)),
           B (fun s l -> Ptycon(s,l)),
           M (fun ~ok ~ko -> function (Ptycon(s,l)) -> ok s l | _ -> ko ()));
        K("sty","System type variable",A(BuiltInData.int,N),
           B (fun i -> Stv i),
           M (fun ~ok ~ko -> function (Stv i) -> ok i | _ -> ko ()));
        K("uvar","",A(uvar,N),
           BS (fun (k,_) state -> record_uvar_Utv k state),         
           M (fun ~ok ~ko _ -> ko ()))
      ]
    } |> ContextualConversion.(!<)

  end

(* --------------------------------------------------------------------- *)

  module Hol_preterm : sig

    val t : preterm Conversion.t
    val elpi_string_of_preterm : preterm -> string

  end = struct

    open BuiltInPredicate;;
    let elpi_string_of_preterm x = string_of_term (unsafe_term_of_preterm x);;

    let t = AlgebraicData.declare {
      ty = TyName "preterm";
      doc = "The algebraic data type of preterms";
      pp = (fun fmt t -> Format.fprintf fmt "%s" (elpi_string_of_preterm t));
      constructors = [
        K("varp","Variable",A(BuiltInData.string,A(Hol_pretype.t,N)),
           B (fun s ty -> Varp(s,ty)),
           MS (fun ~ok ~ko -> function
              | Varp(s,ty) -> fun state ->
                  let len_s = String.length s in
                  if len_s > tag_len && String.sub s 0 tag_len = antiquotation_tag then
                    let text = String.sub s tag_len (len_s - tag_len) in
                    let state, t = Quotation.lp ~depth:0 (*TODO:wrong*) state Ast.(Loc.initial "(antiquot)") text in
                    state, t, []
                  else
                    ok s ty state
              | _ -> ko));
        K("constp","Constant",A(BuiltInData.string,A(Hol_pretype.t, N)),
           B (fun s ty -> Constp(s,ty)),
           M (fun ~ok ~ko -> function Constp(s,ty) -> ok s ty | _ -> ko ()));
        K("combp","Combination",S (S N),
           B (fun hd a -> Combp(hd,a)),
           M (fun ~ok ~ko -> function Combp(hd,a) -> ok hd a | _ -> ko ()));
        K("typing","Typing",S (A(Hol_pretype.t,N)),
           B (fun t ty -> Typing(t,ty)),
           M (fun ~ok ~ko -> function Typing(t,ty) -> ok t ty | _ -> ko ()));
        K("absp","Abstraction",S (S N),
           B (fun v b -> Absp(v,b)),
           M (fun ~ok ~ko -> function Absp(v,b) -> ok v b | _ -> ko ()));
      ]
    }  |> ContextualConversion.(!<)

  end

  module Cprover = struct

    let t_poly (individual : 'i Conversion.t) (formula : 'f Conversion.t)
        : ('i,'f) proof Conversion.t =
      AlgebraicData.declare {
        ty = TyApp ("prover.proof",individual.Conversion.ty,[formula.Conversion.ty]);
        doc = "The algebraic data type of first order proofs";
        pp = (fun fmt t -> Format.fprintf fmt "%s" "TODO");
        constructors = [
          K("prover.and_l","",A(formula,A(formula,S N)),
            B(fun a b x -> Pand_l (a,b,x)),
            M(fun ~ok ~ko -> function Pand_l(a,b,x) -> ok a b x | _ -> ko ()));
          K("prover.and_r","",S (S N),
            B(fun x y -> Pand_r(x,y)),
            M(fun ~ok ~ko -> function Pand_r(x,y) -> ok x y | _ -> ko ()));
          K("prover.or_l","",A(formula,A(formula,S(S N))),
            B(fun t1 t2 p1 p2 -> Por_l(t1,t2,p1,p2)),
            M(fun ~ok ~ko -> function Por_l(t1,t2,p1,p2) -> ok t1 t2 p1 p2 | _ -> ko ()));
          K("prover.or1_r","",S N,
            B(fun p -> Por1_r(p)),
            M(fun ~ok ~ko -> function Por1_r(p) -> ok p | _ -> ko ()));
          K("prover.or2_r","",S N,
            B(fun p -> Por2_r(p)),
            M(fun ~ok ~ko -> function Por2_r(p) -> ok p | _ -> ko ()));
          K("prover.orc_r","",S N,
            B(fun x -> Porc_r x),
            M(fun ~ok ~ko -> function Porc_r x -> ok x | _ -> ko ()));
          K("prover.ex-falso","",N,
            B(Pex_falso),
            M(fun ~ok ~ko -> function Pex_falso -> ok | _ -> ko ()));
          K("prover.initial","",A(formula,N),
            B(fun x -> Pinitial x),
            M(fun ~ok ~ko -> function Pinitial x -> ok x | _ -> ko ()));
          K("prover.imp_l","",A(formula,A(formula,S (S N))),
            B(fun t1 t2 p1 p2 -> Pimp_l(t1,t2,p1,p2)),
            M(fun ~ok ~ko -> function Pimp_l(t1,t2,p1,p2) -> ok t1 t2 p1 p2 | _ -> ko ()));
          K("prover.imp_r","",S N,
            B(fun p -> Pimp_r(p)),
            M(fun ~ok ~ko -> function Pimp_r(p) -> ok p | _ -> ko ()));
          K("prover.forall_l","",A(individual,A(formula,S N)),
            B(fun t1 t2 p -> Pforall_l(t1,t2,p)),
            M(fun ~ok ~ko -> function Pforall_l(t1,t2,p) -> ok t1 t2 p | _ -> ko ()));
          K("prover.nforall_r","",A(individual,A(formula,S N)),
            B(fun t1 t2 p -> Pforall_r(t1,t2,p)),
            M(fun ~ok ~ko -> function Pforall_r(t1,t2,p) -> ok t1 t2 p | _ -> ko ()));
          K("prover.nexists_l","",A(individual,A(formula,S N)),
            B(fun t1 t2 p -> Pexists_l(t1,t2,p)),
            M(fun ~ok ~ko -> function Pexists_l(t1,t2,p) -> ok t1 t2 p | _ -> ko ()));
          K("prover.exists_r","",A(individual,S N),
            B(fun t p -> Pexists_r(t,p)),
            M(fun ~ok ~ko -> function Pexists_r(t,p) -> ok t p | _ -> ko ()));
        ]
      }  |> ContextualConversion.(!<)

    let t = t_poly Hol_preterm.t Hol_preterm.t

  end
  
  (* ========================== quotations ========================== *)

  let () = Quotation.set_default_quotation (fun ~depth st loc txt ->
    let ast = parse_term txt in
    let ast = preterm_of_term ast in
    let st, t, l = Hol_preterm.t.Conversion.embed ~depth st ast in
    assert (l = []);
    st, t)
  ;;

  let () = Quotation.register_named_quotation "raw" (fun ~depth st loc txt ->
    let ast, l = parse_preterm (lex (explode txt)) in
    if l <> [] then failwith "Unparsed input in quotation";
    let st, t, l = Hol_preterm.t.Conversion.embed ~depth st ast in
    assert (l = []);
    st, t)
  ;;

  let () = Quotation.register_named_quotation "" (fun ~depth st loc txt ->
    let ty = parse_type txt in
    let st, t, l = Hol_pretype.t.Conversion.embed ~depth st (pretype_of_type ty) in
    assert (l = []);
    st, t)
  ;;


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
    }  |> ContextualConversion.(!<)

    let goal = AlgebraicData.declare {
      ty = TyName "goal";
      doc = "HOL-light goal";
      pp = (fun fmt h -> Format.fprintf fmt "TODO:goal");
      constructors = [
        K("goal","",A(BuiltInData.list hyp,A(Hol_preterm.t,N)),
          B (fun h c -> Goal(h,c)),
          M (fun ~ok ~ko:_ -> function Goal(h,c) -> ok h c));
      ]
    }  |> ContextualConversion.(!<)

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
    }  |> ContextualConversion.(!<)

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

  module Builtins = struct

    open BuiltInPredicate;;
    open Notation;;
    open BuiltIn;;

    let pretype_of_type2 t =
      let t = pretype_of_type t in
      let rec aux = function
        | Utv s  as x ->
           if s.[0] = '?' then Utv ("?" ^ s) else x
        | Stv _ as x -> x
        | Ptycon(s,tl) -> Ptycon(s,List.map aux tl) in
      aux t

    let declarations = [
      LPDoc "========================== HOL-Light ===========================";

      MLData Hol_pretype.t;
      MLData Hol_preterm.t;

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
           !: (pretype_of_type2 ty)
         with Failure _ -> raise No_clause)),
      DocNext);

      (* TODO:
        - get_var_type (poco usato, per studenti?) *)

      MLCode (Pred("hol.skeleton",
        In(BuiltInData.string,"constant overloaded name",
        Out(Hol_pretype.t,"skeleton type",
        Easy "lookup the list of skeletons of overloaded constants")),
      (fun name _ ~depth ->
         try let ty = assoc name !the_overload_skeletons in
             !: (pretype_of_type2 ty)
         with Failure _ -> raise No_clause)),
      DocNext);

      MLCode (Pred("hol.interface",
        In(BuiltInData.string,"constant overloaded name",
        Out(BuiltInData.list (Elpi.Builtin.pair BuiltInData.string Hol_pretype.t), "constant name and type",
        Easy("lookup the interpretations of overloaded constant"))),
      (fun name _ ~depth ->
         let l = mapfilter (fun (x,(s,t)) ->
                 if x = name then s, pretype_of_type2 t
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

      MLCode (Pred("hol.coercions",
        Out(BuiltInData.list (Elpi.Builtin.pair BuiltInData.string Hol_pretype.t), "coercions",
        Easy("Fetches the list of coercions")),
      (fun _ ~depth ->
         !: (map (fun (s,(ty,_)) -> s, pretype_of_type2 ty) !the_coercions))),
      DocNext);

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

      (*
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
      DocAbove);

      LPDoc "-------------------- cprover ----------------------------";

      MLData (Cprover.t_poly (BuiltInData.poly "I") (BuiltInData.poly "A"));

    ];;

  end

  (* Elpi initialization. header holds the contents of hol-builtin.elpi,
     that is Elpi's standard predicates plus the ones in the Builtins module
     above *)
  let header, _ =
    let elpi_flags =
      try
        let ic, _ as p = Unix.open_process "ocamlfind query elpi 2>/dev/null" in
        let w = input_line ic in
        let _ = Unix.close_process p in ["-I";w]
      with _ -> [] in
    Setup.set_error (fun ?loc:_ s -> failwith ("Elpi: " ^ s));
    Setup.set_anomaly (fun ?loc:_ s -> failwith ("Elpi: anomaly: " ^ s));
    Setup.set_type_error (fun ?loc:_ s -> failwith ("Elpi: type error: " ^ s));
    let builtins_doc_file = "elpi/hol-builtin.elpi" in
    let builtins = Elpi.Builtin.std_declarations @ Builtins.declarations in
    let fmt = Format.formatter_of_out_channel (open_out builtins_doc_file) in
    BuiltIn.document fmt builtins;
    Setup.init
      ~builtins:(BuiltIn.declare ~file_name:builtins_doc_file builtins)
      ~basedir:(Sys.getcwd ()) elpi_flags
  ;;

  type elpi_code = Elpi.API.Compile.program

  let parse_files fl =
    try
      Parse.program fl
    with Parse.ParseError(loc,msg) ->
      failwith ("elpi: " ^ Elpi.API.Ast.Loc.show loc ^ ": " ^ msg)
  ;;

  let parse_string ((file,lnum,cnum,enum),s) =
    try
      let loc = { Ast.Loc.source_name = file; line = lnum; line_starts_at = enum; source_start = cnum; source_stop = cnum } in
      Parse.program_from_stream loc (Stream.of_string s)
    with Parse.ParseError(loc,msg) ->
      failwith ("elpi: " ^ Elpi.API.Ast.Loc.show loc ^ ": " ^ msg)
  ;;

  let compile_ast pl : elpi_code =
      Compile.program ~flags:Compile.default_flags header pl
  ;;

  let hol_files =
    [ "elpi/verbosity.elpi"
        ; "elpi/test.elpi"
        ; "elpi/pre_hol.elpi"
    (*    ; "elpi/elab.elpi" *)
        ; "elpi/infer.elpi"
    (*    ; "elpi/algebra.elpi"
        ; "elpi/cprover.elpi"
        ; "elpi/hol.elpi" *)
        ];;

  let hol () = compile_ast [parse_files hol_files]
    
  let extra_code = ref []

  let accumulate loc_text =
    extra_code := !extra_code @ [loc_text]

  let reset_current () = extra_code := []

  let current () =
    compile_ast (parse_files hol_files :: List.map parse_string !extra_code)

  let compile_files fl = compile_ast [parse_files fl]

  type debug = On of string list | Off

  let debugging = ref Off

  let debug = function
   | On preds ->
      let std_opts = [
        "-trace-on";"-trace-at";"run";"1";"999999";
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
    if not (Compile.static_check h ~checker:[Parse.program ["elpi/elpi-checker.elpi"]] q) then
      failwith "elpi: type error"
  ;;

  let typecheck_current () =
    let q = Parse.goal (Ast.Loc.initial "(query)") "true" in
    let q = Compile.query (current ()) q in
    let are_we_debugging = !debugging in
    Setup.trace [];
    ignore(static_check header q);
    debug are_we_debugging

  let run_text ?max_steps program query =
    let q = Parse.goal (Ast.Loc.initial "(query)") query in
    let q = Compile.query program q in
    let exe = Compile.link q in
    static_check header q;
    match Execute.once ?max_steps exe with
    | Execute.Success { assignments = assignments; pp_ctx = pp_ctx } ->
        if not (Data.StrMap.is_empty assignments) then
        Format.printf "Assignments: %a\n"
          (Data.StrMap.pp Pp.(term pp_ctx)) assignments
    | Failure ->
        Format.printf "Failure\n"
    | NoMoreSteps ->
        Format.printf "Timeout\n"
  ;;

  let run_predicate ?(typecheck=true) ?max_steps program query =
    let q = Query.compile program (Ast.Loc.initial "(run_predicate)") query in

    (* We disable traces when we typecheck the elpi code (Elpi's type checker
       is an elpi program too) *)
    let are_we_debugging = !debugging in
    Setup.trace [];
    if typecheck then
      ignore(static_check header q);
    debug are_we_debugging;

    let exe = Compile.link q in
    match Execute.once exe with
    | Execute.Success s -> s.output
    | Failure -> failwith "elpi finds no solution"
    | NoMoreSteps -> assert false
  ;;

  (* ================================================================ *)
  (* Entry points to call elpi code *)

  let query ?max_steps ?(code=current ()) s = run_text ?max_steps code s;;

  let typecheck ?(code=current ()) () =
    let q = Parse.goal (Ast.Loc.initial "(query)") "true" in
    let q = Compile.query code q in
    static_check header q

  let print2html ?(code=current ()) () =
    let q = Parse.goal (Ast.Loc.initial "(query)") "true" in
    let q = Compile.query code q in
    let quotedP, _  = Quotation.quote_syntax q in
    let printer = compile_files ["elpi2html.elpi"] in
    run_predicate ~typecheck:false printer
      (Query.Query {
        predicate = "main-quoted";
        arguments = D(BuiltInData.list BuiltInData.any,quotedP,
                    D(BuiltInData.string,"elpi/index.html",
                    D(BuiltInData.list BuiltInData.string,[], (* blacklist *)
                    N))) })


  let prove concl =
    let x, _ = run_predicate (current ())
      (Query.Query {
        predicate = "prove";
        arguments = D(Hol_preterm.t,preterm_of_term concl,
                    Q(Thm.t,"P",
                    N)) })
    in
    x
  ;;

  let step (goal : goal) : goalstate =
    let goals, (just, _) = run_predicate (current ())
      (Query.Query {
        predicate = "step";
        arguments = D(Tactics.goal,Tactics.holg2elpig goal,
                    Q(BuiltInData.list Tactics.goal,"Goals",
                    Q(Tactics.justification,"Just",
                    N))) })
    in
    null_meta, List.map Tactics.elpig2holg goals, (fun _ -> Tactics.interp_j just)
  ;;

  let elab_predicate = ref "elaborate";;

  (* This runs the elpi query requesting the elaboration of a given term *)
  let elaborate_preterm p =
    let elab_p, _ = run_predicate ~typecheck:false (current ())
      (Query.Query {
        predicate = !elab_predicate;
        arguments = D(Hol_preterm.t,p,
                    Q(Hol_preterm.t,"Elab_p",
                    N)) })
    in
    elab_p
  ;;

  let elaborate_preterm_with program p =
    let elab_p, _ = run_predicate ~typecheck:false program
      (Query.Query {
        predicate = !elab_predicate;
        arguments = D(Hol_preterm.t,p,
                    Q(Hol_preterm.t,"Elab_p",
                    N)) })
    in
    elab_p
  ;;

  let elaborate p =
    term_of_preterm (elaborate_preterm p);;

  let quotation s =
    let p, l = parse_preterm (lex (explode s)) in
    if l <> [] then failwith "Unparsed input"
    else elaborate p
  ;;

  let search hyps concl =
    let proof, () = run_predicate ~typecheck:false (current ())
      (Query.Query {
        predicate = "search";
        arguments = D(BuiltInData.list Hol_preterm.t,List.map preterm_of_term hyps,
                    D(Hol_preterm.t,preterm_of_term concl,
                    Q(Cprover.t,"P",
                    N))) })
    in
      pcheck proof            
  ;;

  set_jrh_lexer;;

  let prove_tac = CONV_TAC prove

end

(* little test *)
(*
let () = Hol_elpi.(query "main");;
let () = Hol_elpi.(query "hol2prover {{ a /\ b ==> c \/ !x:A. x = x ==> ?y:A. x = y /\ F  }} P");;
let _ : thm = prove (`0 = 0`, Hol_elpi.prove_tac)
*)
Hol_elpi.typecheck ();;
