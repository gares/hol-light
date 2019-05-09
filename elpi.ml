#use "topfind";;
#require "elpi";;
needs "parser.ml";;

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
  val quotation : string -> preterm
        
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
   are also take and return a E.CustomState.t. We use that to store a mapping
   between Elpi's unification variables and HOL-light Stv, for example.
   
*)

(* --------------------------------------------------------------------- *)

  module Hol_pretype : sig

    val t : pretype E.BuiltInPredicate.data

    (* This API is used by Hol_preterm and Hol_type_schema *)
    module Internal : sig
      val embed : depth:int -> pretype -> E.Data.term
      val readback :
        depth:int -> E.CustomState.t -> E.Data.term -> E.CustomState.t * pretype
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

  let rec embed ~depth t =
    match t with
    | Ptycon(s,tl) -> mk_app s (List.map (embed ~depth) tl) 
    | Utv s -> mk_var s
    | Stv _ -> assert false (* Why? *)
  ;;

  (* State component mapping elpi unification variables to HOL-light's 
    invented (system) type variables *)
  let invented_tyvars =
    E.CustomState.declare ~name:"invented-tyvars"
      ~pp:(fun f (_,l) ->
        let pp_elem fmt (ub,(lvl,stvno)) =
          Format.fprintf fmt "(%a,%d)"
            (E.Pp.term lvl) (mkUVar ub lvl 0)
            stvno in
        Format.fprintf f "%a" (E.Pp.list pp_elem ";") l)
      ~init:(E.CustomState.Other(fun () -> -1, []))
  ;;

  let readback ~depth state t =
    let state = ref state in
    let new_Stv ?(r=fresh_uvar_body ()) lvl =
      let s, t = E.CustomState.update_return invented_tyvars !state
        (fun (no,vars) -> (no-1, (r,(lvl,no)):: vars), Stv no) in
      state := s;
      t
      in
    let find_Stv r lvl =
      try
        let _, vars = E.CustomState.get invented_tyvars !state in
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
    embed = (fun ~depth _ { E.Data.state = s } ty ->
      s, embed ~depth:0 ty, []);
    readback = (fun ~depth _ { E.Data.state = s } ty ->
      readback ~depth s ty);
  }

  end include Internal end

(* --------------------------------------------------------------------- *)
  module Hol_preterm : sig

    val t : preterm E.BuiltInPredicate.data

    (* API used to generate the query `elab` *)
    module Internal : sig
      val embed : depth:int -> preterm -> E.Data.term
    end

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


  let rec embed ~depth t =
    match t with
    | Varp(s,ty) -> mk_var s (Hol_pretype.Internal.embed ~depth ty)
    | Constp (s,ty) -> mk_const s (Hol_pretype.Internal.embed ~depth ty)
    | Combp(t1,t2) -> mk_app (embed ~depth t1) (embed ~depth t2)
    | Absp(t1,t2) -> mk_lam (embed ~depth t1) (embed ~depth t2)
    | Typing(t,ty) -> mk_typing (embed ~depth t) (Hol_pretype.Internal.embed ~depth ty)
  ;;

  let rec readback ~depth state t =
    match look ~depth t with
    | App(c,s,[ty]) when c == varc ->
        let state, ty = Hol_pretype.Internal.readback ~depth state ty in
        state, Varp(readback_string ~depth s,ty)
    | App(c,s,[ty]) when c == constc ->
        let state, ty = Hol_pretype.Internal.readback ~depth state ty in
        state, Constp(readback_string ~depth s,ty)
    | App(c,t1,[t2]) when c == appc ->
        let state, t1 = readback ~depth state t1 in
        let state, t2 = readback ~depth state t2 in
        state, Combp(t1, t2)
    | App(c,t1,[t2]) when c == lamc ->
        let state, t1 = readback ~depth state t1 in
        let state, t2 = readback ~depth state t2 in
        state, Absp(t1, t2)
    | App(c,_,_) when c == typingc ->
        assert false
    | _ -> type_error ("readback_preterm: " ^ E.Pp.Raw.show_term t)
  ;;

  open E.BuiltInPredicate;;

  let t : preterm data = {
    ty = TyName "term";
    doc = "Preterm.preterm";
    embed = (fun ~depth _ { E.Data.state = s } t ->
      s, embed ~depth t, []);
    readback = (fun ~depth _ { E.Data.state = s } t ->
      readback ~depth s t);
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
    embed = (fun ~depth _ { E.Data.state = s } (vars,ty) ->
      s, embed ~depth:0 vars ty, []);
    readback = (fun ~depth _ { E.Data.state = s } ty ->
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

  (* This problem in the API is to be fixed in elpi *)
  let hack_elpi_12 f s x =
    let _, t, l = f { E.Data.assignments = StrMap.empty; state = Obj.magic StrMap.empty; constraints = Obj.magic [] } x in
    assert(l = []);
    s, t

  let () = E.Compile.set_default_quotation (fun ~depth st loc txt ->
    let ast, l = parse_preterm (lex (explode txt)) in
    if l <> [] then failwith "Unparsed input in quotation";
    hack_elpi_12 (Hol_preterm.t.embed ~depth []) st ast)
  ;;

  let () = E.Compile.register_named_quotation "" (fun ~depth st loc txt ->
    let ty = parse_type txt in
    let vars = tyvars ty in
    hack_elpi_12 (Hol_type_schema.t.embed ~depth []) st (vars,ty))
  ;;

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
         !: (string_of_term (term_of_preterm t))
       with Failure _ -> !: "(illtyped)")),
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
        Format.printf "Assignments: %a\n"
          (Data.StrMap.pp Pp.term) assignments
    | Failure ->
        Format.printf "Failure\n"
    | NoMoreSteps ->
        Format.printf "Timeout\n"
  ;;

  (* we store in the state the name of the query argument standing for
     the elaborated term (the output of the elaboration) *)
  let elab_cc =
    E.Compile.State.declare ~name:"elab-out" ~init:(fun () -> "")
      ~pp:(fun f s -> Format.fprintf f "%s" s)
  ;;
  let elab_st =
    E.CustomState.declare ~name:"elab-out"
      ~pp:(fun f s -> Format.fprintf f "%s" s)
      ~init:(E.CustomState.CompilerState(elab_cc,fun x -> x))
  ;;

  (* This is the entry point predicate for calling the elaborator *)
  let elabc = E.Data.Constants.from_stringc "elab" ;;

  (* This runs the elpi query requesting the elaboration of a given term *)
  let elaborate p =
    let q = E.Compile.query (hol ()) (fun ~depth st ->
      let t = Hol_preterm.Internal.embed ~depth p in
      let st, n, x = E.Compile.fresh_Arg st ~name_hint:"E" ~args:[] in
      let st = E.Compile.State.set elab_cc st n in
      st, (Ast.Loc.initial "(quotation)",mkApp elabc t [x])) in

    (* We disable traces when we typecheck the elpi code (Elpi's type checker
       is an elpi program too) *)
    let are_we_debugging = !debugging in
    Setup.trace [];
    let _ = Compile.static_check header q in
    debug are_we_debugging;

    let exe = Compile.link q in

    match Execute.once exe with
    | Execute.Success sol ->
        let { state = s; assignments = a } as sol = E.Data.of_solution sol in
        let x = E.CustomState.get elab_st s in
        let t = Data.StrMap.find x a in
        snd (Hol_preterm.t.readback ~depth:0 [] sol t)
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

  set_jrh_lexer;;

end

(* little test *)
let () = Elpi.query (Elpi.hol ()) "self-test";;
