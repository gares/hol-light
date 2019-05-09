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

  let tyvarc = Constants.from_stringc "tyvar";;
  let tyappc = Constants.from_stringc "tyapp";;

  let mk_tyvar s = mkApp tyvarc (of_string s) [];;
  let mk_tyapp s l = mkApp tyappc (of_string s) [list_to_lp_list l];; 

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

  let readback_string ~depth t =
    match look ~depth t with
    | CData c when is_string c -> to_string c
    | _ -> type_error "readback_string"
  ;;

  let rec embed_prety ~depth t =
    match t with
    | Ptycon(s,tl) -> mk_tyapp s (List.map (embed_prety ~depth) tl) 
    | Utv s -> mk_tyvar s
    | Stv _ -> assert false
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

  let readback_prety ~depth state t =
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
      | App(c, s, [l]) when c == tyappc ->
          Ptycon(readback_string ~depth s,
                 List.map aux (lp_list_to_list ~depth l))
      | App(c, s, []) when c == tyvarc -> Utv(readback_string ~depth s)
      | Discard -> new_Stv depth
      | (UVar(r,lvl,_) | AppUVar(r,lvl,_)) -> find_Stv r lvl (* NO args? *)
      | _ -> type_error ("readback_prety: " ^ E.Pp.Raw.show_term t)
    in
    let t = aux t in
    !state, t
  ;;

  let monoc = Constants.from_stringc "mono"
  let allc = Constants.from_stringc "all"

  let rec position ~depth x = function
    | [] -> failwith (x ^ " is a free variable")
    | y :: rest when x = y -> List.length rest + depth
    | _ :: xs -> position ~depth x xs
  ;;

  let embed_prety_schema ~depth (vars, ty) =
    let vars = List.map dest_vartype vars in
    let rec embed_mono = function
      | Tyapp(s,l) -> mk_tyapp s (List.map embed_mono l)
      | Tyvar x -> mkConst (position ~depth x vars)
    in
    let rec embed_all = function
      | [] -> mkApp monoc (embed_mono ty) []
      | _ :: xs -> mkApp allc (mkLam (embed_all xs)) []
    in
      embed_all (List.rev vars)
  ;;

  let readback_prety_schema ~depth t =
    let rec readback_mono ~depth subst t =
      match look ~depth t with
      | App(c,s,[args]) when c == tyappc ->
          mk_type (readback_string ~depth s,
                   List.map (readback_mono ~depth subst) (E.Utils.lp_list_to_list ~depth args))
      | App(c,s,[]) when c == tyvarc -> assert false
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
          | _ -> type_error "readback_prety_schema"
          end
      | _ -> type_error "readback_prety_schema"
    in
      readback_all ~depth [] t
  ;;


  let rec embed_preterm ~depth t =
    match t with
    | Varp(s,ty) -> mk_var s (embed_prety ~depth ty)
    | Constp (s,ty) -> mk_const s (embed_prety ~depth ty)
    | Combp(t1,t2) -> mk_app (embed_preterm ~depth t1) (embed_preterm ~depth t2)
    | Absp(t1,t2) -> mk_lam (embed_preterm ~depth t1) (embed_preterm ~depth t2)
    | Typing(t,ty) -> mk_typing (embed_preterm ~depth t) (embed_prety ~depth ty)
  ;;

  let rec readback_preterm ~depth state t =
    match look ~depth t with
    | App(c,s,[ty]) when c == varc ->
        let state, ty = readback_prety ~depth state ty in
        state, Varp(readback_string ~depth s,ty)
    | App(c,s,[ty]) when c == constc ->
        let state, ty = readback_prety ~depth state ty in
        state, Constp(readback_string ~depth s,ty)
    | App(c,t1,[t2]) when c == appc ->
        let state, t1 = readback_preterm ~depth state t1 in
        let state, t2 = readback_preterm ~depth state t2 in
        state, Combp(t1, t2)
    | App(c,t1,[t2]) when c == lamc ->
        let state, t1 = readback_preterm ~depth state t1 in
        let state, t2 = readback_preterm ~depth state t2 in
        state, Absp(t1, t2)
    | App(c,_,_) when c == typingc ->
        assert false
    | _ -> type_error ("readback_preterm: " ^ E.Pp.Raw.show_term t)
  ;;

(*

  let embed_type ~depth (vars,ty) =
    let rec embedtyexpr ctx = function
      | Hol.Tyapp(name,args) ->
          mkApp tyappc (of_string name)
            [list_to_lp_list (List.map (embedtyexpr ctx) args)]
      | Tyvar s -> mkConst (position ~depth s ctx)
    in
    let rec embedty ctx = function
      | [] -> mkApp tymonoc (embedtyexpr ctx ty) []
      | Tyvar v :: vs -> mkApp tyallc (mkLam (embedty (v :: ctx) vs)) [] 
      | _ -> assert false
    in 
      embedty [] vars
  ;;

  let rec readback_type ~depth t =
    match look ~depth t with
    | App(c,hd,args) when c == tyappc ->
        Hol.mk_type (readback_string ~depth hd,
                     List.map (readback_type ~depth) args)
    | _ -> type_error ("readback_type:" ^ E.Pp.Raw.show_term t)
  ;;

  let embed_term ~depth ctx t =
    let rec embed ctx = function
      | Hol.Var(s,_) -> mkConst (position ~depth s ctx)
      | Const(s,ty) ->
         mkApp constantc (of_string s) [embed_type ~depth (tyvars ty, ty);mkNil]
      | Comb(t1,t2) -> mkApp applicationc (embed ctx t1) [embed ctx t2]
      | Abs(Var(s,ty),bo) ->
          let ty = embed_type ~depth (tyvars ty, ty) in
          let bo = embed (s :: ctx) bo in
          mkApp lambdac (of_string s) [ty; mkLam bo]
      | _ -> failwith "invalid hol term"
    in
      embed ctx t
  ;;

  let readback_term ~depth hyps { E.Data.state = s } t =
    let rec readback ~depth ctx t =
      match look ~depth t with
      | App(c,hd,[ty;subst]) when c == constantc ->
          let hd = readback_string ~depth hd in
          assert false
(*           let ty = readback_type ~depth ty in *)
(*           mk_const (hd,ty) *)
      | App(c,hd,[a]) when c == applicationc ->
          let hd = readback ~depth ctx hd in
          let a = readback ~depth ctx a in
          mk_comb (hd,a)
      | App(c,n,[ty;bo]) when c == lambdac ->
          let n = readback_string ~depth n in
(*           let ty = readback_type ~depth ty in *)
    let ty = assert false in
          begin match look ~depth bo with
          | Lam t ->
              let v = mk_var (n,ty) in
              mk_abs (v, readback ~depth:(depth+1) ((depth,v)::ctx) t)
          | _ -> assert false
          end
      | Const i -> (try List.assoc i ctx with Not_found -> assert false)
      | _ -> assert false
    in
      s, readback ~depth [] t
  ;;

  let embed_pretype ~depth ty =
    let rec embedty = function
      | Ptycon("",[]) -> tydummy
      | Ptycon(name,args) ->
          mkApp tyappc (of_string name)
            [list_to_lp_list (List.map embedty args)]
      | Utv name -> assert false (* TODO *)
      | Stv _ -> assert false
    in
      embedty ty
  ;;

(*
  let embed_preterm ~depth t =
    let rec embed ctx = function
      | Varp(s,_) when can get_generic_type s ->
          mkApp constantc (of_string s) [tydummy]
      | Varp(s,_) when can num_of_string s ->
          let t = pmk_numeral(num_of_string s) in
          embed ctx t
      | Varp(s,_) -> mkConst (position ~depth s ctx) (* make a cast? *)
      | Constp(s,ty) -> mkApp constantc (of_string s) [embed_pretype ~depth ty;mkNil]
      | Combp(t1,t2) -> mkApp applicationc (embed ctx t1) [embed ctx t2]
      | Absp(Varp(s,ty),bo) -> 
          let ty = embed_pretype ~depth ty in
          let bo = embed (s :: ctx) bo in
          mkApp lambdac (of_string s) [ty;mkLam bo]
      | Typing(t,ty) ->
          let t = embed ctx t in
          let ty = embed_pretype ~depth ty in
          mkApp pcastc t [ty]
      | _ -> failwith "invalid hol preterm"
    in
      embed [] t
  ;;
*)
  let embed_preterm ~depth t =
    let rec embed = function
      | Varp(s,_) ->
      | Combp(t1,t2) ->
          mkApp 
      | Absp(t1,t2) ->
      | Typing(t,ty) ->

  (* Proof evidence, non-structured data (such as string, int, ...) *)
  let thm_cd = E.CData.declare { E.CData.data_name = "Hol.thm";
    data_pp = (fun f t -> Format.fprintf f "<<proof-of %a >>" pp_print_thm t);
    data_eq = equals_thm;
    data_hash = Hashtbl.hash;
    data_hconsed = false;
  }
  ;;

  let () = E.Compile.set_default_quotation (fun ~depth st s ->
    st, embed_term ~depth [] (parse_term s))
  ;;

  let () = E.Compile.register_named_quotation "" (fun ~depth st s ->
    let ty = parse_type s in
    let vars = tyvars ty in
    st, embed_type ~depth (vars,ty))
  ;;

  let () = E.Compile.register_named_quotation "pre" (fun ~depth st s ->
    let p, l = parse_preterm (lex (explode s)) in
    if l = [] then st, embed_preterm ~depth p
    else failwith "Unparsed input")
  ;;

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

  let hol_pretype : pretype data = {
    ty = TyName "ty";
    doc = "Preterm.pretype";
    embed = (fun ~depth _ { E.Data.state = s } ty ->
      s, embed_prety ~depth:0 ty, []);
    readback = (fun ~depth _ { E.Data.state = s } ty ->
      readback_prety ~depth s ty);
  }

  let hol_pretype_schema : hol_type data = {
    ty = TyName "tys";
    doc = "Fusion.Hol.hol_type";
    embed = (fun ~depth _ { E.Data.state = s } ty ->
      s, embed_prety_schema ~depth:0 (tyvars ty,ty), []);
    readback = (fun ~depth _ { E.Data.state = s } ty ->
      s, readback_prety_schema ~depth ty);
  }

  let hol_preterm : preterm data = {
    ty = TyName "term";
    doc = "Preterm.preterm";
    embed = (fun ~depth _ { E.Data.state = s } t ->
      s, embed_preterm ~depth t, []);
    readback = (fun ~depth _ { E.Data.state = s } t ->
      readback_preterm ~depth s t);
  }


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
      Out(hol_pretype_schema, "constant type",
      Easy("lookup the type of known constant"))),
    (fun name _ ~depth:_ ->
       try !: (get_const_type name)
       with Failure _ -> raise No_clause)),
    DocNext);

    MLCode (Pred("hol.interface",
      In(string,"constant overloaded name",
      Out(list (Elpi_builtin.pair string hol_pretype), "constant name and type",
      Easy("lookup the interpretations of overloaded constant"))),
    (fun name _ ~depth ->
       let l = mapfilter (fun (x,(s,t)) ->
               if x = name then s, pretype_of_type t
               else fail()) !the_interface in
        !: l)),
    DocNext);

    MLCode (Pred("hol.pmk_numeral",
      In(string,"possibly a numeral",
      Out(hol_preterm,"the number",
      Easy "when the given string is a numeral it outputs its preterm")),
    (fun str _ ~depth ->
       if can num_of_string str then !: (pmk_numeral (num_of_string str))
       else raise No_clause)),
    DocNext);

    LPDoc "-------------------- printing -----------------------------";

    MLCode (Pred("hol.term->string",
      In(hol_preterm,"T",
      Out(string,"S",
      Easy "typechecks T and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (string_of_term (term_of_preterm t))
       with Failure _ -> !: "(illtyped)")),
    DocAbove);

    MLCode (Pred("hol.ty->string",
      In(hol_pretype,"Ty",
      Out(string,"S",
      Easy "typechecks Ty and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (string_of_type (type_of_pretype t))
       with Failure _ -> !: "(illtyped)")),
    DocAbove);

    MLCode (Pred("hol.tys->string",
      In(hol_pretype_schema,"Tys",
      Out(string,"S",
      Easy "typechecks Tys and prints it to S")),
    (fun t _ ~depth ->
       try
         !: (string_of_type t)
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
      let t = embed_preterm ~depth p in
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
        snd (readback_preterm ~depth:0 s t)
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
