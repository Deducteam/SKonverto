open Core
open! Lplib
open Term
open Timed

exception Not_Proof of term
exception Not_ProofS of term

(** Builtin configuration. *)
type config =
  { symb_Skolem     : sym
  ; symb_Axiom      : sym
  ; symb_Formula    : sym
  ; symb_imp        : sym
  ; symb_forall     : sym
  ; symb_exists     : sym
  ; symb_tau        : sym
  ; symb_bot        : sym
  ; symb_proof      : sym }

(** [get_config sign] build the configuration using [sign]. *)
let get_config : Sign.t -> config = fun sign ->
  let fol_sig = Common.Path.(Map.find (of_string "logic.fol")) !Sign.loaded in
  let zen_sig = Common.Path.(Map.find (of_string "logic.zen")) !Sign.loaded in
  let builtin name = Extra.StrMap.find name !(sign.sign_builtins) in
  { symb_Skolem     = builtin "Skolem" 
  ; symb_Axiom      = builtin "Axiom" 
  ; symb_Formula    = builtin "Formula" 
  ; symb_imp        = builtin "imp"  
  ; symb_forall     = Sign.find fol_sig "∀" (* DISCUSS *)
  ; symb_exists     = Sign.find fol_sig "∃" (* DISCUSS *)
  ; symb_tau        = Sign.find zen_sig "τ" (* DISCUSS *)
  ; symb_proof      = builtin "proof" 
  ; symb_bot        = Sign.find fol_sig "⊥" (* DISCUSS *) }

(** [subst_inv fu x t] replaces all the subterms [fu] by [x] in the term [t]. *)
let subst_inv : term -> tvar -> term -> term = fun fu x ->
  let rec subst t =
    if Eval.eq_modulo [] t fu then mk_Vari x else
    match unfold t with
    | Vari _
    | Type
    | Kind
    | Symb _ -> t
    | Prod(a, b) ->
        let (v, b) = Bindlib.unbind b in
        let sa = subst a in
        let sb = Bindlib.bind_var v (lift (subst b)) in
        mk_Prod (sa, Bindlib.unbox sb)
    | Abst(a, b) ->
        let (v, b) = Bindlib.unbind b in
        let sa = subst a in
        let sb = Bindlib.bind_var v (lift (subst b)) in
        mk_Abst (sa, Bindlib.unbox sb)
    | Appl(a, b) -> mk_Appl (subst a, subst b)
    | Meta _
    | Patt _
    | TEnv _
    | Wild
    | LLet _
    | TRef _ -> assert false (* is not handled in the encoding. *)
  in subst

(** [frozen l t] checks if a term [t] contains one of the variables of [l]. *)
let frozen : tvar list -> term -> bool = fun l t ->
    let lifted_t = lift t in
    (* check if all elements of [l] do not occur in [t]. *)
    List.for_all (fun x -> not (Bindlib.occur x lifted_t)) l

(** [skolem_args f l t] returns all the arguments of subterms of [t] that have 
    the skolem symbols [f] as the head of the term. *)
let rec skolem_args : sym -> tvar list  -> term list list -> term 
    -> term list list = fun f vlist l t  ->
    match unfold t with
    | Vari _
    | Type
    | Kind -> l
    | Symb _ ->
        (* check if the current term [t] is the symbol [f]. *)
        if Eval.eq_modulo [] t (mk_Symb f) then
            (* and if we already have the empty argument list. *)
            if List.exists (fun x -> x = []) l then
                (* then return the previous list. *)
                l
            else
                (* otherwise we add the empty argument list to the result. *)
                []::l
        (* check if the current term [t] is not [f] then return the same result. 
            *)
        else
            l
    | Prod(a, b) ->
        let (x, b) = Bindlib.unbind b in
        (* get the arguments of [f] that appear in [a]. *)
        let l = skolem_args f vlist l a in
        (* get the arguments of [f] that appear in [b] and could not contain
            the variable [x]. *)
        skolem_args f (x::vlist) l b
    | Abst(a, b) ->
        let (x, b) = Bindlib.unbind b in
        (* get the arguments of [f] that appear in [a]. *)
        let l = skolem_args f vlist l a in
        (* get the arguments of [f] that appear in [b] and could not contain
            the variable [x]. *)
        skolem_args f (x::vlist) l b
    | Appl(_, _) ->
        let (h, args) = Term.get_args t in
        (* get the arguments of [f] that appear in every argument of [t]. *)
        let args_set = List.fold_left (skolem_args f vlist) l args in
        (* check if the head symbol of [t] is [f]. *)
        if Eval.eq_modulo [] h (mk_Symb f) then
            begin
                (* check if [args] is already in [args_set]. *)
                if List.exists (List.for_all2 (Eval.eq_modulo []) args) args_set
                    (* or [t] is not f-frozen. *)
                    || not (frozen vlist t) then
                    args_set
                else
                    (* add the arguments of [t] to the result. *)
                    args::args_set
            end
        (* otherwise we build the new set of arguments the term [h]. *)
        else
            skolem_args f vlist args_set h
    | Meta _ -> assert false
    | Patt _ -> assert false
    | TEnv _ -> assert false
    | Wild   -> assert false
    | LLet _ -> assert false
    | TRef _ -> assert false (* is not handled in the encoding. *)

(** [size t] return the size of the term [t]. *)
let rec size : term -> int = fun t ->
  List.fold_right (fun a l -> size a + l) (Term.get_args t |> snd) 1

(** [size_args f args] return the size of the term [f a0 a1 ... an] where args
    = [a0; a1; ...; an]. *)
let size_args : sym -> term list -> int = fun f args ->
    size (Term.add_args (mk_Symb f) args)

(** [subst_var x m n] substitutes the variable [x] with the term [n] inside the
    term [m].*)
let subst_var : tvar -> term -> term -> term = fun x m n ->
    Bindlib.subst (Bindlib.unbox (Bindlib.bind_var x (lift m))) n

(** [subst_mvar xs t ts] returns the term [t] with the variables of [xs] 
    replaced by [ts] (with length(xs) = length(ts)). *)
let subst_mvar : tvar list -> term -> term list -> term = fun xs t ts ->
    let xs = Array.of_list xs in
    let ts = Array.of_list ts in
    Bindlib.msubst (Bindlib.unbox (Bindlib.bind_mvar xs (lift t))) ts

(** [get_prop t] returns the proposition which is inside the `ϵ` constructor. *)
let rec get_prop : config -> term -> term = fun cfg t ->
    match unfold t with
    |Appl(s, t') when Term.is_symb cfg.symb_proof s -> t'
    |Prod(a, b) ->
        begin
            try
                (* get the proposition in [a]. *)
                let prop_a = try get_prop cfg a with Not_Proof _ -> 
                    raise (Not_ProofS a) in
                (* check if the variable that has the type [a] is not in [b]. *)
                assert (not (Bindlib.binder_occur b));
                (* return the proposition of [a] => the proposition of [b]. *)
                Term.add_args (mk_Symb cfg.symb_imp) 
                    [prop_a; get_prop cfg (Bindlib.unbind b |> snd)]
            with Not_ProofS _ ->
                match a with
                (* check if the left part of the implication is a variable 
                    declaration. *)
                |Appl(s, a') when Term.is_symb cfg.symb_tau s->
                    (* return that variable => the proposition of [b]. *)
                    Term.add_args (mk_Symb cfg.symb_forall) 
                        [a'; get_prop cfg (Bindlib.unbind b |> snd)]
                |_  ->
                    raise (Not_Proof t)
        end

    |Abst(_, _) -> raise (Not_Proof t)
    |_ -> raise (Not_Proof t)

(** [check_epsilon cfg t] returns true if the proposition is a proof. *)
let rec check_epsilon : config -> term -> bool = fun cfg t ->
    match unfold t with
    |Appl(s, _) when Term.is_symb cfg.symb_proof s -> true
    |Prod(a, b)                         ->
        begin
            try
                if not (check_epsilon cfg a) then
                    raise (Not_ProofS a)
                else
                    check_epsilon cfg (Bindlib.unbind b |> snd)
            with Not_ProofS _ ->
                match a with
                |Appl(s, _) when Term.is_symb cfg.symb_tau s ->
                    check_epsilon cfg (Bindlib.unbind b |> snd)
                |_ ->
                    false
        end
    |Abst(_, _) -> false
    |_          -> false

(** [is_total_instance a b f x y] checks if [b] is a total instance of [a] where
    we substitute [y] with [f x]. *)
let is_total_instance :
    term -> term -> sym -> tvar list -> tvar -> term list option = 
    fun a b f x y ->
    let fx = Term.add_args (mk_Symb f) (List.map (fun x -> mk_Vari x) x) in
    (* Calculate the strong normal form before adding the TRef since we can not
        do it with TRef. *)
    let a = Eval.snf [] a in
    (* replace [y] with [fx] in [a] *)
    let a' = subst_var y a fx in
    let x_tref = Array.init (List.length x) (fun _ -> mk_TRef (ref None)) in
    let a' = subst_mvar x a' (Array.to_list x_tref) in
    let nf_a = a' in
    let nf_b = Eval.snf [] b in
    (* if the normal form of [a] ≡ the normal form of [b]. *)
    if Handle.Rewrite.eq [] nf_a nf_b then
        begin
            (* get the arguments of [a] where the equivalence is satisfied. *)
            let ui_tref = Array.to_list x_tref in
            let get_content = fun t -> match t with
                | TRef(r) -> (match !r with Some(a) -> a | _ -> assert false)
                | _ -> assert false in
            Some(List.map get_content ui_tref)
        end
    else
        begin
            (* return None in case that [b] is not a total instance of [a]. *)
            None
        end

let count = ref 0

(** [construct_delta cfg f a x y t] build the context
    [α₀ : (fu⁰/y, u⁰/x) a, α₁ : (fu¹/y, u¹/x) a, ..., αₖ : (fuᵏ/y, uᵏ/x) a ]
    where [uⁱ] are the arguments of [f] inside [t]. *)
let construct_delta :
    config -> (term * tvar) list -> sym -> term -> tvar list -> tvar 
    -> term list list -> ctxt * term list Extra.IntMap.t * (term * tvar) list = 
    fun cfg inst_map f a x y ui ->
    (* build [f ̄x]. *)
    let fx = Term.add_args (mk_Symb f) (List.map (fun x -> mk_Vari x) x) in
    (* build [f ̄x / y] a. *)
    let a_y = subst_var y a fx in
    let add_context = fun (e, m, inst_map) u ->
        (* build [f ̄x / y, ̄u / ̄x] a. *)
        let ax = subst_mvar x a_y u in
        (* build ϵ ([f ̄x / y, ̄u / ̄x] a). *)
        let pi_ax = mk_Appl(mk_Symb cfg.symb_proof, ax) in
        let fu = subst_mvar x fx u in
        let var, inst_map =
                try
                    (* return the variable of the context that has the type 
                        [f ̄u / y, ̄u / ̄x] a. *)
                    List.find (fun (x, _) -> 
                        Eval.eq_modulo [] fu x) inst_map |> snd, inst_map
                with Not_found -> count := !count + 1;
                    (* otherwise, create a new one. *)
                 let v = Term.new_tvar ("alpha"^(string_of_int !count)) in 
                    v, (fu, v)::inst_map in
            (var, pi_ax, None)::e, Extra.IntMap.add 
                (Bindlib.uid_of var) u m, inst_map in
    List.fold_left add_context ([], Extra.IntMap.empty, inst_map) ui

(** [get_x cfg t] return the list of quantified variables [x₀; x₁; ...; xₙ] and 
    a term [b] if [t] is of the form : [∀x₀x₁xₙ. b]. *)
let rec get_x : config -> term -> tvar list * term = fun cfg t ->
    let s, args = Term.get_args t in
    match s with
    |s when Term.is_symb cfg.symb_forall s ->
        begin
            (* get [λ̄x, b] from [∀ (λ̄x, b)]. *)
            match List.nth args 0 with
            |Abst(_, b) ->
                (* get the first variable [x] from [̄x]. *)
                let x, b = Bindlib.unbind b in
                (* get the rest of variables of [̄x]. *)
                let x', b' = get_x cfg b in
                x::x', b'
            |_ -> assert false
        end
    |_ -> [], t

(** [get_y cfg t] return the existentiel variable [y] and a term [b] if [t] is 
    of the form : [∃y. b]. *)
let get_y : config -> term -> tvar * term = fun cfg t ->
    let s, args = Term.get_args t in
    match s with
    |s when Term.is_symb cfg.symb_exists s ->
        begin
            match unfold (List.nth args 0) with
            (* return the variable [y] of the expression [∃ (λy, b)]. *)
            |Abst(_, b) -> Bindlib.unbind b
            |_ -> assert false
        end
    |_ -> assert false

(** [elim_hypothesis cfg u f x y a pa b pb] return a proof of [b] without the
    hypothesis [h]. if Γ,h: (u/x, fu/y)a ⊢ pb : b and Γ ⊢ pa : a return Γ ⊢
    pa u b (λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb) : b *)
let elim_hypothesis :
    config -> tvar -> term list -> sym -> tvar list -> tvar -> term -> term 
    -> term -> term -> term = fun cfg h u f x y a pa b pb ->
    (* create a new variable [z]. *)
    let z = Term.new_tvar "z" in
    (* build the term [f ̄u]. *)
    let fu = Term.add_args (mk_Symb f) u in
    (* (z / fu) pb. *)
    let fresh_pb = subst_inv fu z pb in
    (* (u / x) a. *)
    let hu = subst_mvar x a u in
    (* (u / x, z / y) a. *)
    let huz = subst_var y hu (mk_Vari z) in
    (* λ (h : huz), (z / fu) pb. *)
    let h_lambda = mk_Abst(mk_Appl(mk_Symb cfg.symb_proof, huz), 
        Bindlib.unbox (Bindlib.bind_var h (lift fresh_pb))) in
    
    let folsig = Common.Path.(Map.find (of_string "logic.fol")) !Sign.loaded in
    let iota = mk_Symb (Sign.find folsig "κ") in (* IMPROVE WITH BUILTINS *)
    (* λ (z : iota), λ (h : huz), (z / fu) pb. *)
    let z_lambda = mk_Abst(iota, 
        Bindlib.unbox (Bindlib.bind_var z (lift h_lambda))) in
    (* pa u b (λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb). *)
    let ndsig = Common.Path.(Map.find (of_string "logic.nd")) !Sign.loaded in (* IMPROVE WITH BUILTINS *)
    let ex_E = Sign.find ndsig "∃E" in (* IMPROVE WITH BUILTINS *)
    let applied_pa = Term.add_args pa u in
    let applied_a = mk_Abst(iota, 
        Bindlib.unbox (Bindlib.bind_var z (lift huz))) in
            Term.add_args (mk_Symb ex_E) 
                [applied_a; applied_pa; get_prop cfg b; z_lambda]

(** [get_prod t x] return [(u, v)] if [t] is of the form [∀ (x : u), v]. *)
let get_prod : term -> tvar -> term * term = fun t x ->
    match unfold t with
    |Prod(u, v) -> u, Bindlib.subst v (mk_Vari x)
    |_ -> assert false

(** [find_term t l] find the term [t] in the list [l = (t₀ : x₀); ...; (tₙ : xₙ)] 
    and return [x]. *)
let find_term : term -> (term * tvar) list -> tvar = fun t l ->
    try
        snd (List.find (fun (x, _) -> Eval.eq_modulo [] t x) l)
    with Not_found -> assert false

let get_term_context = fun (_, x, _) -> x
let get_var_context = fun (v, _, _) -> v

(** [check_bottom cfg t] checks if [t] has the form [ϵ ⊥]. *)
let check_bottom : config -> term -> bool = fun cfg t ->
    match unfold t with
    |Appl(eps, bot) 
        when Term.is_symb cfg.symb_proof eps && Term.is_symb cfg.symb_bot bot
            -> true
    |_ -> false

(** [intro_axioms cfg ctxt proof formula] introduces all hypotheses until we get
    [ϵ ⊥]. *)
let rec intro_axioms : config -> ctxt -> term -> term -> ctxt * term * term = 
    fun cfg ctxt proof formula ->
    (* if the current formula is [ϵ ⊥].*)
    if check_bottom cfg formula then
        (* return the current proof with the same context *)
        ctxt, proof, formula
    else
        (* otherwise we eliminate one lambda from the proof *)
        match proof, formula with
        |Abst(a, b), Prod(_, b') ->
            let x, b = Bindlib.unbind b in
            let _, b' = Bindlib.unbind b' in
            intro_axioms cfg ((x, a, None)::ctxt) b b'
        |_ -> 
            assert false

let deskolemize : config -> (term * tvar) list -> ctxt -> term -> term -> term 
                  -> sym -> term -> ctxt * term 
                  * term list Extra.IntMap.t * ((term * tvar) list) =
  fun cfg inst_map context axiom formula proof f pa ->
  (* get the variables x̅. *)
  let x, a = get_x cfg axiom in
  (* get the variable y. *)
  let y, a = get_y cfg a in
  (* the main function. *)
  let rec deskolem : 
    (term * tvar) list -> ctxt -> term -> term 
    -> ctxt * term * term list Extra.IntMap.t * ((term * tvar) list) =
    fun inst_map context formula proof ->
    (* if the current formula has the form [ϵ A]. *)
    if check_epsilon cfg formula then
      begin
        (* calculate [U̅ᵢ]. *)
        let u = skolem_args f [] [] (unfold formula) in
        let add_ui u alpha =
          try
            (* don't add ∀ x̅, (f x̅ / y) A. *)
            let gtc_alpha = get_term_context alpha in
            try
              skolem_args f [] u gtc_alpha
            with Failure _ -> skolem_args f [] u gtc_alpha
          with Not_Proof(_) -> u in
        (* calculate [U̅ᵢ] of the context. *)
        let u = List.fold_left add_ui u context in
        (* sort [U̅ᵢ] by size. *)
        let u = List.sort (fun x y -> size_args f x - size_args f y) u in
        (* construct Δ. *)
        let delta, mu, inst_map' = construct_delta cfg inst_map f a x y u in
        (* check if [formula] is a total instance of [a]. *)
        match is_total_instance 
            (mk_Appl (mk_Symb cfg.symb_proof, a)) formula f x y 
        with
        (* if it is a total instance. *)
        | Some(_) ->
            (* find in Δ the correspanding variable. *)
           let alpha =
             try List.find
                   (fun (_, x, _) -> Eval.eq_modulo [] formula x) delta
             with Not_found -> assert false in
           delta, mk_Vari (get_var_context alpha), mu, inst_map'
        | None ->
            (* otherwise *)
           let handle_apps head type_head args = 
             let end_type,
                 new_inst_map,
                 new_delta,
                 new_mu,
                 new_proof =
               List.fold_left
                 (fun (type_u, inst_map, delta_u, mu_u, new_u) arg ->
                   let type_v, codomain =
                     match Eval.whnf [] type_u with
                       Prod(x,y) -> x, y
                     | _ -> assert false
                   in
                   (* calculate Δᵥ *)
                   let delta_v, new_v, mu_v, new_inst_map =
                     deskolem inst_map context type_v arg in
                   let exist_delta = fun d y ->
                     if List.exists (fun x -> Eval.eq_modulo [] 
                        (get_term_context x) (get_term_context y)) delta_u then
                       d
                     else y::d
                   in
                   Bindlib.subst codomain arg,
                   new_inst_map,
                   (* construct a new Δ where the elements of Δᵤ are in Δᵥ *)
                   List.fold_left exist_delta delta_u delta_v,
                   Extra.IntMap.union (fun _ x _ -> Some(x)) mu_u mu_v,
                   (* return [u' v']. *)
                   mk_Appl (new_u, new_v))
                 (type_head,
                  inst_map',
                  [],
                  Extra.IntMap.empty,
                  head)
                 args
             in
             let not_exist_env = fun y -> 
             List.for_all (fun x -> not (Eval.eq_modulo [] (get_term_context x) 
                (get_term_context y))) delta in
             let hypotheses = List.filter not_exist_env new_delta in
             let hypotheses = List.sort (fun (_,t,_) (_,v,_) ->
                                  compare (size v) (size t)) hypotheses in
             let elim_hyp = fun pb alpha ->
                let u = Extra.IntMap.find 
                    (alpha |> get_var_context |> Bindlib.uid_of) new_mu in
                let fu = Term.add_args (mk_Symb f) u in
                elim_hypothesis cfg (find_term fu new_inst_map) u f x y a pa 
                    formula pb in
             Infer.conv [] formula end_type;
             (delta, List.fold_left elim_hyp new_proof hypotheses, mu, 
                new_inst_map)
           in
           let proof' = Eval.whnf [] proof in
           match Term.get_args (unfold proof') with
           |Vari(_), []             ->
             delta, proof', mu, inst_map'
           |Symb(_), []             ->
             delta, proof', mu, inst_map'
           |Abst(t, u), []          ->
             let (x_var, u) = Bindlib.unbind u in
             let whnf_formula = Eval.whnf [] formula in
             let t', u' = get_prod whnf_formula x_var in
             let new_context = (x_var, t', None)::context in
             let new_delta, new_u, new_mu, new_inst_map = 
                deskolem inst_map' new_context u' u in
             let not_exist_env = fun y -> 
                List.for_all (fun x -> not (Eval.eq_modulo [] 
                    (get_term_context x) (get_term_context y))) delta in
             let hypotheses = List.filter not_exist_env new_delta in
             let hypotheses = List.sort (fun (_,t,_) (_,v,_) ->
                                  compare (size t) (size v)) hypotheses in
             let proof_b = mk_Abst (t, Bindlib.unbox 
                (Bindlib.bind_var x_var (lift new_u))) in
             let elim_hyp = fun pb alpha ->
               let u = Extra.IntMap.find 
                (alpha |> get_var_context |> Bindlib.uid_of) new_mu in
               let fu = Term.add_args (mk_Symb f) u in
               elim_hypothesis cfg (find_term fu new_inst_map) 
                u f x y a pa formula pb
             in
             delta, List.fold_left elim_hyp proof_b hypotheses, mu, new_inst_map
           | Symb(s) as head, args -> (* CAS D'UNE APPLICATION *)
              let type_h = !(s.sym_type) in
              handle_apps head type_h args
           | Vari(x) as head, args ->
              let type_x = Ctxt.type_of x context in
              handle_apps head type_x args
           |_ -> assert false
      end
    else
      ([], proof, Extra.IntMap.empty, inst_map)
  in
  deskolem inst_map context formula proof

let main : Sign.t -> unit = fun sign ->
    let cfg = get_config sign in
    let a = get_prop cfg !(cfg.symb_Axiom.sym_type) in
    let b = cleanup (!(cfg.symb_Formula.sym_type)) in
    (* Remove all lambdas from the proof and add all product (after removing 
        them) in the context. *)
    let context, proof, formula =   
        intro_axioms cfg [] (Eval.whnf [] (mk_Symb cfg.symb_Formula)) b in
    let _, proof', _, _ = 
        deskolemize cfg [] context a formula (Eval.snf context proof) 
            cfg.symb_Skolem (mk_Symb cfg.symb_Axiom) in
    Common.Console.out 1 "%a@." Print.pp_term proof';
    let oc = Format.formatter_of_out_channel (open_out "test.lp") in
    Stdlib.(Common.Console.out_fmt := oc);
    Common.Console.out 1 "// Add all requires, symbols and builtins" (* IMPROVE *)