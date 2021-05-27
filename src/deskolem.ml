open Core
open! Lplib
open Term
open Timed

(** [subst_inv fu x t] replaces all the subterms [fu] by a fresh variable [x] in
    the term [t]. *)
let subst_inv : term -> term Bindlib.var -> term -> term = fun fu x ->
  let rec subst t =
    if Eval.eq_modulo [] t fu then mk_Vari x else
    match unfold t with
    | Vari _                    -> t
    | Type                      -> t
    | Kind                      -> t
    | Symb _                    -> t
    | Prod( a, b)               ->
        let (v, b) = Bindlib.unbind b in
        let sa = subst a in
        let sb = Bindlib.bind_var v (lift (subst b)) in
        mk_Prod(sa, Bindlib.unbox sb)
    | Abst( a, b)               ->
        let (v, b) = Bindlib.unbind b in
        let sa = subst a in
        let sb = Bindlib.bind_var v (lift (subst b)) in
        mk_Abst(sa, Bindlib.unbox sb)
    | Appl( a, b)               -> mk_Appl(subst a, subst b)
    | Meta _
    | Patt _
    | TEnv _
    | Wild
    | LLet _
    | TRef _                    -> assert false (* is not handled in the encoding. *)
  in subst

(** [frozen l t] checks if a term [t] contains one of the variables of [l]. *)
let frozen : tvar list -> term -> bool = fun l t ->
    let lifted_t = lift t in
    List.for_all (fun x -> not (Bindlib.occur x lifted_t)) l

(** [print_args l] print terms that [l] contains. *)
let print_args l =
    List.iter (Common.Console.out 4 "%a " Print.pp_term) l;
    Common.Console.out 4 "@."

(** [get_ui f l t] returns a list of arguments used in [f]-terms inside [t]. *)
let rec get_ui : sym -> tvar list  -> term list list -> term -> term list list = fun f vlist l t  ->
    Common.Console.out 4 "[DEBUG] Get Uᵢ of [%a]@." Print.pp_term t;
    match unfold t with
    | Vari _
    | Type
    | Kind                      -> l
    | Symb _                    ->
        if Eval.eq_modulo [] t (mk_Symb(f)) then
            if List.exists (fun x -> x = []) l then
                l
            else
                []::l
        else
            l
    | Prod( a, b)               ->
        let (x, b) = Bindlib.unbind b in
        let l = get_ui f vlist l a in
        get_ui f (x::vlist) l b
    | Abst( a, b)               ->
        let (x, b) = Bindlib.unbind b in
        let l = get_ui f vlist l a in
        get_ui f (x::vlist) l b
    | Appl( _, _)               ->
        let (h, args) = Term.get_args t in
        let args_set = List.fold_left (get_ui f vlist) l args in
        if Eval.eq_modulo [] h (mk_Symb(f)) then
            begin
                Common.Console.out 4 "H : %a@." Print.pp_term h;
                if List.exists (List.for_all2 (Eval.eq_modulo []) args) args_set || not (frozen vlist t) then
                    args_set
                else
                    args::args_set
            end
        else
            get_ui f vlist args_set h
    | Meta _                    -> Common.Console.out 4 "[DEBUG] Meta NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | Patt _                    -> Common.Console.out 4 "[DEBUG] Patt NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | TEnv _                    -> Common.Console.out 4 "[DEBUG] TEnv NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | Wild                      -> Common.Console.out 4 "[DEBUG] Wild NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | LLet _                    -> Common.Console.out 4 "[DEBUG] LLet NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | TRef _                    -> Common.Console.out 4 "[DEBUG] TRef NOT HANDLED: [%a]@." Print.pp_term t; assert false (* is not handled in the encoding. *)

(** [get_option opt] returns [x] if [opt] is of the shape `Some x`, raise an
    Invalid_argument otherwise. *)
let get_option = fun opt ->
    match opt with
    | Some(x)   -> x
    | None      -> raise (Invalid_argument "The option is None.")

(** [size t] return the size of the term [t]. *)
let rec size : term -> int = fun t ->
  List.fold_right (fun a l -> size a + l) (snd (Term.get_args t)) 1

(** [size_args f args] return the size of the term [f a0 a1 ... an] where args
    = [a0; a1; ...; an]. *)
let size_args : sym -> term list -> int = fun f args ->
    size (Term.add_args (mk_Symb(f)) args)

(** [subst_var x m n] substitutes the variable [x] with the term [n] inside the
    term [m].*)
let subst_var : term Bindlib.var -> term -> term -> term = fun x m n ->
    Common.Console.out 4 "subst_var [ %a / %a] %a@." Print.pp_term n Print.pp_var x Print.pp_term m;
    Bindlib.subst (Bindlib.unbox (Bindlib.bind_var x (lift m))) n

(** [subst_mvar x m n] substitutes all variables that [x] contains with the terms
    of [n] inside the term [m]. *)
let subst_mvar : term Bindlib.var list -> term -> term list -> term =
    fun x m n ->
    let x = Array.of_list x in
    let n = Array.of_list n in
    Bindlib.msubst (Bindlib.unbox (Bindlib.bind_mvar x (lift m))) n

exception Not_Proof of term
exception Not_ProofS of term

(** [unProof t] returns the proposition which is inside the `Proof` constructor. *)
let rec unProof : Sign.t -> term -> term = fun sign t ->
    Common.Console.out 4 "unProof [%a]@." Print.pp_term t;
    match unfold t with
    |Appl(Symb({sym_name = "π"; _}), t') -> t'
    |Prod(a, b) ->
        (try
            let unProofA = try unProof sign a with Not_Proof _ -> raise (Not_ProofS a) in
            let imp = Extra.StrMap.find "imp" !(sign.sign_builtins) in
            assert (not (Bindlib.binder_occur b));
            Term.add_args (mk_Symb imp) [unProofA; unProof sign (Bindlib.unbind b |> snd)]
        with Not_ProofS _ ->
            match a with
            |Appl(Symb({sym_name = "τ"; _}), a') ->
                let forall = Extra.StrMap.find "forall" !(sign.sign_builtins) in
                Term.add_args (mk_Symb forall) [a'; unProof sign (Bindlib.unbind b |> snd)]
            |_                                  ->
                raise (Not_Proof t))

    |Abst(_, _) -> Common.Console.out 4 "ABST NOT PROOF : %a@." Print.pp_term t; raise (Not_Proof t)
    |_                                          ->
        Common.Console.out 4 "Other cases NOT PROOF : %a@." Print.pp_term t; raise (Not_Proof t)

(** [unProofCheck t] returns true if the proposition is a proof. *)
let rec unProofCheck : Sign.t -> term -> bool = fun sign t ->
    Common.Console.out 4 "unProof [%a]@." Print.pp_term t;
    match unfold t with
    |Appl(Symb({sym_name = "π"; _}), _) -> true
    |Prod(a, b) ->
        (try
            if not (unProofCheck sign a) then
                raise (Not_ProofS a)
            else
                unProofCheck sign (Bindlib.unbind b |> snd)
        with Not_ProofS _ ->
            match a with
            |Appl(Symb({sym_name = "τ"; _}), _) ->
                unProofCheck sign (Bindlib.unbind b |> snd)
            |_                                  ->
                false)

    |Abst(_, _) -> Common.Console.out 4 "ABST NOT PROOF : %a@." Print.pp_term t; false
    |_                                          ->
        Common.Console.out 4 "Other cases NOT PROOF : %a@." Print.pp_term t; false


(** [is_total_instance a b f x y] checks if [b] is a total instance of [a] where
    we substitute [y] with [f x]. *)
let is_total_instance :
    term -> term -> sym -> term Bindlib.var list -> term Bindlib.var
    -> term list option = fun a b f x y ->
    let fx = Term.add_args (mk_Symb(f)) (List.map (fun x -> mk_Vari x) x) in
    (* Calculate the strong normal form before adding the TRef since we can not
        do it with TRef. *)
    let a = Eval.snf [] a in
    Common.Console.out 4 "IsTotalInstance subst_var %a %a %a @." Print.pp_var y Print.pp_term a Print.pp_term fx;
    let a' = subst_var y a fx in
    let x_tref = Array.init (List.length x) (fun _ -> mk_TRef(ref None)) in
    let a' = subst_mvar x a' (Array.to_list x_tref) in (* FIXME to_list is called before of_list in susbt_mvar *)
    let nf_a = a' in
    let nf_b = Eval.snf [] b in
    (* Common.Console.out 4 "NFA : %a@.NFB : %a@." Print.pp_term nf_a Print.pp_term nf_b; *)
    if Handle.Rewrite.eq [] nf_a nf_b then
        begin
            Common.Console.out 4 "IS TOTAL INSTANCE OK@.";
            let ui_tref = Array.to_list x_tref in
            let get_content = fun t -> match t with
                | TRef(r)    -> (match !r with Some(a) -> a | _ -> assert false)
                | _          -> assert false in
            Some(List.map get_content ui_tref)
        end
    else
        begin
            Common.Console.out 4 "IS TOTAL INSTANCE KO@.";
            None
        end

let count = ref 0

(** [construct_delta f a x y t] build the context
    [α₀ : (fu⁰/y, u⁰/x) a, α₁ : (fu¹/y, u¹/x) a, ..., αₖ : (fuᵏ/y, uᵏ/x) a ]
    where [uⁱ] are the arguments of [f] inside [t]. *)
let construct_delta :
    Sign.t -> (term * tvar) list -> sym -> term -> term Bindlib.var list -> term Bindlib.var -> term list list
    -> ctxt * term list Extra.IntMap.t * (term * tvar) list = fun sign inst_map f a x y ui ->
    List.iter (fun l -> List.iter (Common.Console.out 4 " Ui : %a@." Print.pp_term) l) ui;
    let fx = Term.add_args (mk_Symb(f)) (List.map (fun x -> mk_Vari x) x) in
    Common.Console.out 4 "Construct Delta subst_var %a %a %a @." Print.pp_var y Print.pp_term a Print.pp_term fx;
    let a_y = subst_var y a fx in
    let add_context = fun (e, m, inst_map) u ->
        let ax = subst_mvar x a_y u in
        Common.Console.out 4 "Construct Delta : A = %a AX = %a@." Print.pp_term a Print.pp_term ax;
        let pi = Extra.StrMap.find "proof" !(sign.sign_builtins) in
        let pi_ax = mk_Appl(mk_Symb pi, ax) in
        let fu = subst_mvar x fx u in
        let var, inst_map =
                try
                    Common.Console.out 4 "Old alpha";
                    snd (List.find (fun (x, _) -> Eval.eq_modulo [] fu x) inst_map), inst_map
                with Not_found -> count := !count + 1;
                 let v = Term.new_tvar ("alpha"^(string_of_int !count)) in v, (fu, v)::inst_map in
        (var, pi_ax, None)::e, Extra.IntMap.add (Bindlib.uid_of var) u m, inst_map in
    List.fold_left add_context ([], Extra.IntMap.empty, inst_map) ui

(** [get_x t] return the list of quantified variables [x₀; x₁; ...; xₙ] and a
    term [b] if [t] is of the form : [∀x₀x₁xₙ. b]. *)
let rec get_x : term -> term Bindlib.var list * term = fun t ->
    let s, args = Term.get_args t in
    match s with
    |Symb({sym_name = "∀"; _})     ->
        (
            match List.nth args 1 with
            |Abst(_, b) ->
                let x, b = Bindlib.unbind b in
                let x', b' = get_x b in
                x::x', b'
            |_          -> assert false
        )
    |_                                  -> [], t

(** [get_y t] return the existentiel variable [y] and a term [b] if [t] is of
    the form : [∃y. b]. *)
let get_y : term -> term Bindlib.var * term = fun t ->
    let s, args = Term.get_args t in
    match s with
    |Symb({sym_name = "∃"; _})     ->
        (
            match unfold (List.nth args 1) with
            |Abst(_, b) -> Bindlib.unbind b
            |_          -> assert false
        )
    |_                                  -> assert false

(** [type_elm sign s] return the type of the symbol named [s] in the signature
    [sign]. *)
let type_elm sign s = !((Sign.find sign s).sym_type)

let check_term_iota = function
    |Appl(Symb({sym_name = "τ"; _}), _)      -> true
    |_                                          -> false

(** [elim_hypothesis sign u f x y a pa b pb] return a proof of [b] without the
    hypothesis [h]. if Γ,h: (u/x, fu/y)a ⊢ pb : b and Γ ⊢ pa : a return Γ ⊢
    pa u b (λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb) : b *)
let elim_hypothesis :
    Sign.t -> tvar -> term list -> sym -> term Bindlib.var list ->
    term Bindlib.var -> term -> term -> term -> term -> term =
    fun sign h u f x y a pa b pb ->
    Common.Console.out 4 "[DEBUG] First step in elim_hypothesis@.";
    let z = Term.new_tvar "z" in
    let fu = Term.add_args (mk_Symb(f)) u in
    Common.Console.out 4 "[DEBUG] fu : %a@." Print.pp_term fu;
    (* (z / fu) pb. *)
    let fresh_pb = subst_inv fu z pb in (* PEUT ETRE ÇA BUG ICI A CAUSE DE L'ABSENCE DU EXISTS ET FORALL. *)
    Common.Console.out 4 "AVANT : [%a]@." Print.pp_term pb;
    Common.Console.out 4 "APRÈS : [%a]@." Print.pp_term fresh_pb;
    (* (u / x) a. *)
    let hu = subst_mvar x a u in
    Common.Console.out 4 "HU : [%a]@." Print.pp_term hu;
    (* (u / x, z / y) a. *)
    let huz = subst_var y hu (mk_Vari z) in
    Common.Console.out 4 "HUZ : [%a]@." Print.pp_term huz;
    (* let h = Bindlib.new_var mkfree "h" in *)
    (* λ (h : huz), (z / fu) pb. *)
    let pi = Extra.StrMap.find "proof" !(sign.sign_builtins) in
    let h_lambda = mk_Abst(mk_Appl(mk_Symb pi, huz), Bindlib.unbox (Bindlib.bind_var h (lift fresh_pb))) in
    (* zen.iota *)
    Common.Console.out 4 "[DEBUG] Iota step in elim_hypothesis@.";
    let iota = type_elm sign "iota_b" in
    (* λ (z : iota), λ (h : huz), (z / fu) pb. *)
    Common.Console.out 4 "[DEBUG] Constructing Abstraction step in elim_hypothesis@.";
    let z_lambda = mk_Abst(iota, Bindlib.unbox (Bindlib.bind_var z (lift h_lambda))) in
    (* pa u b (λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb). *)
    Common.Console.out 4 "[DEBUG] Final step in elim_hypothesis@.";
    Common.Console.out 4 "unProof pb : [%a]@." Print.pp_term pb;
    let ndsig = Common.Path.(Map.find (of_string "logic.nd")) !Sign.loaded  in
    let ex_E = Sign.find ndsig "∃E" in
    let applied_pa = Term.add_args pa u in
    let pa_u_b_l = Term.add_args (mk_Symb ex_E) 
                     [iota; a; applied_pa; unProof sign b; z_lambda] in
    Common.Console.out 4 "END ELIM HYP : [%a]@." Print.pp_term pa_u_b_l;
    pa_u_b_l

(** [get_prod t x] return [(u, v)] if [t] is of the form [∀ (x : u), v]. *)
let get_prod : term -> term Bindlib.var -> term * term = fun t x ->
    match unfold t with
    |Prod(u, v) -> u, Bindlib.subst v (mk_Vari x)
    |_          -> Common.Console.out 4 "%a" Print.pp_term t; assert false

let find_term : term -> (term * tvar) list -> tvar = fun t l ->
    try
        snd (List.find (fun (x, _) -> Eval.eq_modulo [] t x) l)
    with Not_found -> assert false

let get_term_context = fun (_, x, _) -> x
let get_var_context = fun (v, _, _) -> v


let check_bottom : term -> bool = fun t ->
    match unfold t with
    |Appl(Symb({sym_name = "π"; _}), Symb({sym_name = "⊥"; _})) -> true
    |_                                                          -> false

let rec intro_axioms : ctxt -> term -> term -> ctxt * term * term = fun ctxt proof formula ->
    if check_bottom formula then
        ctxt, proof, formula
    else
        match proof, formula with
        |Abst(a, b), Prod(_, b')    ->
            let x, b = Bindlib.unbind b in
            let _, b' = Bindlib.unbind b' in
            intro_axioms ((x, a, None)::ctxt) b b'
        |_                          ->
            Common.Console.out 4 "intro_axioms : %a %a" Print.pp_term (Eval.whnf [] proof) Print.pp_term formula; assert false

let deskolemize : Sign.t -> (term * tvar) list -> ctxt -> term -> term -> term -> sym -> term
                  -> term -> ctxt * term * term list Extra.IntMap.t * ((term * tvar) list) =
  fun sign inst_map context axiom formula proof f pa iota ->
  Common.Console.out 4 "[DEBUG] Deskolemize on @. B := [%a]@. P := [%a]@." Print.pp_term formula Print.pp_term proof;
  List.iter (fun (x, y) -> Common.Console.out 4 "INST_MAP : (%a, %a)@." Print.pp_term x Print.pp_var y) inst_map;
  (* Get the variables x̅ and y. *)
  Common.Console.out 4 "[Debug] geting [x̅] from [%a]@." Print.pp_term axiom;
  let x, a = get_x axiom in
  Common.Console.out 4 "[Debug] geting [y] from [%a]@." Print.pp_term a;
  let y, a = get_y a in
  Common.Console.out 4 "[Debug] construct [f(x̅)] from [%a]@." Print.pp_term a;
  let fx = Term.add_args (mk_Symb f) (List.map (fun x -> mk_Vari x) x) in
  Common.Console.out 4 "[Debug] replace [%a] with [%a] in [%a]@." Print.pp_var y Print.pp_term fx Print.pp_term a;
  let a_fx = subst_var y a fx in
  let bind_var t x_var = mk_Abst(iota, Bindlib.unbox (Bindlib.bind_var x_var (lift t))) in
  Common.Console.out 4 "[Debug] constructing lambdas [λ(x̅ : term iota).[f(x̅)/y]A] @.";
  let x_a_fx = List.fold_left bind_var a_fx x in
  Common.Console.out 4 "[DEBUG] X_A_FX : [%a]@." Print.pp_term x_a_fx;
  Common.Console.out 4 "[Debug] calculating U̅ᵢ@.";
  (* Calculate U̅ᵢ *)
  let pi = Extra.StrMap.find "proof" !(sign.sign_builtins) in
  let rec deskolem : (term * tvar) list -> ctxt -> term -> term -> ctxt * term * term list Extra.IntMap.t * ((term * tvar) list) =
    fun inst_map context formula proof ->
    Common.Console.out 4 "[DEBUG] formula : %a@." Print.pp_term formula;
    Common.Console.out 4 "[DEBUG] proof : %a@." Print.pp_term proof;
    if unProofCheck sign formula then
      begin
        let u = get_ui f [] [] (unfold formula) in
        Common.Console.out 4 "[DEBUG] après unProof :  %a@." Print.pp_term formula;
        List.iter (fun l -> List.iter (Common.Console.out 4 "[DEBUG] Ui : %a, " Print.pp_term) l; Common.Console.out 4 "@.") u;
        Common.Console.out 4 "[Debug] get only Proof formulas@.";
        List.iter (fun (_, x, _) -> Common.Console.out 4 "[DEBUG] context : %a@." Print.pp_term x) context;
        let add_ui u alpha =
          try
            (* Don't add ∀ x̅, (f x̅ / y) A. *)
            let gtc_alpha = get_term_context alpha in
            try
              (* START CLEAN HERE. *)
              (* Common.Console.out 4 "Axiom : %a@." Print.pp_term gtc_alpha;
                        let axiom = unProof sign gtc_alpha in
                        Common.Console.out 4 "Axiom After UnProof : %a@." Print.pp_term axiom;
                        let axiom = List.nth (Term.Term.get_args axiom |> snd) 1 in
                        Common.Console.out 4 "Axiom After List.nth : %a@." Print.pp_term axiom;
                        (*let forall_symb = Extra.StrMap.find "forall" !(sign.sign_builtins) in
                        let pii = Extra.StrMap.find "proof" !(sign.sign_builtins) in
                        let pi_forall_x_a_fx = Term.add_args (mk_Symb pii) [(Term.add_args (mk_Symb forall_symb) [iota; x_a_fx])] in
                        *)
                        Common.Console.out 4 "GTC Alpha : %a@. X_A_FX : %a@." Print.pp_term axiom Print.pp_term x_a_fx;

                        if Eval.eq_modulo [] axiom x_a_fx then
                            u
                        else*)
              (* END CLEAN HERE. *)
              get_ui f [] u gtc_alpha
            with Failure _ -> (Common.Console.out 4 "Fail [%a]@." Print.pp_term gtc_alpha; get_ui f [] u gtc_alpha)
          with Not_Proof(_) -> u in

        let u = List.fold_left add_ui u context in
        (* Sort U̅ᵢ *)
        let u = List.sort (fun x y -> size_args f x - size_args f y) u in
        (* Construct Δ. *)
        let delta, mu, inst_map' = construct_delta sign inst_map f a x y u in
        Common.Console.out 4 "[DEBUG] DELTA : @.";
        List.iter (fun (v, t, _) -> Common.Console.out 4 "%a : %a @." Print.pp_var v Print.pp_term t) delta;
        Common.Console.out 4 "@.";
        Common.Console.out 4 "[DEBUG] MU : "; Extra.IntMap.iter (fun s _ -> Common.Console.out 4 ", %d@." s) mu;
        Common.Console.out 4 "@.";
        (* Check if [formula] is a total instance of [a]. *)
        Common.Console.out 4 "IS TOTAL INSTANCE [%a] OF [%a]@." Print.pp_term formula Print.pp_term a;

        match is_total_instance (mk_Appl(mk_Symb pi, a)) formula f x y with
        | Some(_)   ->
           Common.Console.out 4 "[DEBUG] Find [%a]@." Print.pp_term formula;
           Common.Console.out 4 "[DEBUG]  In [%d] @." (List.length delta);
           List.iter (fun (x, y, _) ->  Common.Console.out 4 "%a : %a" Print.pp_var x Print.pp_term y) delta;
           Common.Console.out 4 "[DEBUG] Find [%a]@." Print.pp_term formula;
           Common.Console.out 4 "[DEBUG]  In [%d] @." (List.length inst_map');
           List.iter (fun (y, x) ->  Common.Console.out 4 "  %a : %a@." Print.pp_var x Print.pp_term y) inst_map';
           Common.Console.out 4 "[DEBUG] Is total instance OK";
           let alpha =
             try List.find
                   (fun (_, x, _) -> Eval.eq_modulo [] formula x) delta
             with Not_found -> Common.Console.out 4 "formula : [%a]@." Print.pp_term formula; assert false in
           delta, mk_Vari(get_var_context alpha), mu, inst_map'
        | None      ->
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
                   let delta_v, new_v, mu_v, new_inst_map =
                     deskolem inst_map context type_v arg in
                   let exist_delta = fun d y ->
                     if List.exists (fun x -> Eval.eq_modulo [] (get_term_context x) (get_term_context y)) delta_u then
                       d
                     else y::d
                   in
                   Bindlib.subst codomain arg,
                   new_inst_map,
                   List.fold_left exist_delta delta_u delta_v,
                   Extra.IntMap.union (fun _ x _ -> Some(x)) mu_u mu_v,
                   mk_Appl(new_u, new_v))
                 (type_head,
                  inst_map',
                  [],
                  Extra.IntMap.empty,
                  head)
                 args
             in
             let not_exist_env = fun y -> List.for_all (fun x -> not (Eval.eq_modulo [] (get_term_context x) (get_term_context y))) delta in
             Common.Console.out 4 "[DEBUG] Filter hypotheses in Appl@.";
             let hypotheses = List.filter not_exist_env new_delta in
             let hypotheses = List.sort (fun (_,t,_) (_,v,_) ->
                                  compare (size v) (size t)) hypotheses in
             List.iter (fun (v, x, _) -> Common.Console.out 4 "[DEBUG] delta [%a : %a]@." Print.pp_var v Print.pp_term x) delta;
             List.iter (fun (v, x, _) -> Common.Console.out 4 "[DEBUG] new_delta [%a : %a]@." Print.pp_var v Print.pp_term x) new_delta;
             List.iter (fun (v, x, _) -> Common.Console.out 4 "[DEBUG] hypotheses [%a : %a]@." Print.pp_var v Print.pp_term x) hypotheses;
             Common.Console.out 4 "[DEBUG] Generating the new proof in Appl@.";
             Common.Console.out 4 "[DEBUG] proof_b : [%a]@." Print.pp_term new_proof;
             Common.Console.out 4 "[DEBUG] Eliminating hypotheses in Appl@.";
             let elim_hyp = fun pb alpha ->
               Common.Console.out 4 "[DEBUG] Alpha = %s@."  (Bindlib.name_of (get_var_context alpha));
               Common.Console.out 4 "[DEBUG] MAP U v V : "; Extra.IntMap.iter (fun s t -> Common.Console.out 4 ", %d => [%a]@." s (List.pp Print.pp_term "; ") t)  new_mu;
               let u = Extra.IntMap.find (alpha |> get_var_context |> Bindlib.uid_of) new_mu in
               Common.Console.out 4 "[DEBUG] Return the eliminated hypotheses@.";
               let fu = Term.add_args (mk_Symb f) u in
               Common.Console.out 4 "AVANT assoc@.";
               Common.Console.out 4 "FU : %a@." Print.pp_term fu;
               Common.Console.out 4 "ELIM HYPOTHESIS (APPL) : [%a]@." Print.pp_term pb;
               let eh = elim_hypothesis sign (find_term fu new_inst_map) u f x y a pa formula pb in
               Common.Console.out 4 "[DEBUG] Post return the eliminated hypotheses@.";
               eh
             in
             Common.Console.out 4 "[DEBUG] Test convertability in Appl@.";
             Infer.conv [] formula end_type;
             (* if Pervasives.(!Infer.constraints) <> [] then (* check if [v'/x]w ≃ B. *)
                        (Common.Console.out 4 "[DEBUG] Constraints on conv of [%a] and [%a]: @." Print.pp_term formula Print.pp_term (subst_var x_var type_w new_v);
                        List.iter (fun (_, x, y) -> Common.Console.out 4 "[DEBUG] [%a] ≡ [%a] @." Print.pp_term x Print.pp_term y) (Pervasives.(!Infer.constraints))); *)
             Common.Console.out 4 "[DEBUG] Return delta, hypotheses, mu in Appl@.";
             Common.Console.out 4 "[DEBUG] MAP U : "; Extra.IntMap.iter (fun s _ -> Common.Console.out 4 ", %d@." s) mu;
             let dhm = (delta, List.fold_left elim_hyp new_proof hypotheses, mu, new_inst_map) in
             Common.Console.out 4 "[DEBUG] Post return delta, hypotheses, mu in Appl@."; dhm
           in
           Common.Console.out 4 " [DEBUG] PROOF : [%a]@." Print.pp_term proof;
           let proof' = Eval.whnf [] proof in
           Common.Console.out 4 " [DEBUG] WHNF  : [%a]@." Print.pp_term proof';
           match Term.get_args (unfold proof') with
           |Vari(_), []    ->
             Common.Console.out 4 "[DEBUG] Var : [%a]@." Print.pp_term proof';
             delta, proof', mu, inst_map'
           |Symb(_), []    ->
             Common.Console.out 4 "[DEBUG] Symb : [%a]@." Print.pp_term proof';
             delta, proof', mu, inst_map'
           |Abst(t, u), [] ->
             let (x_var, u) = Bindlib.unbind u in
             Common.Console.out 4 "[DEBUG] Abst(t, u) : @. t : [%a]@. u : [%a]@. formula : [%a]@." Print.pp_term t Print.pp_term u Print.pp_term formula;
             let whnf_formula = Eval.whnf [] formula in
             Common.Console.out 4 "  [DEBUG] TERM Abst : [%a] ABST WHNF : [%a]@." Print.pp_term (unfold proof') Print.pp_term formula;
             let t', u' = get_prod whnf_formula x_var in (* FIXME check if t = t'. *)
             Common.Console.out 4 "[DEBUG] Adding var to the context [%a]@." Print.pp_term (mk_Vari(x_var));
             let new_context = (x_var, t', None)::context in
             Common.Console.out 4 "[DEBUG] APST Calling Deskolemize from [%a] to [%a]@." Print.pp_term (unfold proof') Print.pp_term u';
             let new_delta, new_u, new_mu, new_inst_map = deskolem inst_map' new_context u' u in
             let not_exist_env = fun y -> List.for_all (fun x -> not (Eval.eq_modulo [] (get_term_context x) (get_term_context y))) delta in
             let hypotheses = List.filter not_exist_env new_delta in
             let hypotheses = List.sort (fun (_,t,_) (_,v,_) ->
                                  compare (size t) (size v)) hypotheses in
             let proof_b = mk_Abst(t, Bindlib.unbox (Bindlib.bind_var x_var (lift new_u))) in
             let elim_hyp = fun pb alpha ->
               let u = Extra.IntMap.find (alpha |> get_var_context |> Bindlib.uid_of) new_mu in
               let fu = Term.add_args (mk_Symb f) u in
               Common.Console.out 4 "ELIM HYPOTHESIS (ABST) : [%a]@." Print.pp_term pb;
               elim_hypothesis sign (find_term fu new_inst_map) u f x y a pa formula pb
             in
             delta, List.fold_left elim_hyp proof_b hypotheses, mu, new_inst_map
           (* |Appl(Symb({sym_name="nnpp";_}), _)  ->
                    Common.Console.out 4 "NNPP Case : [%a]@." Print.pp_term proof';
                    delta, proof', mu, inst_map' *)
           | Symb(s) as head, args  -> (* CAS D'UNE APPLICATION *)
              let type_h = !(s.sym_type) in
              handle_apps head type_h args
           | Vari(x) as head, args ->
              let type_x = Ctxt.type_of x context in
              handle_apps head type_x args
           |_      -> Common.Console.out 1 "Unhandled case : [%a]@.[%a]@." Print.pp_term formula Print.pp_term proof;
                      assert false
      end
    else
      (Common.Console.out 4 "None proof proof : [%a]@.[%a]@." Print.pp_term formula Print.pp_term proof;
       [], proof, Extra.IntMap.empty, inst_map)
  in
  deskolem inst_map context formula proof

(*                            get_ui f [] u gtc_alpha
                    with Failure _ -> (Common.Console.out 4 "Fail [%a]@." Print.pp_term gtc_alpha; get_ui f [] u gtc_alpha)
                with Not_Proof(_) -> u in

            let u = List.fold_left add_ui u context in
            (* Sort U̅ᵢ *)
            let u = List.sort (fun x y -> size_args f x - size_args f y) u in
            (* Construct Δ. *)
            let delta, mu, inst_map' = construct_delta sign inst_map f a x y u in
            Common.Console.out 4 "[DEBUG] DELTA : @.";
            List.iter (fun (v, t, _) -> Common.Console.out 4 "%a : %a @." Print.pp_var v Print.pp_term t) delta;
            Common.Console.out 4 "@.";
            Common.Console.out 4 "[DEBUG] MU : "; Extra.IntMap.iter (fun s _ -> Common.Console.out 4 ", %d@." s) mu;
            Common.Console.out 4 "@.";
            (* Check if [formula] is a total instance of [a]. *)
            Common.Console.out 4 "IS TOTAL INSTANCE [%a] OF [%a]@." Print.pp_term formula Print.pp_term a;

            match is_total_instance (mk_Appl(mk_Symb pi, a)) formula f x y with
            | Some(_)   ->
                Common.Console.out 4 "[DEBUG] Find [%a]@." Print.pp_term formula;
                Common.Console.out 4 "[DEBUG]  In [%d] @." (List.length delta);
                List.iter (fun (x, y, _) ->  Common.Console.out 4 "%a : %a" Print.pp_var x Print.pp_term y) delta;
                Common.Console.out 4 "[DEBUG] Find [%a]@." Print.pp_term formula;
                Common.Console.out 4 "[DEBUG]  In [%d] @." (List.length inst_map');
                List.iter (fun (y, x) ->  Common.Console.out 4 "  %a : %a@." Print.pp_var x Print.pp_term y) inst_map';
                Common.Console.out 4 "[DEBUG] Is total instance OK";
                let alpha =
                    try List.find
                        (fun (_, x, _) -> Eval.eq_modulo [] formula x) delta
                    with Not_found -> Common.Console.out 4 "formula : [%a]@." Print.pp_term formula; assert false in
                delta, mk_Vari(get_var_context alpha), mu, inst_map'
            | None      ->
                Common.Console.out 4 " [DEBUG] PROOF : [%a]@." Print.pp_term proof;
                let proof' = Eval.whnf [] proof in
                Common.Console.out 4 " [DEBUG] WHNF  : [%a]@." Print.pp_term proof';
                match unfold proof' with
                |Vari(_)    ->
                    Common.Console.out 4 "[DEBUG] Var : [%a]@." Print.pp_term proof';
                    delta, proof', mu, inst_map'
                |Symb(_)    ->
                    Common.Console.out 4 "[DEBUG] Symb : [%a]@." Print.pp_term proof';
                    delta, proof', mu, inst_map'
                |Abst(t, u) ->
                    let (x_var, u) = Bindlib.unbind u in
                    Common.Console.out 4 "[DEBUG] Abst(t, u) : @. t : [%a]@. u : [%a]@. formula : [%a]@." Print.pp_term t Print.pp_term u Print.pp_term formula;
                    let whnf_formula = Eval.whnf [] formula in
                    Common.Console.out 4 "  [DEBUG] TERM Abst : [%a] ABST WHNF : [%a]@." Print.pp_term (unfold proof') Print.pp_term formula;
                    let t', u' = get_prod whnf_formula x_var in (* FIXME check if t = t'. *)
                    Common.Console.out 4 "[DEBUG] Adding var to the context [%a]@." Print.pp_term (mk_Vari(x_var));
                    let new_context = (x_var, t', None)::context in
                    Common.Console.out 4 "[DEBUG] APST Calling Deskolemize from [%a] to [%a]@." Print.pp_term (unfold proof') Print.pp_term u';
                    let new_delta, new_u, new_mu, new_inst_map = deskolem inst_map' new_context u' u in
                    let not_exist_env = fun y -> List.for_all (fun x -> not (Eval.eq_modulo [] (get_term_context x) (get_term_context y))) delta in
                    let hypotheses = List.filter not_exist_env new_delta in
                    let proof_b = mk_Abst(t, Bindlib.unbox (Bindlib.bind_var x_var (lift new_u))) in
                    let elim_hyp = fun pb alpha ->
                        let u = Extra.IntMap.find (alpha |> get_var_context |> Bindlib.uid_of) new_mu in
                        let fu = Term.add_args (mk_Symb f) u in
                        Common.Console.out 4 "ELIM HYPOTHESIS (ABST) : [%a]@." Print.pp_term pb;
                        elim_hypothesis sign (find_term fu new_inst_map) u f x y a pa formula pb
                    in
                    delta, List.fold_left elim_hyp proof_b hypotheses, mu, new_inst_map
                (* |Appl(Symb({sym_name="nnpp";_}), _)  ->
                    Common.Console.out 4 "NNPP Case : [%a]@." Print.pp_term proof';
                    delta, proof', mu, inst_map' *)
                |Appl(u, v)  -> (* CAS CLASSIQUE DE APPL  *)
                    Common.Console.out 4 "[DEBUG] Appl(u, v) : @. u : [%a]@. v : [%a]@. formula : [%a]@." Print.pp_term u Print.pp_term v Print.pp_term formula;
                    let type_u (* , constraints **) = Infer.infer Unif.solve_noexn None (ax2::context) u in
                    Common.Console.out 4 "TEST@.";
                    (*match Unif.solve {Unif.empty_problem with Unif.to_solve = constraints} with
                     Some([])   -> Common.Console.out 4 "INFER OK.@."
                    |Some(_)    -> Common.Console.out 4 "INFER KO.@."
                    |None       -> Common.Console.out 4 "INFER ERROR.@."); **)
                    (*if constraints <> [] then
                        (Common.Console.out 4 "[DEBUG] Context : @.";
                        List.iter (fun (v, t) -> Common.Console.out 4 " %a : %a @." Print.pp_term (Vari(v)) Print.pp_term t) context;
                        Common.Console.out 4 "[DEBUG] Constraints on infer of [%a] : @." Print.pp_term u;
                        List.iter (fun (x, y) -> Common.Console.out 4 "[DEBUG] [%a] ≡ [%a] @." Print.pp_term x Print.pp_term y) constraints);
                    assert (constraints = []); *)
                    Common.Console.out 4 "  [DEBUG] TERM : [%a] APPL WHNF : [%a]@." Print.pp_term (unfold proof') Print.pp_term type_u;
                    let whnf_type_u = Eval.whnf [] type_u in
                    let x_var = Term.new_tvar "X" in
                    Common.Console.out 4 "[DEBUG] APPL1 Calling Deskolemize from [%a] to [%a]@." Print.pp_term proof' Print.pp_term type_u;
                    let type_v, type_w = get_prod whnf_type_u x_var in (* B should be convertible with [v/x]type_w. *)
                    Common.Console.out 4 " type(u) : [%a]@. type(v) : [%a]@." Print.pp_term type_u Print.pp_term type_v;
                    let delta_u, new_u, mu_u, new_inst_map = deskolem inst_map' context type_u u in
                    Common.Console.out 4 "[DEBUG] NEW U : [%a]@." Print.pp_term new_u;
                    Common.Console.out 4 "[DEBUG] APPL2 Calling Deskolemize from [%a] to [%a]@." Print.pp_term proof' Print.pp_term type_v;

                    let exist_delta = fun d y ->
                        if List.exists (fun x -> Eval.eq_modulo [] (get_term_context x) (get_term_context y)) delta_u then
                            d
                        else y::d
                        in
                    Common.Console.out 4 "[DEBUG] Calculating new delta in Appl@.";
                    let new_delta, new_v, mu_v, new_inst_map' =
                        let delta_v, new_v, mu_v, new_inst_map' = deskolem new_inst_map context type_v v in
                        Common.Console.out 4 "[DEBUG] NEW V : [%a]@." Print.pp_term new_v;
                        List.fold_left exist_delta delta_u delta_v, new_v, mu_v, new_inst_map' in
                    let not_exist_env = fun y -> List.for_all (fun x -> not (Eval.eq_modulo [] (get_term_context x) (get_term_context y))) delta in
                    Common.Console.out 4 "[DEBUG] Filter hypotheses in Appl@.";
                    let hypotheses = List.filter not_exist_env new_delta in
                    List.iter (fun (v, x, _) -> Common.Console.out 4 "[DEBUG] delta [%a : %a]@." Print.pp_var v Print.pp_term x) delta;
                    List.iter (fun (v, x, _) -> Common.Console.out 4 "[DEBUG] new_delta [%a : %a]@." Print.pp_var v Print.pp_term x) new_delta;
                    List.iter (fun (v, x, _) -> Common.Console.out 4 "[DEBUG] hypotheses [%a : %a]@." Print.pp_var v Print.pp_term x) hypotheses;
                    Common.Console.out 4 "[DEBUG] Generating the new proof in Appl@.";
                    let proof_b = mk_Appl(new_u, new_v) in
                    Common.Console.out 4 "[DEBUG] new_u : [%a], new_v : [%a]@." Print.pp_term new_u Print.pp_term new_v;
                    Common.Console.out 4 "[DEBUG] proof_b : [%a]@." Print.pp_term proof_b;
                    Common.Console.out 4 "[DEBUG] Eliminating hypotheses in Appl@.";
                    let elim_hyp = fun pb alpha ->
                        Common.Console.out 4 "[DEBUG] Alpha = %s@."  (Bindlib.name_of (get_var_context alpha));
                        Common.Console.out 4 "[DEBUG] MAP U v V : "; Extra.IntMap.iter (fun s t -> Common.Console.out 4 ", %d => [%a]@." s (List.pp Print.pp_term "; ") t)  (Extra.IntMap.union (fun _ x _ -> Some(x)) mu_u mu_v);
                        let u = Extra.IntMap.find (alpha |> get_var_context |> Bindlib.uid_of) (Extra.IntMap.union (fun _ x _ -> Some(x)) mu_u mu_v) in
                        Common.Console.out 4 "[DEBUG] Return the eliminated hypotheses@.";
                        let fu = Term.add_args (mk_Symb f) u in
                        Common.Console.out 4 "AVANT assoc@.";
                        Common.Console.out 4 "FU : %a@." Print.pp_term fu;
                        Common.Console.out 4 "ELIM HYPOTHESIS (APPL) : [%a]@." Print.pp_term pb;
                        let eh = elim_hypothesis sign (find_term fu new_inst_map') u f x y a pa formula pb in
                        Common.Console.out 4 "[DEBUG] Post return the eliminated hypotheses@.";
                        eh
                    in
                    Common.Console.out 4 "[DEBUG] Test convertability in Appl@.";
                    Infer.conv [] formula (subst_var x_var type_w new_v);
                    (* if Pervasives.(!Infer.constraints) <> [] then (* check if [v'/x]w ≃ B. *)
                        (Common.Console.out 4 "[DEBUG] Constraints on conv of [%a] and [%a]: @." Print.pp_term formula Print.pp_term (subst_var x_var type_w new_v);
                        List.iter (fun (_, x, y) -> Common.Console.out 4 "[DEBUG] [%a] ≡ [%a] @." Print.pp_term x Print.pp_term y) (Pervasives.(!Infer.constraints))); *)
                    Common.Console.out 4 "[DEBUG] Return delta, hypotheses, mu in Appl@.";
                    Common.Console.out 4 "[DEBUG] MAP U : "; Extra.IntMap.iter (fun s _ -> Common.Console.out 4 ", %d@." s) mu;
                    let dhm = (delta, List.fold_left elim_hyp proof_b hypotheses, mu, new_inst_map') in
                    Common.Console.out 4 "[DEBUG] Post return delta, hypotheses, mu in Appl@."; dhm
                |_      -> assert false
            end
        else
            (Common.Console.out 4 "None proof proof : [%a]@.[%a]@." Print.pp_term formula Print.pp_term proof;
            [], proof, Extra.IntMap.empty, inst_map)
        in
            deskolem inst_map context formula proof *)



let test : Sign.t -> unit = fun sign ->
    Common.Console.out 4 "[Debug] getting iota@.";
    let iota = Extra.StrMap.find "iota" !(sign.sign_builtins) in
    Common.Console.out 4 "[Debug] skolem_symbol@.";
    let f = Extra.StrMap.find "skolem_symbol" !(sign.sign_builtins) in
    Common.Console.out 4 "[Debug] symbol of A@.";
    let pa_symb = Extra.StrMap.find "A" !(sign.sign_builtins) in
    Common.Console.out 4 "[Debug] type of A@.";
    let a = unProof sign !(pa_symb.sym_type) in
    Common.Console.out 4 "[Debug] proof of A@.";
    let pa = mk_Symb(pa_symb) in
    Common.Console.out 4 "[Debug] symbol of B@.";
    let pb_symb = Extra.StrMap.find "B" !(sign.sign_builtins) in
    Common.Console.out 4 "[Debug] proof of B@.";
    let pb = mk_Symb(pb_symb) in
    Common.Console.out 4 "[Debug] type of B@.";
    let b = cleanup (!(pb_symb.sym_type)) in
    Common.Console.out 4 "[Debug] main function@.";
    (* Remove all lambdas from the proof and add all product (after removing them) in the context. *)
    Common.Console.out 4 "[DEBUG] a : %a@." Print.pp_term a;
    Common.Console.out 4 "[DEBUG] b : %a@." Print.pp_term b;
    Common.Console.out 4 "[DEBUG] pb : %a@." Print.pp_term pb;
    Common.Console.out 4 "[DEBUG] f : %a@." Print.pp_term (mk_Symb f);
    Common.Console.out 4 "[DEBUG] pa : %a@." Print.pp_term pa;
    (* Common.Console.out 4 "%a" Print.pp_term (Eval.snf [] pb) *)
    let context, proof, formula = intro_axioms [] (Eval.whnf [] pb) b in
    Common.Console.out 4 "proof after intros : %a@.formula after intros : %a@." Print.pp_term proof Print.pp_term formula;
    let _, proof', _, _ = deskolemize sign [] context a formula (Eval.snf context proof) f pa !(iota.sym_type) in
    (* Print.print_domains := true; *)
    (* Common.Console.out 4 "before : [%a]@." Print.pp_term (Eval.whnf [] pb); *)
    Common.Console.out 1 "%a@." Print.pp_term proof';
    let oc = Format.formatter_of_out_channel (open_out "test.lp") in
    Stdlib.(Common.Console.out_fmt := oc);
    Common.Console.out 4 "testing @. dada"
    (* List.iter (Common.Console.out 4 "arg : %a@." Print.pp_term) (get_option ui_ref) *)
    (* Common.Console.out 4 "B : %a@." Print.pp_term b *)
    (* let proof_term = Sign.find sign "delta" in *)
    (* let proof = get_option !(proof_term.sym_def) in *)
    (* let ui_type = (get_ui f [] !(proof_term.sym_type)) in *)
    (* let ui_proof = get_ui f [] proof in
    let ordered_ui = List.sort (fun x y -> size_args f y - size_args f x) ui_proof in
    List.iter print_args ordered_ui; *)
