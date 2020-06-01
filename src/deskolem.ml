open Core
open Terms
open Timed

(** [subst_inv fu x t] replaces all the subterms [fu] by a fresh variable [x] in
    the term [t]. *)
let subst_inv : term -> term Bindlib.var -> term -> term = fun fu x ->
  let rec subst t =
    if Eval.eq_modulo [] t fu then Vari x else
    match unfold t with
    | Vari _                    -> t
    | Type                      -> t
    | Kind                      -> t
    | Symb _                    -> t
    | Prod( a, b)               ->
        let (v, b) = Bindlib.unbind b in
        let sa = subst a in
        let sb = Bindlib.bind_var v (lift (subst b)) in
        Prod(sa, Bindlib.unbox sb)
    | Abst( a, b)               ->
        let (v, b) = Bindlib.unbind b in
        let sa = subst a in
        let sb = Bindlib.bind_var v (lift (subst b)) in
        Abst(sa, Bindlib.unbox sb)
    | Appl( a, b)               -> Appl(subst a, subst b)
    | Meta _
    | Patt _
    | TEnv _
    | Wild
    | LLet _
    | TRef _                    -> assert false (* is not handled in the encoding. *)
  in subst

(** [frozen t] checks if a term [t] contains free variables. *)
let frozen : term -> bool = fun t ->
    Bindlib.is_closed (lift t)

(** [print_args l] print terms that [l] contains. *)
let print_args l =
    List.iter (Console.out 1 "%a " Print.pp_term) l;
    Console.out 1 "@."

(** [get_ui f l t] returns a list of arguments used in [f]-terms inside [t]. *)
let rec get_ui : sym -> term list list -> term -> term list list = fun f l t ->
    Console.out 4 "[DEBUG] Get Uᵢ of [%a]@." Print.pp_term t;
    match unfold t with
    | Vari _
    | Type
    | Kind                      -> l
    | Symb _                    -> l
    | Prod( a, b)               ->
        let (_, b) = Bindlib.unbind b in
        let l = get_ui f l a in
        get_ui f l b
    | Abst( a, b)               ->
        let (_, b) = Bindlib.unbind b in
        let l = get_ui f l a in
        get_ui f l b
    | Appl( _, _)               ->
        let (h, args) = Basics.get_args t in
        let args_set = List.fold_left (get_ui f) l args in
        if Eval.eq_modulo [] h (Symb(f)) then
            if List.exists (List.for_all2 (Eval.eq_modulo []) args) args_set || not (frozen t) then
                args_set
            else
                args::args_set
        else
            args_set
    | Meta _                    -> Console.out 4 "[DEBUG] Meta NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | Patt _                    -> Console.out 4 "[DEBUG] Patt NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | TEnv _                    -> Console.out 4 "[DEBUG] TEnv NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | Wild                      -> Console.out 4 "[DEBUG] Wild NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | LLet _                    -> Console.out 4 "[DEBUG] LLet NOT HANDLED: [%a]@." Print.pp_term t; assert false
    | TRef _                    -> Console.out 4 "[DEBUG] TRef NOT HANDLED: [%a]@." Print.pp_term t; assert false (* is not handled in the encoding. *)

(** [get_option opt] returns [x] if [opt] is of the shape `Some x`, raise an
    Invalid_argument otherwise. *)
let get_option = fun opt ->
    match opt with
    | Some(x)   -> x
    | None      -> raise (Invalid_argument "The option is None.")

(** [size t] return the size of the term [t]. *)
let rec size : term -> int = fun t ->
  List.fold_right (fun a l -> size a + l) (snd (Basics.get_args t)) 1

(** [size_args f args] return the size of the term [f a0 a1 ... an] where args
    = [a0; a1; ...; an]. *)
let size_args : sym -> term list -> int = fun f args ->
    size (Basics.add_args (Symb(f)) args)

(** [subst_var x m n] substitutes the variable [x] with the term [n] inside the
    term [m].*)
let subst_var : term Bindlib.var -> term -> term -> term = fun x m n ->
    Bindlib.subst (Bindlib.unbox (Bindlib.bind_var x (lift m))) n

(** [subst_mvar x m n] substitutes all variables that [x] contains with the terms
    of [n] inside the term [m]. *)
let subst_mvar : term Bindlib.var list -> term -> term list -> term =
    fun x m n ->
    let x = Array.of_list x in
    let n = Array.of_list n in
    Bindlib.msubst (Bindlib.unbox (Bindlib.bind_mvar x (lift m))) n

exception Not_Proof of term

(** [unProof t] returns the proposition which is inside the `Proof` constructor. *)
let unProof : term -> term = fun t ->
    match unfold t with
    |Appl(Symb({sym_name = "π"; _}), t') -> t'
    |_                                          -> Console.out 1 "NOT PROOF : %a@." Print.pp_term t; raise (Not_Proof t)

(** [is_total_instance a b f x y] checks if [b] is a total instance of [a] where
    we substitute [y] with [f x]. *)
let is_total_instance :
    term -> term -> sym -> term Bindlib.var list -> term Bindlib.var
    -> term list option = fun a b f x y ->
    let fx = Basics.add_args (Symb(f)) (List.map (fun x -> Vari x) x) in
    (* Calculate the strong normal form before adding the TRef since we can not
        do it with TRef. *)
    let a = Eval.snf [] a in
    let a' = subst_var y a fx in
    let x_tref = Array.init (List.length x) (fun _ -> TRef(ref None)) in
    let a' = subst_mvar x a' (Array.to_list x_tref) in (* FIXME to_list is called before of_list in susbt_mvar *)
    let nf_a = a' in
    let nf_b = Eval.snf [] b in
    (* Console.out 1 "NFA : %a@.NFB : %a@." Print.pp_term nf_a Print.pp_term nf_b; *)
    if Rewrite.eq [] nf_a nf_b then
        let ui_tref = Array.to_list x_tref in
        let get_content = fun t -> match t with
            | TRef(r)    -> (match !r with Some(a) -> a | _ -> assert false)
            | _          -> assert false in
        Some(List.map get_content ui_tref)
    else
        None

(** [construct_delta f a x y t] build the context
    [α₀ : (fu⁰/y, u⁰/x) a, α₁ : (fu¹/y, u¹/x) a, ..., αₖ : (fuᵏ/y, uᵏ/x) a ]
    where [uⁱ] are the arguments of [f] inside [t]. *)
let construct_delta :
    Sign.t -> (term * tvar) list -> sym -> term -> term Bindlib.var list -> term Bindlib.var -> term list list
    -> ctxt * term list Extra.IntMap.t * (term * tvar) list = fun sign inst_map f a x y ui ->
    Console.out 1 "Ui : @.";
    List.iter (fun l -> List.iter (Console.out 1 "Ui : %a@." Print.pp_term) l) ui;
    let fx = Basics.add_args (Symb(f)) (List.map (fun x -> Vari x) x) in
    let a_y = subst_var y a fx in
    let add_context = fun (e, m, inst_map) u ->
        let ax = subst_mvar x a_y u in
        Console.out 1 "Construct Delta : AX = %a@." Print.pp_term ax;
        let pi = Extra.StrMap.find "proof" !(sign.sign_builtins) in 
        let pi_ax = Appl(Symb pi, ax) in
        let var, inst_map = 
                try 
                    snd (List.find (fun (x, _) -> Eval.eq_modulo [] pi_ax x) inst_map), inst_map
                with Not_found -> let v = Bindlib.new_var mkfree "alpha" in v, (pi_ax, v)::inst_map in
        (var, pi_ax, None)::e, Extra.IntMap.add (Bindlib.uid_of var) u m, inst_map in
    List.fold_left add_context ([], Extra.IntMap.empty, inst_map) ui 

(** [get_x t] return the list of quantified variables [x₀; x₁; ...; xₙ] and a
    term [b] if [t] is of the form : [∀x₀x₁xₙ. b]. *)
let rec get_x : term -> term Bindlib.var list * term = fun t ->
    let s, args = Basics.get_args t in
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
    let s, args = Basics.get_args t in
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
    Console.out 1 "[DEBUG] First step in elim_hypothesis@.";
    let z = Bindlib.new_var mkfree "z" in
    let fu = Basics.add_args (Symb(f)) u in
    (* (z / fu) pb. *)
    let fresh_pb = subst_inv fu z pb in (* PEUT ETRE ÇA BUG ICI A CAUSE DE L'ABSENCE DU EXISTS ET FORALL. *)
    Console.out 1 "AVANT : [%a]@." Print.pp_term pb;
    Console.out 1 "APRÈS : [%a]@." Print.pp_term fresh_pb;
    (* (u / x) a. *)
    let hu = subst_mvar x a u in
    Console.out 1 "HU : [%a]@." Print.pp_term hu;
    (* (u / x, z / y) a. *)
    let huz = subst_var y hu (Vari z) in
    Console.out 1 "HUZ : [%a]@." Print.pp_term huz;
    (* let h = Bindlib.new_var mkfree "h" in *)
    (* λ (h : huz), (z / fu) pb. *)
    let h_lambda = Abst(huz, Bindlib.unbox (Bindlib.bind_var h (lift fresh_pb))) in
    (* zen.iota *)
    Console.out 1 "[DEBUG] Iota step in elim_hypothesis@.";
    let iota = type_elm sign "iota_b" |> Basics.get_args |> snd |> List.hd in
    (* λ (z : iota), λ (h : huz), (z / fu) pb. *)
    Console.out 1 "[DEBUG] Constructing Abstraction step in elim_hypothesis@.";
    let z_lambda = Abst(iota, Bindlib.unbox (Bindlib.bind_var z (lift h_lambda))) in
    (* pa u b (λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb). *)
    Console.out 1 "[DEBUG] Final step in elim_hypothesis@.";
    let pa_u_b_l = Basics.add_args pa (u @ [unProof b; z_lambda]) in
    Console.out 1 "END ELIM HYP : [%a]@." Print.pp_term pa_u_b_l;
    pa_u_b_l

(** [get_prod t x] return [(u, v)] if [t] is of the form [∀ (x : u), v]. *)
let get_prod : term -> term Bindlib.var -> term * term = fun t x ->
    match unfold t with
    |Prod(u, v) -> u, Bindlib.subst v (Vari x)
    |_          -> assert false

let get_term_context = fun (_, x, _) -> x
let get_var_context = fun (v, _, _) -> v

let rec deskolemize : Sign.t -> (term * tvar) list -> ctxt -> term -> term -> term -> sym -> term
    -> term -> ctxt * term * term list Extra.IntMap.t = fun sign inst_map context axiom formula proof f pa iota ->
    Console.out 1 "[DEBUG] Deskolemize on @. B := [%a]@. P := [%a]@." Print.pp_term formula Print.pp_term proof;
    (* Get the variables x̅ and y. *)
    Console.out 1 "[Debug] geting [x̅] from [%a]@." Print.pp_term axiom;
    let x, a = get_x axiom in
    Console.out 1 "[Debug] geting [y] from [%a]@." Print.pp_term a;
    let y, a = get_y a in
    Console.out 1 "[Debug] construct [f(x̅)] from [%a]@." Print.pp_term a;
    let fx = Basics.add_args (Symb(f)) (List.map (fun x -> Vari x) x) in
    Console.out 1 "[Debug] replace [y] with [f(x̅)] in [%a]@." Print.pp_term a;
    let a_fx = subst_var y a fx in
    let bind_var t x_var = Abst(iota, Bindlib.unbox (Bindlib.bind_var x_var (lift t))) in
    Console.out 1 "[Debug] constructing lambdas [λ(x̅ : term iota).[f(x̅)/y]A] @.";
    let x_a_fx = List.fold_left bind_var a_fx x in
    Console.out 1 "[DEBUG] X_A_FX : [%a]@." Print.pp_term x_a_fx;
    Console.out 1 "[Debug] calculating U̅ᵢ@.";
    (* Calculate U̅ᵢ *)
    let u = get_ui f [] (unfold formula) in
    Console.out 1 "[Debug] get only Proof formulas@.";
    let add_ui u alpha =
        try
            (* Don't add ∀ x̅, (f x̅ / y) A. *)
            if Eval.eq_modulo [] (get_term_context alpha) x_a_fx then
                u
            else
                get_ui f u (get_term_context alpha)
        with Not_Proof(_) -> u in

    let u = List.fold_left add_ui u context in
    (* Sort U̅ᵢ *)
    let u = List.sort (fun x y -> size_args f y - size_args f x) u in
    (* Construct Δ. *)
    let delta, mu, inst_map' = construct_delta sign inst_map f a x y u in
    Console.out 1 "[DEBUG] DELTA  [%a] : " Print.pp_term formula;
    List.iter (fun (v, t, _) -> Console.out 1 "%a : %a," Print.pp_var v Print.pp_term t) delta;
    Console.out 1 "@.";
    Console.out 1 "[DEBUG] MU : "; Extra.IntMap.iter (fun s _ -> Console.out 4 ", %d@." s) mu;
    Console.out 1 "@.";
    (* Check if [formula] is a total instance of [a]. *)
    Console.out 1 "IS TOTAL INSTANCE [%a] OF [%a]@." Print.pp_term formula Print.pp_term a;
    let pi = Extra.StrMap.find "proof" !(sign.sign_builtins) in 
    match is_total_instance (Appl(Symb pi, a)) formula f x y with
    | Some(_)   ->
        Console.out 1 "[DEBUG] Is total instance OK";
        let alpha =
            try List.find
                (fun (_, x, _) -> Eval.eq_modulo [] formula x) delta 
            with Not_found -> assert false in
        delta, Vari(get_var_context alpha), mu
    | None      ->
        Console.out 1 " [DEBUG] PROOF : [%a]@." Print.pp_term proof;
        let proof' = Eval.whnf [] proof in
        Console.out 1 " [DEBUG] WHNF  : [%a]@." Print.pp_term proof';
        match unfold proof' with
        |Vari(_)    ->
            Console.out 1 "[DEBUG] Var : [%a]@." Print.pp_term proof';
            delta, proof', mu
        |Symb(_)    ->
            Console.out 1 "[DEBUG] Symb : [%a]@." Print.pp_term proof';
            delta, proof', mu
        |Abst(t, u) ->
            let (x_var, u) = Bindlib.unbind u in
            Console.out 1 "[DEBUG] Abst(t, u) : @. t : [%a]@. u : [%a]@. formula : [%a]@." Print.pp_term t Print.pp_term u Print.pp_term formula;
            let whnf_formula = Eval.whnf [] formula in
            Console.out 1 "  [DEBUG] TERM Abst : [%a] ABST WHNF : [%a]@." Print.pp_term (unfold proof') Print.pp_term formula;
            let t', u' = get_prod whnf_formula x_var in (* FIXME check if t = t'. *)
            Console.out 1 "[DEBUG] Adding var to the context [%a]@." Print.pp_term (Vari(x_var));
            let new_context = (x_var, t', None)::context in
            Console.out 1 "[DEBUG] APST Calling Deskolemize from [%a] to [%a]@." Print.pp_term (unfold proof') Print.pp_term u';
            let new_delta, new_u, new_mu = deskolemize sign inst_map' new_context axiom u' u f pa iota in
            let not_exist_env = fun y -> List.for_all (fun x -> not (Eval.eq_modulo [] (get_term_context x) (get_term_context y))) delta in
            let hypotheses = List.filter not_exist_env new_delta in
            let proof_b = Abst(t, Bindlib.unbox (Bindlib.bind_var x_var (lift new_u))) in
            let elim_hyp = fun pb alpha ->
                let u = Extra.IntMap.find (alpha |> get_var_context |> Bindlib.uid_of) new_mu in
                elim_hypothesis sign (get_var_context alpha) u f x y a pa formula pb
            in
            delta, List.fold_left elim_hyp proof_b hypotheses, mu
        |Appl(u, v)  ->
        Console.out 4 "[DEBUG] Appl(u, v) : @. u : [%a]@. v : [%a]@. formula : [%a]@." Print.pp_term u Print.pp_term v Print.pp_term formula;
            let type_u, constraints = Infer.infer context u in
            (match Unif.solve {Unif.empty_problem with Unif.to_solve = constraints} with
             Some([])   -> Console.out 4 "INFER OK.@."
            |Some(_)    -> Console.out 4 "INFER KO.@."
            |None       -> Console.out 4 "INFER ERROR.@.");
            (*if constraints <> [] then
                (Console.out 1 "[DEBUG] Context : @.";
                List.iter (fun (v, t) -> Console.out 1 " %a : %a @." Print.pp_term (Vari(v)) Print.pp_term t) context;
                Console.out 1 "[DEBUG] Constraints on infer of [%a] : @." Print.pp_term u;
                List.iter (fun (x, y) -> Console.out 1 "[DEBUG] [%a] ≡ [%a] @." Print.pp_term x Print.pp_term y) constraints);
            assert (constraints = []); *)
            Console.out 4 "  [DEBUG] TERM : [%a] APPL WHNF : [%a]@." Print.pp_term (unfold proof') Print.pp_term type_u;
            let whnf_type_u = Eval.whnf [] type_u in
            let x_var = Bindlib.new_var mkfree "X" in
            Console.out 4 "[DEBUG] APPL1 Calling Deskolemize from [%a] to [%a]@." Print.pp_term (unfold proof') Print.pp_term type_u;
            let type_v, type_w = get_prod whnf_type_u x_var in (* B should be convertible with [v/x]type_w. *)
            Console.out 4 " type(u) : [%a]@. type(v) : [%a]@." Print.pp_term type_u Print.pp_term type_v;
            let delta_u, new_u, mu_u = deskolemize sign inst_map' context axiom type_u u f pa iota in
            Console.out 1 "[DEBUG] APPL2 Calling Deskolemize from [%a] to [%a]@." Print.pp_term (unfold proof') Print.pp_term type_v;

            let exist_delta = fun d y ->
                if List.exists (fun x -> Eval.eq_modulo [] (get_term_context x) (get_term_context y)) delta_u then
                    d
                else y::d
                in
            Console.out 1 "[DEBUG] Calculating new delta in Appl@.";
            let new_delta, new_v, mu_v =
                if check_term_iota type_v then
                    delta_u, v, Extra.IntMap.empty
                else
                    let delta_v, new_v, mu_v = deskolemize sign inst_map' context axiom type_v v f pa iota in
                    List.fold_left exist_delta delta_u delta_v, new_v, mu_v in
            let not_exist_env = fun y -> List.for_all (fun x -> not (Eval.eq_modulo [] (get_term_context x) (get_term_context y))) delta in
            Console.out 1 "[DEBUG] Filter hypotheses in Appl@.";
            let hypotheses = List.filter not_exist_env new_delta in
            Console.out 1 "[DEBUG] Generating the new proof in Appl@.";
            let proof_b = Appl(new_u, new_v) in
            Console.out 1 "[DEBUG] Eliminating hypotheses in Appl@.";
            let elim_hyp = fun pb alpha ->
                Console.out 1 "[DEBUG] Alpha = %s@."  (Bindlib.name_of (get_var_context alpha));
                Console.out 1 "[DEBUG] MAP U v V : "; Extra.IntMap.iter (fun s _ -> Console.out 4 ", %d@." s) (Extra.IntMap.union (fun _ x _ -> Some(x)) mu_u mu_v);
                
                let u = Extra.IntMap.find (alpha |> get_var_context |> Bindlib.uid_of) (Extra.IntMap.union (fun _ x _ -> Some(x)) mu_u mu_v) in
                Console.out 1 "[DEBUG] Return the eliminated hypotheses@.";

                let eh = elim_hypothesis sign (get_var_context alpha) u f x y a pa formula pb in
                Console.out 1 "[DEBUG] Post return the eliminated hypotheses@.";
                eh
            in
            Console.out 1 "[DEBUG] Test convertability in Appl@.";
            Infer.conv [] formula (subst_var x_var type_w new_v);
            if Pervasives.(!Infer.constraints) <> [] then (* check if [v'/x]w ≃ B. *)
                (Console.out 1 "[DEBUG] Constraints on conv of [%a] and [%a]: @." Print.pp_term formula Print.pp_term (subst_var x_var type_w new_v);
                List.iter (fun (_, x, y) -> Console.out 4 "[DEBUG] [%a] ≡ [%a] @." Print.pp_term x Print.pp_term y) (Pervasives.(!Infer.constraints)));
            Console.out 1 "[DEBUG] Return delta, hypotheses, mu in Appl@.";
            Console.out 1 "[DEBUG] MAP U : "; Extra.IntMap.iter (fun s _ -> Console.out 4 ", %d@." s) mu;
            let dhm = (delta, List.fold_left elim_hyp proof_b hypotheses, mu) in
            Console.out 1 "[DEBUG] Post return delta, hypotheses, mu in Appl@."; dhm
        |_      -> assert false


let test : Sign.t -> unit = fun sign ->
    Console.out 4 "[Debug] getting iota@.";
    let iota = Extra.StrMap.find "iota" !(sign.sign_builtins) in
    Console.out 4 "[Debug] skolem_symbol@.";
    let f = Extra.StrMap.find "skolem_symbol" !(sign.sign_builtins) in
    Console.out 4 "[Debug] symbol of A@.";
    let pa_symb = Extra.StrMap.find "A" !(sign.sign_builtins) in
    Console.out 4 "[Debug] type of A@.";
    let a = unProof !(pa_symb.sym_type) in
    Console.out 4 "[Debug] proof of A@.";
    let pa = Symb(pa_symb) in
    Console.out 4 "[Debug] symbol of B@.";
    let pb_symb = Extra.StrMap.find "B" !(sign.sign_builtins) in
    Console.out 4 "[Debug] proof of B@.";
    let pb = Symb(pb_symb) in
    Console.out 4 "[Debug] type of B@.";
    let b = !(pb_symb.sym_type) in
    Console.out 4 "[Debug] main function@.";
    (* Remove all lambdas from the proof and add all product (after removing them) in the context. *)
    Console.out 1 "[DEBUG] a : %a@." Print.pp_term a;
    Console.out 1 "[DEBUG] b : %a@." Print.pp_term b;
    Console.out 1 "[DEBUG] pb : %a@." Print.pp_term pb;
    Console.out 1 "[DEBUG] f : %a@." Print.pp_term (Symb f);
    Console.out 1 "[DEBUG] pa : %a@." Print.pp_term pa;
    let _, proof, _ = deskolemize sign [] [] a b pb f pa !(iota.sym_type) in
    Console.out 1 "%a@." Print.pp_term proof
    (* List.iter (Console.out 1 "arg : %a@." Print.pp_term) (get_option ui_ref) *)
    (* Console.out 1 "B : %a@." Print.pp_term b *)
    (* let proof_term = Sign.find sign "delta" in *)
    (* let proof = get_option !(proof_term.sym_def) in *)
    (* let ui_type = (get_ui f [] !(proof_term.sym_type)) in *)
    (* let ui_proof = get_ui f [] proof in
    let ordered_ui = List.sort (fun x y -> size_args f y - size_args f x) ui_proof in
    List.iter print_args ordered_ui; *)
