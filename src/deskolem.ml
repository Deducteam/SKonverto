open Core
open Terms
open Timed

(** [subst_inv fu x t] replaces all the subterms [fu] by a fresh variable [x] in
    the term [t]. *)
let subst_inv : term -> term Bindlib.var -> term -> term = fun fu x ->
  let rec subst t =
    if Basics.eq t fu then Vari x else
    match t with
    | Vari _
    | Type
    | Kind                      -> t
    | Symb(_, _)                -> t
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
    match t with
    | Vari _
    | Type
    | Kind                      -> l
    | Symb(_, _)                -> l
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
        if Basics.eq h (Symb(f, Nothing)) then
            if List.exists (List.for_all2 Basics.eq args) args_set || not (frozen t) then
                args_set
            else
                args::args_set
        else
            args_set
    | Meta _
    | Patt _
    | TEnv _
    | Wild
    | TRef _                    -> assert false (* is not handled in the encoding. *)

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
    size (Basics.add_args (Symb(f, Nothing)) args)

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

(** [is_total_instance a b f x y] checks if [b] is a total instance of [a] where
    we substitute [y] with [f x]. *)
let is_total_instance :
    term -> term -> sym -> term Bindlib.var list -> term Bindlib.var
    -> term list option = fun a b f x y ->
    let fx = Basics.add_args (Symb(f, Nothing)) (List.map (fun x -> Vari x) x) in
    (* Calculate the strong normal form before adding the TRef since we can not
        do it with TRef. *)
    let a = Eval.snf a in
    let a' = subst_var y a fx in
    let x_tref = Array.init (List.length x) (fun _ -> TRef(ref None)) in
    let a' = subst_mvar x a' (Array.to_list x_tref) in (* FIXME to_list is called before of_list in susbt_mvar *)
    let nf_a = a' in
    let nf_b = Eval.snf b in
    (* Console.out 1 "NFA : %a@.NFB : %a@." Print.pp nf_a Print.pp nf_b; *)
    if Basics.eq nf_a nf_b then
        let ui_tref = Array.to_list x_tref in
        let get_content = fun t -> match t with
            | TRef(r)    -> (match !r with Some(a) -> a | _ -> assert false)
            | _          -> assert false in
        let ui = List.map  get_content ui_tref in
        Some(ui)
    else
        None

(** [unProof t] returns the proposition which is inside the `Proof` constructor. *)
let unProof : term -> term = fun t ->
    match t with
    |Appl(Symb({sym_name = "Proof"; _}, _), t') -> t'
    |_                                          -> assert false

(** [construct_delta f a x y t] build the context
    [α₀ : (fu⁰/y, u⁰/x) a, α₁ : (fu¹/y, u¹/x) a, ..., αₖ : (fuᵏ/y, uᵏ/x) a ]
    where [uⁱ] are the arguments of [f] inside [t]. *)
let construct_delta :
    sym -> term -> term Bindlib.var list -> term Bindlib.var-> term -> Env.t =
    fun f a x y t ->
    let ui = get_ui f [] t in
    let fx = Basics.add_args (Symb(f, Nothing)) (List.map (fun x -> Vari x) x) in
    let a_y = subst_var y a fx in
    let a_x = List.map (subst_mvar x a_y) ui in
    let add_context = fun e ax ->
        Env.add (Bindlib.new_var mkfree "alpha") (Bindlib.box ax) e in
    List.fold_left add_context Env.empty a_x

(** [get_x t] return the list of quantified variables [x₀; x₁; ...; xₙ] and a
    term [b] if [t] is of the form : [∀x₀x₁xₙ. b]. *)
let rec get_x : term -> term Bindlib.var list * term = fun t ->
    let s, args = Basics.get_args t in
    match s with
    |Symb({sym_name = "forall"; _}, _)  ->
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
    |Symb({sym_name = "exists"; _}, _)  ->
        (
            match List.nth args 1 with
            |Abst(_, b) -> Bindlib.unbind b
            |_          -> assert false
        )
    |_                                  -> assert false

let type_elm sign s = !((Sign.find sign s).sym_type)

(** [elim_hypothesis sign u f x y a pa b pb] return a proof of [b] without the
    hypothesis [h]. if Γ,h: (u/x, fu/y)a ⊢ pb : b and Γ ⊢ pa : a return Γ ⊢
    pa u b (λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb) : b *)
let elim_hypothesis :
    Sign.t -> term list -> sym -> term Bindlib.var list ->
    term Bindlib.var -> term -> term -> term -> term -> term =
    fun sign u f x y a pa b pb ->
    let z = Bindlib.new_var mkfree "z" in
    let fu = Basics.add_args (Symb(f, Nothing)) u in
    (* (z / fu) pb. *)
    let fresh_pb = subst_inv fu z pb in
    (* (u / x) a. *)
    let hu = subst_mvar x a u in
    (* (u / x, z / y) a. *)
    let huz = subst_var y hu (Vari z) in
    let h = Bindlib.new_var mkfree "h" in
    (* λ (huz : (u/x, z/y)a), (z / fu) pb. *)
    let h_lambda = Abst(huz, Bindlib.unbox (Bindlib.bind_var h (lift fresh_pb))) in
    (* zen.iota *)
    let iota = type_elm sign "iota" |> Basics.get_args |> snd |> List.hd in
    (* λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb. *)
    let z_lambda = Abst(iota, Bindlib.unbox (Bindlib.bind_var z (lift h_lambda))) in
    (* pa u b (λ (z : iota), λ (huz : (u/x, z/y)a), (z / fu) pb). *)
    Basics.add_args pa (u @ [b; z_lambda])

let test : Sign.t -> unit = fun sign ->
    let f = Sign.builtin None !(sign.sign_builtins) "skolem_symbol" in
    let a = !((Sign.find sign "F").sym_type) in
    let a = unProof a in
    let b = unProof !((Sign.find sign "B").sym_type) in
    let x, a = get_x a in
    let y, a = get_y a in
    let ui_ref = is_total_instance a b f x y in
    List.iter (Console.out 1 "arg : %a@." Print.pp) (get_option ui_ref)
    (* Console.out 1 "B : %a@." Print.pp b *)
    (* let proof_term = Sign.find sign "delta" in *)
    (* let proof = get_option !(proof_term.sym_def) in *)
    (* let ui_type = (get_ui f [] !(proof_term.sym_type)) in *)
    (* let ui_proof = get_ui f [] proof in
    let ordered_ui = List.sort (fun x y -> size_args f y - size_args f x) ui_proof in
    List.iter print_args ordered_ui; *)
