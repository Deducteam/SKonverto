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

let frozen : term -> bool = fun t ->
    Bindlib.is_closed (Bindlib.box t)

let rec display_frozen : term -> unit = fun t ->
    match t with
    | Vari _
    | Type
    | Kind                      -> ()
    | Symb(_, _)                -> Console.out 1 "SYMB : %a@." Print.pp_term t
    | Prod( a, b)               ->
        let (_, b) = Bindlib.unbind b in
        Console.out 1 "PROD : %a => %a@." Print.pp_term a Print.pp_term b
    | Abst( a, b)               ->
        let (_, b) = Bindlib.unbind b in
        if frozen b then Console.out 1 "%a is FROOOOOOOZEN@." Print.pp_term b else Console.out 1 "%a is NOOOOOOOOO@." Print.pp_term b;
        Console.out 1 "ABST : %a, %a@." Print.pp_term a Print.pp_term b
    | Appl( a, b)               ->
        Console.out 1 "APP : (%a) (%a)@." Print.pp_term a Print.pp_term b;
        display_frozen a; display_frozen b
    | Meta _
    | Patt _
    | TEnv _
    | Wild
    | TRef _                    -> assert false (* is not handled in the encoding. *)

let existstype =
    fun sign -> Sign.find sign "frozen"
let test sign =
    let et = existstype sign in
    Console.out 1 "%a : %a@." (Print.pp_symbol Nothing) et Print.pp_term !(et.sym_type);
    display_frozen !(et.sym_type);
    if frozen !(et.sym_type) then  Console.out 1 "FOZEN@." else Console.out 1 "NOT FROZEN@."