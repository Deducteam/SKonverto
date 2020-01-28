open Core
open Terms
open Timed

(** Set for terms. *)
module TermS =
  struct
    type t = term list
    let compare l1 l2 =
        if List.for_all2 Basics.eq l1 l2 then
            0
        else
            Pervasives.compare l1 l2
  end

module TermSet = Set.Make(TermS)

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
    Bindlib.is_closed (lift t)

let print_args l =
    List.iter (Console.out 1 "%a " Print.pp_term) l;
    Console.out 1 "@."

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
        (* let args = List.map (get_ui f l) args in *)
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

let get_option opt =
    match opt with
    | Some(x)   -> x
    | None      -> raise (Invalid_argument "The option is None.")

let comparer a b = if List.for_all2 Basics.eq a b then Console.out 1 "TRUE" else Console.out 1 "FALSE"

let test : Sign.t -> unit = fun sign ->
    let f = Sign.builtin None !(sign.sign_builtins) "skolem_symbol" in
    let proof_term = Sign.find sign "delta" in
    let proof = get_option !(proof_term.sym_def) in
    (* let ui_type = (get_ui f [] !(proof_term.sym_type)) in *)
    let ui_proof = get_ui f [] proof in
    (* List.iter print_args ui_type; *)
    (* Console.out 1 "RESULT : "; *)
    List.iter print_args ui_proof
    (* comparer (List.hd (List.hd !liste)) (List.hd (List.hd (List.tl !liste))) *)
    (*let et = existstype sign in
    Console.out 1 "%a : %a@." (Print.pp_symbol Nothing) et Print.pp_term !(et.sym_type);
    display_frozen !(et.sym_type);
    if frozen !(et.sym_type) then  Console.out 1 "FOZEN@." else Console.out 1 "NOT FROZEN@." *)