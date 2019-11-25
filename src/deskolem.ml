open Core
open Terms
open Timed

(** [subst_inv s x t] replaces all the subterms starting with the symbol [s] by
    a fresh variable [x] in the term [t]. *)
let rec subst_inv : sym -> term Bindlib.var -> term -> term =
  fun s x t->
  let h, ts = Basics.get_args t in
  match h with
  | Vari _
  | Type
  | Kind                      -> t
  | Symb(s', _) when s == s'  -> Vari x
  | Symb( _, _)               ->
    Basics.add_args h (List.map (subst_inv s x) ts)
  | Prod( a, b)               ->
      let (v, b) = Bindlib.unbind b in
      let sa = subst_inv s x a in
      let sb = Bindlib.bind_var v (lift (subst_inv s x b)) in
      Prod(sa, Bindlib.unbox sb)
  | Abst( a, b)               ->
      let (v, b) = Bindlib.unbind b in
      let sa = subst_inv s x a in
      let sb = Bindlib.bind_var v (lift (subst_inv s x b)) in
      Abst(sa, Bindlib.unbox sb)
  | Appl _                    -> assert false (* h could not be Appl. *)
  | Meta _
  | Patt _
  | TEnv _
  | Wild
  | TRef _                    -> assert false (* is not handled in the encoding. *)


let skolem_symbol : Sign.t -> sym = fun sign ->
  Sign.builtin None Timed.(!(sign.sign_builtins)) "skolem_symbol"

let target_type : Sign.t -> sym = fun sign ->
  Sign.builtin None Timed.(!(sign.sign_builtins)) "target_type"


let test sign =
  let sk_sym = skolem_symbol sign in
  let target = target_type sign in
  let fresh_var = Bindlib.new_var mkfree "z" in
  let transformed = subst_inv sk_sym fresh_var !(target.sym_type) in
    Console.out 1 "SKOLEM : %a@." (Print.pp_symbol Nothing) sk_sym;
    Console.out 1 "TARGET : %a@." Print.pp_term !(target.sym_type);
    Console.out 1 "TEST   : %a@." Print.pp_term transformed