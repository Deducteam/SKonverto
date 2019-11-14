open Core
open Terms

let rec subst_inv : term -> sym -> term Bindlib.var -> term =
  fun t s x ->
  match t with
  | Vari _
  | Type
  | Kind                      -> t
  | Symb(s', _) when s == s'  -> Vari x
  | Symb( _, _)               -> t
  | Prod( a, b)               ->
      let (v, b) = Bindlib.unbind b in
      let sa = subst_inv a s x in
      let sb = Bindlib.bind_var v (lift (subst_inv b s x)) in
      Prod(sa, Bindlib.unbox sb)
  | Abst( a, b)               ->
      let (v, b) = Bindlib.unbind b in
      let sa = subst_inv a s x in
      let sb = Bindlib.bind_var v (lift (subst_inv b s x)) in
      Abst(sa, Bindlib.unbox sb)
  | Appl( a, b)               ->
      let s', _ = Basics.get_args t in
      if Basics.eq (Symb(s, Nothing)) s' then
        Vari x
      else
        Appl(subst_inv a s x, subst_inv b s x)
  | _                         -> t