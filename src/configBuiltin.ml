open Core
open! Lplib
open Term
open Timed

(** Builtin configuration. *)
type config =
  { symb_Skolem      : sym
  ; symb_Axiom       : sym
  ; symb_Formula     : sym
  ; symb_Skolemized  : sym
  ; symb_imp         : sym
  ; symb_forall      : sym
  ; symb_exists      : sym
  ; symb_tau         : sym
  ; symb_bot         : sym
  ; symb_proof       : sym
  ; symb_exists_elim : sym
  ; symb_iota        : sym }

(** [get_config sign] build the configuration using [sign]. *)
let get_config : Sign.t -> config = fun sign ->
  let builtin name = Extra.StrMap.find name !(sign.sign_builtins) in
  { symb_Skolem      = builtin "Skolem"
  ; symb_Axiom       = builtin "Axiom"
  ; symb_Formula     = builtin "Formula"
  ; symb_Skolemized  = builtin "SkolemizedAxiom"
  ; symb_imp         = builtin "⇒"
  ; symb_forall      = builtin "∀"
  ; symb_exists      = builtin "∃"
  ; symb_tau         = builtin "τ"
  ; symb_proof       = builtin "ϵ"
  ; symb_bot         = builtin "⊥"
  ; symb_exists_elim = builtin "∃E"
  ; symb_iota        = builtin "κ"
   }
