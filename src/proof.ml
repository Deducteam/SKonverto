open Core
open! Lplib
open Term
open Timed
open ConfigBuiltin

(** [is_axim s excluded] return true if [s] ends with string `_ax` and [s] is 
    different from [excluded]. *)
let is_axiom : string -> string -> bool = fun s excluded ->
    if String.length s > 3 && s <> excluded then
        String.sub s (String.length s - 3) 3 = "_ax"
    else
        false
        
(** [output file_name sign proof signature package] create a file that contains
    the deskolemized proof [proof] with the signature [signature]. *)
let output : string -> Sign.t -> term -> string -> string -> unit = 
    fun file_name sign proof signature package ->
    (* get the config from the signature. *)
    let cfg = get_config sign in
    (* add [deskolemized] to the file name. *)
    let file_name = (Filename.remove_extension file_name) ^ "_deskolemized.lp"  in
    let oc = Format.formatter_of_out_channel (open_out file_name) in
    Stdlib.(Common.Console.out_fmt := oc);
    (* print the required modules. *)
    Common.Console.out 1 "require open logic.fol logic.nd logic.nd_eps logic.zen;@.";
    Common.Console.out 1 "@.";
    (* print the required signature. *)
    Common.Console.out 1 "// Signature@.";
    Common.Console.out 1 "require open %s.%s;@." package signature;
    Common.Console.out 1 "@.";
    (* print the axioms. *)
    Common.Console.out 1 "// Axioms@.";
    Extra.StrMap.iter (fun _ s -> if is_axiom s.sym_name cfg.symb_Skolemized.sym_name then Common.Console.out 1 "constant symbol %s : %a;@." s.sym_name Print.term !(s.sym_type)) !(sign.sign_symbols);
    Common.Console.out 1 "@.";
    (* print the original axiom. *)
    Common.Console.out 1 "// The original axiom before skolemization@.";
    Common.Console.out 1 "constant symbol %s : %a;@." cfg.symb_Axiom.sym_name Print.term !(cfg.symb_Axiom.sym_type);
    Common.Console.out 1 "@.";
    (* print the deskolemized proof. *)
    Common.Console.out 1 "// Deskolemized proof@.";
    Common.Console.out 1 "@.symbol proof_deskolemized : ϵ ⊥@.";
    Common.Console.out 1 " ≔ @.";
    Common.Console.out 1 "%a;@." Print.term proof;
