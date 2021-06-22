# SKonverto
SKonverto is a tool that transforms Lambdapi proofs containing Skolem symbols 
into proofs without these symbols. It is based on the approach used in 
(http://www.lsv.fr/~dowek/Publi/skolem.pdf).

## Installation
To install SKonverto, you need to install all these dependencies:
- dune
- lambdapi (https://github.com/Deducteam/lambdapi)
- OCaml >= 4.07.1

### Compilation
```bash
    git clone https://github.com/elhaddadyacine/SKonverto
    cd SKonverto
    make
    make install
```
### Use
```bash
    skonverto path_to_the_lambdapi_file.lp
```

### Example
```
require open logic.fol logic.nd logic.nd_eps logic.zen; // files available in (https://github.com/elhaddadyacine/zenon_modulo/tree/modulo_lp/logic)

// signature 
constant symbol a : κ;
constant symbol p : κ → κ → Prop;
constant symbol s : κ → κ;
constant symbol f : κ → κ;

// axiom that is skolemized
symbol axiom_A :  ϵ (`∀ X, `∃ Y, (p X (s  Y) ));

// proof with a Skolem symbol
symbol example 
 (ax_tran : ϵ (`∀ X1, `∀ X2, `∀ X3, p X1 X2 ⇒ p X2 X3 ⇒ p X1 X3))
 // skolemized version of axiom_A
 (ax_step : ϵ (`∀ X1, (p X1 (s (f X1)))))
 (ax_congr : ϵ (`∀ X1, `∀ X2, p X1 X2 ⇒ p (s X1) (s X2)))
 (ax_goal : ϵ (¬ (`∃ X4, p a (s (s X4)))))
  : ϵ ⊥

 ≔ ax_goal (∃I (λ X4, p a (s (s X4))) (f (f a))
   (ax_tran a (s (f a)) (s (s (f (f a))))
     (ax_step a)
     (ax_congr (f a) (s (f (f a))) (ax_step (f a)))));

// builtins necessary for Skonverto
builtin "Skolem" ≔ f;
builtin "Axiom" ≔ axiom_A;
builtin "Formula" ≔ example;
builtin "iota" ≔ κ;
builtin "proof" ≔ ϵ;
builtin "imp" ≔ ⇒;
builtin "forall" ≔ ∀;
```