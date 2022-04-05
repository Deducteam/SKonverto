# SKonverto
SKonverto is a tool that transforms [Lambdapi](https://github.com/Deducteam/lambdapi) proofs containing Skolem symbols 
into proofs without these symbols. It is based on the approach used in 
(http://www.lsv.fr/~dowek/Publi/skolem.pdf).


## Installation
To install `SKonverto`, you will need to install all these dependencies:
- `dune`,
- `lambdapi` (https://github.com/Deducteam/lambdapi),
- `OCaml >= 4.07.1`.

### Compilation
```bash
    git clone https://github.com/elhaddadyacine/SKonverto
    cd SKonverto
    make
    make install
```
## Use
```bash
    skonverto --signature [NAME] --package [NAME] [FILE]
```
The `lambdapi` file must follow these instructions:
- The signature file provided as option to the program should not contain a 
  Skolem symbol
- Every axiom name (except the original axiom) should end with `_ax` string 
  (example: `axiom_ax`) as it is generated with `ektraksto` 
  (https://github.com/elhaddadyacine/ekstrakto)
- A set of builtins is required by `SKonverto` :
  1. Skolem symbol
  2. Original axiom
  3. Formula that represents the proof the user wants to deskolemize
  4. Skolemized version of the axiom
- Another set of builtins to map some required symbols of the encoding
  1. Implication : ⇒
  2. Forall : ∀
  3. Exists : ∃
  4. Tau : τ (lifting codes of types to types)
  5. Epsilon : ϵ (lifting propositions to types)
  6. Bot : ⊥
  7. Exists_elim : ∃E (symbol that elimination the existential quantifier)
  8. Kappa : κ (default type for terms)

### Example
```
require open logic.fol logic.nd logic.nd_eps logic.zen; // files available in (https://github.com/elhaddadyacine/zenon_modulo/tree/modulo_lp/logic)

// Signature
require open skolem.signature;

// Skolem symbol
constant symbol f : κ → κ;

// Original axiom
symbol axiom_A :  ϵ (`∀ X, `∃ Y, (p X (s  Y) ));

// Axioms
constant symbol tran_ax : ϵ (`∀ X1, `∀ X2, `∀ X3, p X1 X2 ⇒ p X2 X3 ⇒ p X1 X3 );
constant symbol step_ax : ϵ (`∀ X1, (p X1 (s (f X1))));
constant symbol congr_ax : ϵ (`∀ X1, `∀ X2, p X1 X2 ⇒ p (s X1) (s X2));
constant symbol goal_ax : ϵ (¬ (`∃ X4, (p a (s (s X4)))));
 
// Proof to deskolemize (proof with a Skolem symbol)
symbol proof_example  : ϵ ⊥

≔ goal_ax (∃I (λ X4, p a (s (s X4))) (f (f a))
  (tran_ax a (s (f a)) (s (s (f (f a))))
    (step_ax a)
    (congr_ax (f a) (s (f (f a))) (step_ax (f a)))));

// builtins required to run SKonverto
// The Skolem symbol
builtin "Skolem" ≔ f;
// The original axiom before Skolemization
builtin "Axiom" ≔ axiom_A;
// The symbol that represents the proof that the user wants to transform
builtin "Formula" ≔ proof_example;
// The Skolemized version of the axiom
builtin "SkolemizedAxiom" ≔ step_ax;

// symbols of the encoding of first-order logic required to run SKonverto
builtin "⇒" ≔ ⇒; // Implication
builtin "∀" ≔ ∀; // Forall
builtin "∃" ≔ ∃; // Exists
builtin "τ" ≔ τ; // Tau
builtin "ϵ" ≔ ϵ; // Epsilon
builtin "⊥" ≔ ⊥; // Bot
builtin "∃E" ≔ ∃E; // Exists_elim
builtin "κ" ≔ κ; // Kappa
```
