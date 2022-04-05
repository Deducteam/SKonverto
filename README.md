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

See [example](https://github.com/Deducteam/SKonverto/blob/master/example/proof_skolem.lp).
