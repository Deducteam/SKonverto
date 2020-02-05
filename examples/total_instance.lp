
require logic.zen as zen

symbol a : zen.term zen.iota
symbol b : zen.term zen.iota
symbol f : zen.term zen.iota ⇒ zen.term zen.iota ⇒  zen.term zen.iota
symbol p : zen.term zen.iota ⇒ zen.term zen.iota ⇒  zen.term zen.iota ⇒ zen.prop
symbol F : zen.Proof (
    zen.forall zen.iota  (λ (x1 : zen.term zen.iota),
    zen.forall zen.iota  (λ (x2 : zen.term zen.iota),
    zen.exists zen.iota  (λ (y  : zen.term zen.iota), p x1 x2 y)))
)

symbol B : zen.Proof (
    p a b (f a b)
)

// Skonverto needs to check if B is a total instance of F

set builtin "skolem_symbol" ≔ f
set builtin "B" ≔ B
set builtin "F" ≔ F