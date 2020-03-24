// Calculus of Construction embedded into Lambda-Pi Modulo

constant symbol Nat : TYPE


constant symbol uT : TYPE
symbol eT : uT ⇒ TYPE

constant symbol Pi : ∀ (X : uT), ((eT X) ⇒ uT) ⇒ uT
constant symbol PiT : (uT ⇒ uT) ⇒ uT

rule eT (Pi &X &Y) → ∀ (x : (eT &X)), eT (&Y x)
rule eT (PiT &Y)   → ∀ (x : uT), eT (&Y x)

symbol Arrow : uT ⇒ uT ⇒ uT
rule Arrow &t1 &t2 → Pi &t1 (λ (x : eT &t1), &t2)