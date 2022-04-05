require open Logic.Zenon.FOL Logic.Zenon.ND Logic.Zenon.ND_eps Logic.Zenon.zen;

// Signature
require open skolem.signature;

// Axioms
constant symbol congr_ax : ϵ (`∀ X1, `∀ X2, p X1 X2 ⇒ p (s X1) (s X2));
constant symbol goal_ax : ϵ (¬ (`∃ X4, p a (s (s X4))));
constant symbol tran_ax : ϵ (`∀ X1, `∀ X2, `∀ X3, p X1 X2 ⇒ (p X2 X3 ⇒ p X1 X3));

// The original axiom before skolemization
constant symbol axiom_A : ϵ (`∀ X, `∃ Y, p X (s Y));

// Deskolemized proof

symbol proof_deskolemized : ϵ ⊥
 ≔ 
goal_ax (λ r h, ∃E (λ z, p a (s z)) (axiom_A a) r (λ z alpha1, ∃E (λ z0, p z (s z0)) (axiom_A z) r (λ z0 alpha2, h z0 (tran_ax a (s z) (s (s z0)) alpha1 (congr_ax z (s z0) alpha2)))));
