require open Logic.Zenon.FOL Logic.Zenon.ND Logic.Zenon.ND_eps Logic.Zenon.zen;

require open skolem.signature;

constant symbol f : κ → κ;

symbol axiom_A :  ϵ (`∀ X, `∃ Y, (p X (s  Y) ));

constant symbol tran_ax : ϵ (`∀ X1, `∀ X2, `∀ X3, p X1 X2 ⇒ p X2 X3 ⇒ p X1 X3 );
constant symbol step_ax : ϵ (`∀ X1, (p X1 (s (f X1))));
constant symbol congr_ax : ϵ (`∀ X1, `∀ X2, p X1 X2 ⇒ p (s X1) (s X2));
constant symbol goal_ax : ϵ (¬ (`∃ X4, (p a (s (s X4)))));
 
symbol proof_example  : ϵ ⊥

≔ goal_ax (∃I (λ X4, p a (s (s X4))) (f (f a))
  (tran_ax a (s (f a)) (s (s (f (f a))))
    (step_ax a)
    (congr_ax (f a) (s (f (f a))) (step_ax (f a)))));


builtin "Skolem" ≔ f;
builtin "Axiom" ≔ axiom_A;
builtin "Formula" ≔ proof_example;
builtin "SkolemizedAxiom" ≔ step_ax;
builtin "⇒" ≔ ⇒;
builtin "∀" ≔ ∀;
builtin "∃" ≔ ∃;
builtin "τ" ≔ τ;
builtin "ϵ" ≔ ϵ;
builtin "⊥" ≔ ⊥;
builtin "∃E" ≔ ∃E;
builtin "κ" ≔ κ;
