require logic.cc as cc
require logic.dk_logic as dk_logic
require logic.dk_bool as dk_bool
require logic.zen as zen

definition bool ≔
  dk_bool.bool

definition Bool ≔
  dk_bool.Bool

definition true ≔
  dk_bool.true

definition false ≔
  dk_bool.false

definition not ≔
  dk_bool.not

definition {|and|} ≔
  dk_bool.{|and|}

definition or ≔
  dk_bool.or

definition xor ≔
  dk_bool.xor

definition if ≔
  dk_bool.ite

definition ifb ≔
  dk_bool.iteb

definition match ≔
  dk_bool.match

definition Prop ≔
  dk_logic.Prop

definition eP ≔
  dk_logic.eP

definition eeP : Prop → cc.uT ≔
  dk_logic.eeP

definition True ≔
  dk_logic.True

definition False ≔
  dk_logic.False

definition TrueT ≔
  dk_logic.TrueT

definition FalseT ≔
  dk_logic.FalseT

definition Not ≔
  dk_logic.not

definition NotNot : Prop → Prop ≔
  λ(H : Prop), Not (Not H)

definition And ≔
  dk_logic.{|and|}

definition Or ≔
  dk_logic.or

definition Imp ≔
  dk_logic.imp

definition Eqv ≔
  dk_logic.eqv

definition Forall ≔
  dk_logic.forall

definition Forallb ≔
  Forall bool

definition equal ≔
  zen.equal

definition eqb ≔
  equal bool

definition refl ≔
  dk_logic.refl bool

definition sym ≔
  dk_logic.equal_sym bool

definition tt : TrueT ≔
  λ(P : dk_logic.Prop), λ(H : eP P), H

definition ff (H : FalseT) : FalseT ≔
  H

definition is_true : Bool → Prop ≔
  dk_logic.ebP

definition Is_true (b : Bool) ≔
  is_true b

definition zenon_focal_false : eP (Not (Is_true false)) ≔
  ff

definition zenon_focal_nottrue (H : eP (Not (Is_true true))) : FalseT ≔
  H tt

definition zenon_focal_trueequal (x : Bool) (H : eP (Not (Is_true x))) (G : eP (eqb true x)) : FalseT ≔
  H (G Is_true tt)

definition zenon_focal_equaltrue (x : Bool) (H : eP (Not (Is_true x))) (G : eP (eqb x true)) : FalseT ≔
  zenon_focal_trueequal x H (sym x true G)

definition zenon_focal_truenotequal : Π(x : Bool), eP (NotNot (Is_true x)) → eP (NotNot (eqb true x)) ≔
  match (λ(x : Bool), eeP (Imp (NotNot (Is_true x)) (NotNot (eqb true x)))) (λ(H : eP (NotNot True)), λ(G : eP (Not (eqb true true))), G (refl true)) (λ(H : eP (NotNot False)), λ(G : eP (Not (eqb true false))), H ff)

definition zenon_focal_notequaltrue (x : Bool) (H : eP (NotNot (Is_true x))) (Abs : eP (Not (eqb x true))) : FalseT ≔
  zenon_focal_truenotequal x H (λ(G : eP (eqb true x)), Abs (sym true x G))

definition zenon_focal_falseequal : Π(x : Bool), eP (NotNot (Is_true x)) → eP (Not (eqb false x)) ≔
  match (λ(x : Bool), eeP (Imp (NotNot (Is_true x)) (Not (eqb false x)))) (λ(H : eP (NotNot True)), λ(G : eP (eqb false true)), G (λ(x : Bool), Is_true (not x)) tt) (λ(H : eP (NotNot False)), λ(G : eP (eqb false false)), H ff)

definition zenon_focal_equalfalse (x : Bool) (H : eP (NotNot (Is_true x))) (G : eP (eqb x false)) : FalseT ≔
  zenon_focal_falseequal x H (sym x false G)

definition zenon_focal_falsenotequal : Π(x : Bool), eP (Not (Is_true x)) → eP (NotNot (eqb false x)) ≔
  match (λ(x : Bool), eeP (Imp (Not (Is_true x)) (NotNot (eqb false x)))) (λ(H : eP (Not True)), λ(G : eP (Not (eqb false true))), H tt) (λ(H : eP (Not False)), λ(G : eP (Not (eqb false false))), G (refl false))

definition zenon_focal_notequalfalse (x : Bool) (H : eP (Not (Is_true x))) (G : eP (Not (eqb x false))) : FalseT ≔
  zenon_focal_falsenotequal x H (λ(E : eP (eqb false x)), G (sym false x E))

definition zenon_focal_not : Π(a : Bool), eP (NotNot (Is_true a)) → eP (Not (Is_true (not a))) ≔
  match (λ(a : Bool), eeP (Imp (NotNot (Is_true a)) (Not (Is_true (not a))))) (λ(H : eP (NotNot True)), λ(G : FalseT), G) (λ(H : eP (NotNot False)), λ(G : TrueT), H ff)

definition zenon_focal_notnot : Π(a : Bool), eP (Not (Is_true a)) → eP (NotNot (Is_true (not a))) ≔
  match (λ(a : Bool), eeP (Imp (Not (Is_true a)) (NotNot (Is_true (not a))))) (λ(H : eP (Not True)), λ(G : eP (Not False)), H tt) (λ(H : eP (Not False)), λ(G : eP (Not True)), G tt)

definition zenon_focal_and : Π(a : Bool), Π(b : Bool), eP (Not (And (Is_true a) (Is_true b))) → eP (Is_true ({|and|} a b)) → FalseT ≔
  match (λ(a : Bool), eeP (Forallb (λ(b : Bool), Imp (Not (And (Is_true a) (Is_true b))) (Not (Is_true ({|and|} a b)))))) (λ(b : Bool), λ(H : eP (Not (And True (Is_true b)))), λ(G : eP (Is_true b)), H (λ(P : Prop), λ(I : TrueT → eP (Is_true b) → eP P), I tt G)) (λ(b : Bool), λ(H : eP (Not (And False (Is_true b)))), λ(G : FalseT), G)

definition zenon_focal_notand : Π(a : Bool), Π(b : Bool), eP (NotNot (And (Is_true a) (Is_true b))) → eP (NotNot (Is_true ({|and|} a b))) ≔
  match (λ(a : Bool), eeP (Forallb (λ(b : Bool), Imp (NotNot (And (Is_true a) (Is_true b))) (NotNot (Is_true ({|and|} a b)))))) (λ(b : Bool), λ(H : eP (NotNot (And True (Is_true b)))), λ(G : eP (Not (Is_true b))), H (λ(I : eP (And True (Is_true b))), G (I (Is_true b) (λ(tt : TrueT), λ(J : eP (Is_true b)), J)))) (λ(b : Bool), λ(H : eP (NotNot (And False (Is_true b)))), λ(G : eP (Not False)), H (λ(I : eP (And False (Is_true b))), I False (λ(ff : FalseT), λ(J : eP (Is_true b)), ff)))

definition zenon_focal_or : Π(a : Bool), Π(b : Bool), eP (Not (Or (Is_true a) (Is_true b))) → eP (Not (Is_true (or a b))) ≔
  match (λ(a : Bool), eeP (Forallb (λ(b : Bool), Imp (Not (Or (Is_true a) (Is_true b))) (Not (Is_true (or a b)))))) (λ(b : Bool), λ(H : eP (Not (Or True (Is_true b)))), λ(G : TrueT), H (λ(P : Prop), λ(Hl : TrueT → eP P), λ(Hr : eP (Is_true b) → eP P), Hl tt)) (λ(b : Bool), λ(H : eP (Not (Or False (Is_true b)))), λ(G : eP (Is_true b)), H (λ(P : Prop), λ(Hl : FalseT → eP P), λ(Hr : eP (Is_true b) → eP P), Hr G))

definition zenon_focal_notor : Π(a : Bool), Π(b : Bool), eP (NotNot (Or (Is_true a) (Is_true b))) → eP (NotNot (Is_true (or a b))) ≔
  match (λ(a : Bool), eeP (Forallb (λ(b : Bool), Imp (NotNot (Or (Is_true a) (Is_true b))) (NotNot (Is_true (or a b)))))) (λ(b : Bool), λ(H : eP (NotNot (Or True (Is_true b)))), λ(G : eP (Not True)), G tt) (λ(b : Bool), λ(H : eP (NotNot (Or False (Is_true b)))), λ(G : eP (Not (Is_true b))), H (λ(I : eP (Or False (Is_true b))), G (I (Is_true b) (λ(J : FalseT), J (Is_true b)) (λ(J : eP (Is_true b)), J))))

definition zenon_focal_xor : Π(a : Bool), Π(b : Bool), eP (NotNot (Eqv (Is_true a) (Is_true b))) → eP (Not (Is_true (xor a b))) ≔
  match (λ(a : Bool), eeP (Forallb (λ(b : Bool), Imp (NotNot (Eqv (Is_true a) (Is_true b))) (Not (Is_true (xor a b)))))) (λ(b : Bool), λ(H : eP (NotNot (Eqv True (Is_true b)))), zenon_focal_not b (λ(I : eP (Not (Is_true b))), H (λ(J : eP (Eqv True (Is_true b))), J False (λ(H1 : TrueT → eP (Is_true b)), λ(H2 : eP (Is_true b) → TrueT), I (H1 tt))))) (λ(b : Bool), λ(H : eP (NotNot (Eqv False (Is_true b)))), λ(G : eP (Is_true b)), H (λ(I : eP (Eqv False (Is_true b))), I False (λ(H1 : FalseT → eP (Is_true b)), λ(H2 : eP (Is_true b) → FalseT), H2 G)))

definition zenon_focal_notxor : Π(a : Bool), Π(b : Bool), eP (Not (Eqv (Is_true a) (Is_true b))) → eP (NotNot (Is_true (xor a b))) ≔
  match (λ(a : Bool), eeP (Forallb (λ(b : Bool), Imp (Not (Eqv (Is_true a) (Is_true b))) (NotNot (Is_true (xor a b)))))) (λ(b : Bool), λ(H : eP (Not (Eqv True (Is_true b)))), zenon_focal_notnot b (λ(I : eP (Is_true b)), H (λ(P : Prop), λ(J : (TrueT → eP (Is_true b)) → (eP (Is_true b) → TrueT) → eP P), J (λ(K : TrueT), I) (λ(K : eP (Is_true b)), tt)))) (λ(b : Bool), λ(H : eP (Not (Eqv False (Is_true b)))), λ(G : eP (Not (Is_true b))), H (λ(P : Prop), λ(I : (FalseT → eP (Is_true b)) → eP (Not (Is_true b)) → eP P), I (λ(J : FalseT), J (Is_true b)) G))

definition zenon_focal_ite_bool : Π(cond : Bool), Π(thn : Bool), Π(els : Bool), eP (Imp (Is_true cond) (Not (Is_true thn))) → eP (Imp (Not (Is_true cond)) (Not (Is_true els))) → eP (Not (Is_true (ifb cond thn els))) ≔
  match (λ(cond : Bool), eeP (Forallb (λ(thn : Bool), Forallb (λ(els : Bool), Imp (Imp (Is_true cond) (Not (Is_true thn))) (Imp (Imp (Not (Is_true cond)) (Not (Is_true els))) (Not (Is_true (ifb cond thn els)))))))) (λ(thn : Bool), λ(els : Bool), λ(H : TrueT → eP (Not (Is_true thn))), λ(G : eP (Not True) → eP (Not (Is_true els))), H tt) (λ(thn : Bool), λ(els : Bool), λ(H : FalseT → eP (Not (Is_true thn))), λ(G : eP (Not False) → eP (Not (Is_true els))), G ff)

definition zenon_focal_ite_bool_n : Π(cond : Bool), Π(thn : Bool), Π(els : Bool), eP (Imp (Is_true cond) (NotNot (Is_true thn))) → eP (Imp (Not (Is_true cond)) (NotNot (Is_true els))) → eP (NotNot (Is_true (ifb cond thn els))) ≔
  match (λ(cond : Bool), eeP (Forallb (λ(thn : Bool), Forallb (λ(els : Bool), Imp (Imp (Is_true cond) (NotNot (Is_true thn))) (Imp (Imp (Not (Is_true cond)) (NotNot (Is_true els))) (NotNot (Is_true (ifb cond thn els)))))))) (λ(thn : Bool), λ(els : Bool), λ(H : TrueT → eP (NotNot (Is_true thn))), λ(G : eP (Not True) → eP (NotNot (Is_true els))), H tt) (λ(thn : Bool), λ(els : Bool), λ(H : FalseT → eP (NotNot (Is_true thn))), λ(G : eP (Not False) → eP (NotNot (Is_true els))), G ff)

definition zenon_focal_ite_rel_l (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) : Π(cond : Bool), Π(thn : cc.eT A), Π(els : cc.eT A), Π(e2 : cc.eT B), eP (Imp (Is_true cond) (Not (r thn e2))) → eP (Imp (Not (Is_true cond)) (Not (r els e2))) → eP (Not (r (if A cond thn els) e2)) ≔
  match (λ(cond : Bool), eeP (Forall A (λ(thn : cc.eT A), Forall A (λ(els : cc.eT A), Forall B (λ(e2 : cc.eT B), Imp (Imp (Is_true cond) (Not (r thn e2))) (Imp (Imp (Not (Is_true cond)) (Not (r els e2))) (Not (r (if A cond thn els) e2)))))))) (λ(thn : cc.eT A), λ(els : cc.eT A), λ(e2 : cc.eT B), λ(H : TrueT → eP (Not (r thn e2))), λ(G : eP (Not True) → eP (Not (r els e2))), H tt) (λ(thn : cc.eT A), λ(els : cc.eT A), λ(e2 : cc.eT B), λ(H : FalseT → eP (Not (r thn e2))), λ(G : eP (Not False) → eP (Not (r els e2))), G ff)

definition zenon_focal_ite_rel_r (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) (e1 : cc.eT A) (cond : Bool) (thn : cc.eT B) (els : cc.eT B) (H : eP (Is_true cond) → eP (Not (r e1 thn))) (G : eP (Not (Is_true cond)) → eP (Not (r e1 els))) : eP (Not (r e1 (if B cond thn els))) ≔
  zenon_focal_ite_rel_l B A (λ(b : cc.eT B), λ(a : cc.eT A), r a b) cond thn els e1 H G

definition zenon_focal_ite_rel_nl (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) (cond : Bool) (thn : cc.eT A) (els : cc.eT A) (e2 : cc.eT B) (H : eP (Is_true cond) → eP (NotNot (r thn e2))) (G : eP (Not (Is_true cond)) → eP (NotNot (r els e2))) : eP (NotNot (r (if A cond thn els) e2)) ≔
  zenon_focal_ite_rel_l A B (λ(a : cc.eT A), λ(b : cc.eT B), Not (r a b)) cond thn els e2 H G

definition zenon_focal_ite_rel_nr (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) (e1 : cc.eT A) (cond : Bool) (thn : cc.eT B) (els : cc.eT B) (H : eP (Is_true cond) → eP (NotNot (r e1 thn))) (G : eP (Not (Is_true cond)) → eP (NotNot (r e1 els))) : eP (NotNot (r e1 (if B cond thn els))) ≔
  zenon_focal_ite_rel_r A B (λ(a : cc.eT A), λ(b : cc.eT B), Not (r a b)) e1 cond thn els H G

definition zenon_focal_istrue_true : Π(e : Bool), eP (Not (eqb e true)) → eP (Not (Is_true e)) ≔
  match (λ(e : Bool), eeP (Imp (Not (eqb e true)) (Not (Is_true e)))) (λ(H : eP (Not (eqb true true))), λ(G : TrueT), H (refl true)) (λ(H : eP (Not (eqb false true))), ff)

definition zenon_focal_notistrue_false : Π(e : Bool), eP (Not (eqb e false)) → eP (NotNot (Is_true e)) ≔
  match (λ(e : Bool), eeP (Imp (Not (eqb e false)) (NotNot (Is_true e)))) (λ(H : eP (Not (eqb true false))), λ(G : eP (Not True)), G tt) (λ(H : eP (Not (eqb false false))), λ(G : eP (Not False)), H (refl false))

constant symbol zenon_focal_eqdec : Π(T : cc.uT), Π(x : cc.eT T), Π(y : cc.eT T), eP (Or (equal T x y) (Not (equal T x y)))

definition zenon_focal_false_s ≔
  zenon_focal_false

definition zenon_focal_nottrue_s ≔
  zenon_focal_nottrue

definition zenon_focal_trueequal_s (x : Bool) (c : eP (eqb true x)) (h : eP (Not (Is_true x))) ≔
  zenon_focal_trueequal x h c

definition zenon_focal_equaltrue_s (x : Bool) (c : eP (eqb x true)) (h : eP (Not (Is_true x))) ≔
  zenon_focal_equaltrue x h c

definition zenon_focal_truenotequal_s (x : Bool) (c : eP (Not (eqb true x))) (h : eP (NotNot (Is_true x))) ≔
  zenon_focal_truenotequal x h c

definition zenon_focal_notequaltrue_s (x : Bool) (c : eP (eqb x true)) (h : eP (Not (Is_true x))) ≔
  zenon_focal_equaltrue x h c

definition zenon_focal_falseequal_s (x : Bool) (c : eP (eqb false x)) (h : eP (NotNot (Is_true x))) ≔
  zenon_focal_falseequal x h c

definition zenon_focal_equalfalse_s (x : Bool) (c : eP (eqb x false)) (h : eP (NotNot (Is_true x))) ≔
  zenon_focal_equalfalse x h c

definition zenon_focal_falsenotequal_s (x : Bool) (c : eP (Not (eqb false x))) (h : eP (Not (Is_true x))) ≔
  zenon_focal_falsenotequal x h c

definition zenon_focal_notequalfalse_s (x : Bool) (c : eP (Not (eqb x false))) (h : eP (Not (Is_true x))) ≔
  zenon_focal_notequalfalse x h c

definition zenon_focal_not_s (a : Bool) (c : eP (Is_true (not a))) (h : eP (NotNot (Is_true a))) ≔
  zenon_focal_not a h c

definition zenon_focal_notnot_s (a : Bool) (c : eP (Not (Is_true (not a)))) (h : eP (Not (Is_true a))) ≔
  zenon_focal_notnot a h c

definition zenon_focal_and_s (a : Bool) (b : Bool) (c : eP (Is_true ({|and|} a b))) (h : eP (Not (And (Is_true a) (Is_true b)))) ≔
  zenon_focal_and a b h c

definition zenon_focal_notand_s (a : Bool) (b : Bool) (c : eP (Not (Is_true ({|and|} a b)))) (h : eP (NotNot (And (Is_true a) (Is_true b)))) ≔
  zenon_focal_notand a b h c

definition zenon_focal_or_s (a : Bool) (b : Bool) (c : eP (Is_true (or a b))) (h : eP (Not (Or (Is_true a) (Is_true b)))) ≔
  zenon_focal_or a b h c

definition zenon_focal_notor_s (a : Bool) (b : Bool) (c : eP (Not (Is_true (or a b)))) (h : eP (NotNot (Or (Is_true a) (Is_true b)))) ≔
  zenon_focal_notor a b h c

definition zenon_focal_xor_s (a : Bool) (b : Bool) (c : eP (Is_true (xor a b))) (h : eP (NotNot (Eqv (Is_true a) (Is_true b)))) ≔
  zenon_focal_xor a b h c

definition zenon_focal_notxor_s (a : Bool) (b : Bool) (c : eP (Not (Is_true (xor a b)))) (h : eP (Not (Eqv (Is_true a) (Is_true b)))) ≔
  zenon_focal_notxor a b h c

definition zenon_focal_ite_bool_s (cond : Bool) (thn : Bool) (els : Bool) (c : eP (Is_true (ifb cond thn els))) (h1 : eP (Imp (Is_true cond) (Not (Is_true thn)))) (h2 : eP (Imp (Not (Is_true cond)) (Not (Is_true els)))) ≔
  zenon_focal_ite_bool cond thn els h1 h2 c

definition zenon_focal_ite_bool_n_s (cond : Bool) (thn : Bool) (els : Bool) (c : eP (Not (Is_true (ifb cond thn els)))) (h1 : eP (Imp (Is_true cond) (NotNot (Is_true thn)))) (h2 : eP (Imp (Not (Is_true cond)) (NotNot (Is_true els)))) ≔
  zenon_focal_ite_bool_n cond thn els h1 h2 c

definition zenon_focal_ite_rel_l_s (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) (cond : Bool) (thn : cc.eT A) (els : cc.eT A) (e2 : cc.eT B) (c : eP (r (if A cond thn els) e2)) (h1 : eP (Is_true cond) → eP (Not (r thn e2))) (h2 : eP (Not (Is_true cond)) → eP (Not (r els e2))) ≔
  zenon_focal_ite_rel_l A B r cond thn els e2 h1 h2 c

definition zenon_focal_ite_rel_r_s (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) (e1 : cc.eT A) (cond : Bool) (thn : cc.eT B) (els : cc.eT B) (c : eP (r e1 (if B cond thn els))) (h1 : eP (Is_true cond) → eP (Not (r e1 thn))) (h2 : eP (Not (Is_true cond)) → eP (Not (r e1 els))) ≔
  zenon_focal_ite_rel_r A B r e1 cond thn els h1 h2 c

definition zenon_focal_ite_rel_nl_s (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) (cond : Bool) (thn : cc.eT A) (els : cc.eT A) (e2 : cc.eT B) (c : eP (Not (r (if A cond thn els) e2))) (h1 : eP (Is_true cond) → eP (NotNot (r thn e2))) (h2 : eP (Not (Is_true cond)) → eP (NotNot (r els e2))) ≔
  zenon_focal_ite_rel_nl A B r cond thn els e2 h1 h2 c

definition zenon_focal_ite_rel_nr_s (A : cc.uT) (B : cc.uT) (r : cc.eT A → cc.eT B → Prop) (e1 : cc.eT A) (cond : Bool) (thn : cc.eT B) (els : cc.eT B) (c : eP (Not (r e1 (if B cond thn els)))) (h1 : eP (Is_true cond) → eP (NotNot (r e1 thn))) (h2 : eP (Not (Is_true cond)) → eP (NotNot (r e1 els))) ≔
  zenon_focal_ite_rel_nr A B r e1 cond thn els h1 h2 c

constant symbol syntactic_equal : Π(A : cc.uT), cc.eT A → cc.eT A → dk_bool.Bool

constant symbol zenon_syntactic_equal : Π(A : cc.uT), Π(x : cc.eT A), Π(y : cc.eT A), eP (Not (equal A x y)) → eP (Not (Is_true (syntactic_equal A x y)))

constant symbol zenon_not_syntactic_equal : Π(A : cc.uT), Π(x : cc.eT A), Π(y : cc.eT A), eP (NotNot (equal A x y)) → eP (NotNot (Is_true (syntactic_equal A x y)))

definition zenon_focal_not_all_bool (P : Bool → Prop) (h1 : eP (NotNot (P true))) (h2 : eP (NotNot (P false))) (hc : eP (Not (dk_logic.forall bool P))) ≔
  hc (match (λ(b : Bool), eeP (P b)) (zen.nnpp (P true) h1) (zen.nnpp (P false) h2))

definition zenon_focal_ex_bool (P : Bool → Prop) (h1 : eP (Not (P true))) (h2 : eP (Not (P false))) (hc : eP (dk_logic.exists bool P)) : eP False ≔
  hc False (match (λ(b : Bool), eeP (Not (P b))) h1 h2)
