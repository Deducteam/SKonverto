
symbol prop  : TYPE
symbol _type  : TYPE
symbol Proof : prop → TYPE
symbol term  : _type → TYPE

constant symbol iota  : _type
symbol False : prop

symbol not : prop → prop
symbol imp : prop → prop → prop

symbol forall : Π (a : _type), (term a → prop) → prop
symbol exists : Π (a : _type), (term a → prop) → prop

symbol seq : TYPE

rule seq ↪ Proof False
rule Proof False ↪ Π (p : prop), Proof p
rule Proof (not $p) ↪ Proof $p → Proof False

rule Proof (imp $p $q) ↪ Proof $p → Proof $q

rule Proof (exists $a $p) ↪ Π(P:prop), (Π(x : term $a), Proof ($p x) → Proof P) → Proof P
rule Proof (forall $a $p) ↪ Π(x : term $a), Proof ($p x)
constant symbol xmid       : Π (p : prop) (z : prop),
	     (Proof p → Proof z) →
	     (Proof (not p) → Proof z) →
	     Proof z

symbol a : term iota
symbol p : term iota → term iota →  prop
symbol f : term iota →  term iota
symbol axiom_A : Proof (forall iota (λ (X1 : (term iota)), exists iota (λ (Y : term iota), (p X1 Y ))))
type (λax_goal ax_ax, xmid (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False)) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False)) (λH2, H2) (λH3, H3 (λH4, H3 (λ_ H5, axiom_A a (Proof False) (λz _, H4 z (H5 a)) False) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False)) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False))) (xmid (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λ_, H4) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))))) (xmid (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λ_ t, xmid (not (p a t)) (not (p a t)) (λH2, H2) (λH5, H5 (λ{|v_Vt|}, H4 (λz H3, H3 t {|v_Vt|})) (not (p a t)))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|}))))) (xmid (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λ_, H4) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))))) ax_goal))) (xmid (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λ_, H4) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))))) (xmid (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λ_, H4) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))))) ax_ax)))
// type (λax_goal ax_ax, xmid (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False)) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False)) (λH2, H2) (λH3, H3 (λH4, H3 (λH5 H5, axiom_A a (Proof False) (λz h, H4 z (H5 a)) False) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False)) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) False))) (xmid (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λH5, H4) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))) (forall iota (λ{|v_Vm|}, not (p a {|v_Vm|}))))) (xmid (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λH5 t, xmid (not (p a t)) (not (p a t)) (λH2, H2) (λH5, H5 (λ{|v_Vt|}, H4 (λz H3, H3 t {|v_Vt|})) (not (p a t)))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (forall iota (λ{|v_Vn|}, not (p a {|v_Vn|}))))) (xmid (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λH5, H4) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|})))) (imp (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))) (not (exists iota (λ{|v_Vm|}, p a {|v_Vm|}))))) ax_goal))) (xmid (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λH5, H4) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))))) (xmid (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (λH2, H2) (λH3, H3 (λH4, H3 (λH5, H4) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|})))) (imp (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))) (forall iota (λ{|v_Vm|}, p {|v_Vm|} (f {|v_Vm|}))))) ax_ax)))