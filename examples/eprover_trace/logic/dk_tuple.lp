require open logic.cc

constant symbol prod : uT → uT → uT
constant symbol Prod : uT → uT → TYPE
rule eT (prod $A $B) ↪ Prod $A $B

constant symbol pair : Π (A : uT) (B : uT), eT A → eT B → Prod A B

symbol fst : Π (A : uT) (B : uT), Prod A B → eT A
symbol snd : Π (A : uT) (B : uT), Prod A B → eT B

rule fst _ _ (pair _ _ $a _) ↪ $a
rule snd _ _ (pair _ _ _ $b) ↪ $b

symbol match__pair : Π (A : uT) (B : uT) (C : uT),
                     Prod A B → (eT A → eT B → eT C) → eT C → eT C

rule match__pair _ _ _ (pair _ _ $a $b) $f _ ↪ $f $a $b