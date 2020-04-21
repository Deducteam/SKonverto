require example.lemmas.c_0_4 as c_0_4
require example.lemmas.c_0_5 as c_0_5
require example.lemmas.c_0_6 as c_0_6
require example.lemmas.c_0_7 as c_0_7
require example.lemmas.c_0_8 as c_0_8
require example.lemmas.c_0_9 as c_0_9
require example.lemmas.c_0_10 as c_0_10
require example.lemmas.c_0_11 as c_0_11
require example.lemmas.c_0_12 as c_0_12
require example.lemmas.c_0_13 as c_0_13
require example.lemmas.c_0_14 as c_0_14
require example.lemmas.c_0_15 as c_0_15
require example.lemmas.c_0_16 as c_0_16

require example.logic.zen as zen
require example.eprover_trace as eprover_trace

symbol iota_b : zen.term zen.iota

type (zen.imp (zen.forall zen.iota (λ{|v_Vm|}, zen.not (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} {|v_Vm|}))))) (zen.imp (zen.forall zen.iota (λ{|v_Vm|},
    eprover_trace.{|p|} {|v_Vm|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} {|v_Vm|})))))) zen.False))

symbol axiom_A : zen.Proof (zen.forall (zen.iota) (λ X1, zen.exists (zen.iota) (λ Y, eprover_trace.{|p|} X1 (eprover_trace.{|s|} (Y))   )))
definition proof_eprover_trace
(ax_goal : zen.Proof (zen.not (zen.exists zen.iota (λ  X4, (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} X4))   )))))
  : zen.seq

 ≔

zen.xmid
    (zen.imp (zen.forall zen.iota (λ{|v_Vm|}, zen.not (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} {|v_Vm|}))))) (zen.imp (zen.forall zen.iota (λ{|v_Vm|},
    eprover_trace.{|p|} {|v_Vm|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} {|v_Vm|})))))) zen.False))
    (zen.imp (zen.forall zen.iota (λ{|v_Vm|}, zen.not (eprover_trace.{|p|} eprover_trace.{|a|}  (eprover_trace.{|s|} (eprover_trace.{|s|} {|v_Vm|}))))) (zen.imp (zen.forall zen.iota (λ{|v_Vm|},
    eprover_trace.{|p|} {|v_Vm|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} {|v_Vm|})))))) zen.False))
    (λH2, H2)
    (λH3, (λ{|v_Vn|}, zen.Rnotimply
        (zen.forall zen.iota (λ{|v_Vm|}, zen.not (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} {|v_Vm|})))))
        (zen.imp (zen.forall zen.iota (λ{|v_Vm|}, eprover_trace.{|p|} {|v_Vm|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} {|v_Vm|})))))) zen.False)
        (λ{|v_Vo|} {|v_Vp|}, zen.Rnotimply (zen.forall zen.iota (λ{|v_Vm|}, eprover_trace.{|p|} {|v_Vm|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} {|v_Vm|}))))))
            zen.False (λ{|v_Vq|} {|v_Vr|}, zen.Rall zen.iota (λ{|v_Vm|}, eprover_trace.{|p|} {|v_Vm|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} {|v_Vm|}))))) eprover_trace.{|a|} (λ{|v_Vs|}, zen.Rall zen.iota (λ{|v_Vm|}, zen.not (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} {|v_Vm|})))) (eprover_trace.{|f|} (eprover_trace.{|f|} eprover_trace.{|a|})) (λ{|v_Vt|}, zen.Raxiom (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} eprover_trace.{|a|}))))) {|v_Vs|} {|v_Vt|}) {|v_Vo|}) {|v_Vq|}) {|v_Vp|})
            {|v_Vn|}) H3 (zen.imp (zen.forall zen.iota (λ{|v_Vm|}, zen.not (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} {|v_Vm|}))))) (zen.imp (zen.forall zen.iota (λ{|v_Vm|}, eprover_trace.{|p|} {|v_Vm|} (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} {|v_Vm|})))))) zen.False))
        )
    (c_0_14.delta (c_0_12.delta (c_0_9.delta ax_goal)))

set builtin "skolem_symbol" ≔ eprover_trace.{|f|}
set builtin "A" ≔ axiom_A
set builtin "B" ≔ proof_eprover_trace
set builtin "iota" ≔ iota_b