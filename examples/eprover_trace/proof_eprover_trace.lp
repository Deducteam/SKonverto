require open eprover_trace.eprover_trace
require eprover_trace.lemmas.c_0_4 as c_0_4
require eprover_trace.lemmas.c_0_5 as c_0_5
require eprover_trace.lemmas.c_0_6 as c_0_6
require eprover_trace.lemmas.c_0_7 as c_0_7
require eprover_trace.lemmas.c_0_8 as c_0_8
require eprover_trace.lemmas.c_0_9 as c_0_9
require eprover_trace.lemmas.c_0_10 as c_0_10
require eprover_trace.lemmas.c_0_11 as c_0_11
require eprover_trace.lemmas.c_0_12 as c_0_12
require eprover_trace.lemmas.c_0_13 as c_0_13
require eprover_trace.lemmas.c_0_14 as c_0_14
require eprover_trace.lemmas.c_0_15 as c_0_15
require eprover_trace.lemmas.c_0_16 as c_0_16

require open eprover_trace.logic.zen

definition proof_eprover_trace 
 (ax_ax_tran : π (∀ X1, ∀ X2, ∀ X3, ((eprover_trace.p X1 X2 )) ⇒ (((eprover_trace.p X2 X3 )) ⇒ ((eprover_trace.p X1 X3 ))))))))
 (ax_ax_step : π (∀ X1, (eprover_trace.p X1 (eprover_trace.s (eprover_trace.f X1 ) ) ))))
 (ax_ax_congr : π (∀ X1, ∀ X2, ((eprover_trace.p X1 X2 )) ⇒ ((eprover_trace.p (eprover_trace.s X1 ) (eprover_trace.s X2 ) ))))))
 (ax_goal : π (∃ (X4) ((eprover_trace.p eprover_trace.a (eprover_trace.s (eprover_trace.s X4 ) ) ))))
  : seq 

 ≔ 

let lemmas_c_0_4 = c_0_4.delta ax_ax_tran  in
let lemmas_c_0_5 = c_0_5.delta ax_ax_step  in
let lemmas_c_0_6 = c_0_6.delta lemmas_c_0_4  in
let lemmas_c_0_7 = c_0_7.delta lemmas_c_0_5  in
let lemmas_c_0_8 = c_0_8.delta ax_ax_congr  in
let lemmas_c_0_9 = c_0_9.delta ax_goal  in
let lemmas_c_0_10 = c_0_10.delta lemmas_c_0_6 lemmas_c_0_7  in
let lemmas_c_0_11 = c_0_11.delta lemmas_c_0_8  in
let lemmas_c_0_12 = c_0_12.delta lemmas_c_0_9  in
let lemmas_c_0_13 = c_0_13.delta lemmas_c_0_10 lemmas_c_0_11  in
let lemmas_c_0_14 = c_0_14.delta lemmas_c_0_12  in
let lemmas_c_0_15 = c_0_15.delta lemmas_c_0_13 lemmas_c_0_7  in
let lemmas_c_0_16 = c_0_16.delta lemmas_c_0_14 lemmas_c_0_15  in
lemmas_c_0_16