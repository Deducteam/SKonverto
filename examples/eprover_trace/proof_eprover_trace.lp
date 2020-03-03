require lemmas.c_0_4 as c_0_4
require lemmas.c_0_5 as c_0_5
require lemmas.c_0_6 as c_0_6
require lemmas.c_0_7 as c_0_7
require lemmas.c_0_8 as c_0_8
require lemmas.c_0_9 as c_0_9
require lemmas.c_0_10 as c_0_10
require lemmas.c_0_11 as c_0_11
require lemmas.c_0_12 as c_0_12
require lemmas.c_0_13 as c_0_13
require lemmas.c_0_14 as c_0_14
require lemmas.c_0_15 as c_0_15
require lemmas.c_0_16 as c_0_16

require logic.zen as zen
require eprover_trace

symbol axiom_A : zen.Proof (zen.forall (zen.iota) (λ X1, zen.exists (zen.iota) (λ Y, eprover_trace.{|p|} X1 (eprover_trace.{|s|} (Y))   )))
definition proof_eprover_trace
 (ax_ax_tran : zen.Proof (zen.forall (zen.iota) (λ X1, zen.forall (zen.iota) (λ X2, zen.forall (zen.iota) (λ X3, zen.imp (eprover_trace.{|p|} X1 X2 ) (zen.imp (eprover_trace.{|p|} X2 X3 ) (eprover_trace.{|p|} X1 X3 )))))))
 (ax_ax_step : zen.Proof (zen.forall (zen.iota) (λ X1, eprover_trace.{|p|} X1 (eprover_trace.{|s|} (eprover_trace.{|f|} X1))   )))
 (ax_ax_congr : zen.Proof (zen.forall (zen.iota) (λ X1, zen.forall (zen.iota) (λ X2, zen.imp (eprover_trace.{|p|} X1 X2 ) (eprover_trace.{|p|} (eprover_trace.{|s|} X1)  (eprover_trace.{|s|} X2)  )))))
 (ax_goal : zen.Proof (zen.not (zen.exists zen.iota (λ  X4, (eprover_trace.{|p|} eprover_trace.{|a|} (eprover_trace.{|s|} (eprover_trace.{|s|} X4))   )))))
  : zen.seq

 ≔

let lemmas_c_0_4 ≔ c_0_4.delta ax_ax_tran  in
let lemmas_c_0_5 ≔ c_0_5.delta ax_ax_step  in
let lemmas_c_0_6 ≔ c_0_6.delta lemmas_c_0_4  in
let lemmas_c_0_7 ≔ c_0_7.delta lemmas_c_0_5  in
let lemmas_c_0_8 ≔ c_0_8.delta ax_ax_congr  in
let lemmas_c_0_9 ≔ c_0_9.delta ax_goal  in
let lemmas_c_0_10 ≔ c_0_10.delta lemmas_c_0_6 lemmas_c_0_7  in
let lemmas_c_0_11 ≔ c_0_11.delta lemmas_c_0_8  in
let lemmas_c_0_12 ≔ c_0_12.delta lemmas_c_0_9  in
let lemmas_c_0_13 ≔ c_0_13.delta lemmas_c_0_10 lemmas_c_0_11  in
let lemmas_c_0_14 ≔ c_0_14.delta lemmas_c_0_12  in
let lemmas_c_0_15 ≔ c_0_15.delta lemmas_c_0_13 lemmas_c_0_7  in
let lemmas_c_0_16 ≔ c_0_16.delta lemmas_c_0_14 lemmas_c_0_15  in
lemmas_c_0_16

set builtin "skolem_symbol" ≔ eprover_trace.{|f|}
set builtin "A" ≔ axiom_A
set builtin "B" ≔ proof_eprover_trace
set builtin "iota" ≔ zen.iota