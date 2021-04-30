require example.test_e as test_e
require example.lemmas.{|c_0_2|} as {|c_0_2|}
require example.lemmas.{|c_0_3|} as {|c_0_3|}
require example.lemmas.{|c_0_4|} as {|c_0_4|}
require example.lemmas.{|c_0_5|} as {|c_0_5|}
require example.lemmas.{|c_0_6|} as {|c_0_6|}
require example.lemmas.{|c_0_7|} as {|c_0_7|}

require example.logic.zen as zen

symbol iota_b : zen.term zen.iota

symbol axiom_A : zen.Proof (zen.forall (zen.iota) (λ (X1 : (zen.term zen.iota)), zen.exists (zen.iota) (λ (Y : zen.term zen.iota), (test_e.{|p|} X1 Y ))))
definition proof_test_e
 (ax_goal : zen.Proof (zen.not (zen.exists (zen.iota) (λ(X2 : (zen.term zen.iota)), ((test_e.{|p|} test_e.{|a|} X2 ))))))
 (ax_ax : zen.Proof (zen.forall (zen.iota) (λ (X1 : (zen.term zen.iota)), (test_e.{|p|} X1 (test_e.{|f|} X1 ) ))))
  : zen.seq

 ≔

let {|lemmas_c_0_2|} ≔ {|c_0_2|}.delta ax_goal  in
let {|lemmas_c_0_3|} ≔ {|c_0_3|}.delta {|lemmas_c_0_2|}  in
let {|lemmas_c_0_4|} ≔ {|c_0_4|}.delta ax_ax  in
let {|lemmas_c_0_5|} ≔ {|c_0_5|}.delta {|lemmas_c_0_3|}  in
let {|lemmas_c_0_6|} ≔ {|c_0_6|}.delta {|lemmas_c_0_4|}  in
let {|lemmas_c_0_7|} ≔ {|c_0_7|}.delta {|lemmas_c_0_5|} {|lemmas_c_0_6|}  in
{|lemmas_c_0_7|}

set builtin "skolem_symbol" ≔ test_e.{|f|}
set builtin "A" ≔ axiom_A
set builtin "B" ≔ proof_test_e
set builtin "iota" ≔ iota_b