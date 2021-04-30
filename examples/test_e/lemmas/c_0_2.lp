require example.logic.zen as zen
require example.test_e as test_e
definition delta : zen.Proof (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))))
 ≔
 zen.nnpp (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))))

(λ ({|v_Vn|} : zen.Proof (zen.not
 (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))))),
 zen.Rnotimply
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))
 (λ ({|v_Vo|} : zen.Proof (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))),
 λ ({|v_Vp|} : zen.Proof (zen.not
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))))),
 zen.Raxiom
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))
 ({|v_Vo|})
 ({|v_Vp|})
)
 ({|v_Vn|})
)