require example.logic.zen as zen
require example.test_e as test_e
definition delta : zen.Proof (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vn|})))))
 ≔
 zen.nnpp (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vn|})))))

(λ ({|v_Vo|} : zen.Proof (zen.not
 (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vn|}))))))),
 zen.Rnotimply
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))
 (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vn|}))))
 (λ ({|v_Vp|} : zen.Proof (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))),
 λ ({|v_Vq|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vn|})))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vn|})))
 (λ ({|v_Vr|} : zen.term (zen.iota)),
 λ ({|v_Vs|} : zen.Proof (zen.not
 (zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vr|}))))),
 zen.Rnotnot
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vr|}))
 (λ ({|v_Vt|} : zen.Proof (test_e.{|p|} (test_e.{|a|}) ({|v_Vr|}))),
 zen.Rnotex
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))
 ({|v_Vr|})
 (λ ({|v_Vu|} : zen.Proof (zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vr|})))),
 zen.Raxiom
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vr|}))
 ({|v_Vt|})
 ({|v_Vu|})
)
 ({|v_Vp|})
)
 ({|v_Vs|})
)
 ({|v_Vq|})
)
 ({|v_Vo|})
)