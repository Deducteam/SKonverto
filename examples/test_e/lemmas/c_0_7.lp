require example.logic.zen as zen
require example.test_e as test_e
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|})))) (zen.False)))
 ≔
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|})))) (zen.False)))

(λ ({|v_Vn|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|})))) (zen.False))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|})))) (zen.False))
 (λ ({|v_Vo|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vm|}))))),
 λ ({|v_Vp|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|})))) (zen.False)))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|}))))
 (zen.False)
 (λ ({|v_Vq|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|}))))),
 λ ({|v_Vr|} : zen.Proof (zen.not
 (zen.False))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 test_e.{|p|} ({|v_Vm|}) (test_e.{|f|} ({|v_Vm|})))
 (test_e.{|a|})
 (λ ({|v_Vs|} : zen.Proof (test_e.{|p|} (test_e.{|a|}) (test_e.{|f|} (test_e.{|a|})))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (test_e.{|p|} (test_e.{|a|}) ({|v_Vm|})))
 (test_e.{|f|} (test_e.{|a|}))
 (λ ({|v_Vt|} : zen.Proof (zen.not
 (test_e.{|p|} (test_e.{|a|}) (test_e.{|f|} (test_e.{|a|}))))),
 zen.Raxiom
 (test_e.{|p|} (test_e.{|a|}) (test_e.{|f|} (test_e.{|a|})))
 ({|v_Vs|})
 ({|v_Vt|})
)
 ({|v_Vo|})
)
 ({|v_Vq|})
)
 ({|v_Vp|})
)
 ({|v_Vn|})
)