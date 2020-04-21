require example.logic.zen as zen
require example.eprover_trace as eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))) (zen.False)))
 ≔
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))) (zen.False)))

(λ ({|v_Vn|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))) (zen.False))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))) (zen.False))
 (λ ({|v_Vo|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))),
 λ ({|v_Vp|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))) (zen.False)))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|})))))))
 (zen.False)
 (λ ({|v_Vq|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|})))))))),
 λ ({|v_Vr|} : zen.Proof (zen.not
 (zen.False))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))
 (eprover_trace.{|a|})
 (λ ({|v_Vs|} : zen.Proof (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} (eprover_trace.{|a|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.not
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))
 (eprover_trace.{|f|} (eprover_trace.{|f|} (eprover_trace.{|a|})))
 (λ ({|v_Vt|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} (eprover_trace.{|a|})))))))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} (eprover_trace.{|a|}))))))
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