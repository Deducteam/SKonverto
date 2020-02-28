require logic.zen as zen
require eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))) 
 ≔ 
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))))

(λ ({|v_Vn|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))
 (λ ({|v_Vo|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))),
 λ ({|v_Vp|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))))),
 zen.Raxiom
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))
 ({|v_Vo|})
 ({|v_Vp|})
)
 ({|v_Vn|})
)