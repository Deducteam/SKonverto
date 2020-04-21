require example.logic.zen as zen
require example.eprover_trace as eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))

 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))))
 ≔
 zen.nnpp (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))) (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))))

(λ ({|v_Vn|} : zen.Proof (zen.not
 (zen.imp
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))) (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))))),
 zen.Rnotimply
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))
 (λ ({|v_Vo|} : zen.Proof (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))),
 λ ({|v_Vp|} : zen.Proof (zen.not
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|})))))))),
 zen.Raxiom
 (zen.not
 (zen.exists (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} (eprover_trace.{|a|}) (eprover_trace.{|s|} (eprover_trace.{|s|} ({|v_Vm|}))))))
 ({|v_Vo|})
 ({|v_Vp|})
)
 ({|v_Vn|})
)