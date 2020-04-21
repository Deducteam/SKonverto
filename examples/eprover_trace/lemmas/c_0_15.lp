require example.logic.zen as zen
require example.eprover_trace as eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|})))))))))
 ≔
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|})))))))))

(λ ({|v_Vo|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|}))))))
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))))
 (λ ({|v_Vp|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|}))))))),
 λ ({|v_Vq|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|})))))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|})))))))
 (λ ({|v_Vr|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|})))))),
 λ ({|v_Vs|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vm|}))))))
 (λ ({|v_Vt|} : zen.term (zen.iota)),
 λ ({|v_Vu|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|})))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))
 ({|v_Vt|})
 (λ ({|v_Vv|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vn|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))))
 (eprover_trace.{|f|} ({|v_Vt|}))
 (λ ({|v_Vw|} : zen.Proof (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vn|}))))
 (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|}))))
 (λ ({|v_Vx|} : zen.Proof (zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|})))))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|})))))))),
 zen.Ror
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|}))))))
 (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|}))))))
 (λ ({|v_Vy|} : zen.Proof (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|}))))))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|}))))))
 ({|v_Vy|})
 ({|v_Vu|})
)
 (λ ({|v_Vz|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|}))))))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) (eprover_trace.{|s|} (eprover_trace.{|f|} (eprover_trace.{|f|} ({|v_Vt|})))))
 ({|v_Vw|})
 ({|v_Vz|})
)
 ({|v_Vx|})
)
 ({|v_Vv|})
)
 ({|v_Vr|})
)
 ({|v_Vp|})
)
 ({|v_Vs|})
)
 ({|v_Vq|})
)
 ({|v_Vo|})
)