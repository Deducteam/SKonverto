require logic.zen as zen
require eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vo|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vo|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vo|})) (eprover_trace.{|s|} ({|v_Vp|}))))))) 
 ≔ 
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vo|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vo|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vo|})) (eprover_trace.{|s|} ({|v_Vp|})))))))

(λ ({|v_Vq|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vo|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vo|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vo|})) (eprover_trace.{|s|} ({|v_Vp|}))))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))))))
 (zen.forall (zen.iota)
 (λ ({|v_Vo|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vo|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vo|})) (eprover_trace.{|s|} ({|v_Vp|}))))))
 (λ ({|v_Vr|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))))))),
 λ ({|v_Vs|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vo|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vo|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vo|})) (eprover_trace.{|s|} ({|v_Vp|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vo|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vo|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vo|})) (eprover_trace.{|s|} ({|v_Vp|})))))
 (λ ({|v_Vt|} : zen.term (zen.iota)),
 λ ({|v_Vu|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vp|}))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vp|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vp|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vp|}))))
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 λ ({|v_Vw|} : zen.Proof (zen.not
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|}))) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vv|})))))),
 zen.Rnotor
 (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|})))
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vv|})))
 (λ ({|v_Vx|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|}))))),
 λ ({|v_Vy|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vv|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|}))
 (λ ({|v_Vz|} : zen.Proof (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|})))))
 ({|v_Vt|})
 (λ ({|v_Vaa|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vn|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vn|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vn|}))))
 ({|v_Vv|})
 (λ ({|v_Vba|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|})) (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vv|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|}))
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vv|})))
 (λ ({|v_Vca|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vv|}))
 ({|v_Vz|})
 ({|v_Vca|})
)
 (λ ({|v_Vda|} : zen.Proof (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vv|})))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vt|})) (eprover_trace.{|s|} ({|v_Vv|})))
 ({|v_Vda|})
 ({|v_Vy|})
)
 ({|v_Vba|})
)
 ({|v_Vaa|})
)
 ({|v_Vr|})
)
 ({|v_Vx|})
)
 ({|v_Vw|})
)
 ({|v_Vu|})
)
 ({|v_Vs|})
)
 ({|v_Vq|})
)