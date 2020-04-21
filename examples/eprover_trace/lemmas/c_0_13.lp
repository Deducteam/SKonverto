require example.logic.zen as zen
require example.eprover_trace as eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))) ({|v_Vn|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|}))))))))
 ≔
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))) ({|v_Vn|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|}))))))))

(λ ({|v_Vo|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))) ({|v_Vn|})))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))) ({|v_Vn|}))))))
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))))
 (λ ({|v_Vp|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))) ({|v_Vn|}))))))),
 λ ({|v_Vq|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|}))))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|}))))))
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|}))))))
 (λ ({|v_Vr|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|}))))))),
 λ ({|v_Vs|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vm|})) ({|v_Vn|})))))
 (λ ({|v_Vt|} : zen.term (zen.iota)),
 λ ({|v_Vu|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vn|}))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vn|}))))
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 λ ({|v_Vw|} : zen.Proof (zen.not
 (zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|})))))),
 zen.Rnotor
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vv|})))
 (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|})))
 (λ ({|v_Vx|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vv|}))))),
 λ ({|v_Vy|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|}))
 (λ ({|v_Vz|} : zen.Proof (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} ({|v_Vm|})) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})))))
 (eprover_trace.{|f|} ({|v_Vt|}))
 (λ ({|v_Vaa|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vn|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vn|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vn|}))))
 ({|v_Vv|})
 (λ ({|v_Vba|} : zen.Proof (zen.or
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|}))))),
 zen.Ror
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vv|})))
 (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|})))
 (λ ({|v_Vca|} : zen.Proof (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vv|})))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vm|}))) ({|v_Vn|})))))
 ({|v_Vt|})
 (λ ({|v_Vda|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) ({|v_Vn|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) ({|v_Vn|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) ({|v_Vn|}))))
 (eprover_trace.{|s|} ({|v_Vv|}))
 (λ ({|v_Vea|} : zen.Proof (zen.or
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vv|})))))),
 zen.Ror
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vv|})))
 (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vv|}))))
 (λ ({|v_Vfa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vv|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vt|}) (eprover_trace.{|s|} ({|v_Vv|})))
 ({|v_Vfa|})
 ({|v_Vx|})
)
 (λ ({|v_Vga|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vv|}))))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vt|}))) (eprover_trace.{|s|} ({|v_Vv|})))
 ({|v_Vca|})
 ({|v_Vga|})
)
 ({|v_Vea|})
)
 ({|v_Vda|})
)
 ({|v_Vp|})
)
 (λ ({|v_Vha|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|})))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|f|} ({|v_Vt|})) ({|v_Vv|}))
 ({|v_Vz|})
 ({|v_Vha|})
)
 ({|v_Vba|})
)
 ({|v_Vaa|})
)
 ({|v_Vr|})
)
 ({|v_Vy|})
)
 ({|v_Vw|})
)
 ({|v_Vu|})
)
 ({|v_Vs|})
)
 ({|v_Vq|})
)
 ({|v_Vo|})
)