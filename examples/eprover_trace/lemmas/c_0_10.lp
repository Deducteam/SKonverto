require example.logic.zen as zen
require example.eprover_trace as eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})))))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|}))))))))
 ≔
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})))))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|}))))))))

(λ ({|v_Vx|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})))))))) (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|})))))))))),
 zen.Rcut
 (zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vaa|})))))))
 (λ ({|v_Vba|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vaa|})))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))))))))
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|})))))))
 (λ ({|v_Vca|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))))))))),
 λ ({|v_Vda|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|}))))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|})))))
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|}))))))
 (λ ({|v_Vea|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|})))))),
 λ ({|v_Vfa|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|})))))
 (λ ({|v_Vga|} : zen.term (zen.iota)),
 λ ({|v_Vha|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vv|}))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vv|}))))
 (λ ({|v_Via|} : zen.term (zen.iota)),
 λ ({|v_Vja|} : zen.Proof (zen.not
 (zen.or
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})))))),
 zen.Rnotor
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))
 (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})))
 (λ ({|v_Vka|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|})))),
 λ ({|v_Vla|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 (λ ({|v_Vma|} : zen.Proof (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))),
 zen.Rcut
 (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))) (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))))
 (λ ({|v_Vna|} : zen.Proof (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))) (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))))),
 zen.Rand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))
 (λ ({|v_Voa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))),
 λ ({|v_Vpa|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))
 ({|v_Vga|})
 (λ ({|v_Vqa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 ({|v_Vqa|})
 ({|v_Vpa|})
)
 ({|v_Vea|})
)
 ({|v_Vna|})
)
 (λ ({|v_Vra|} : zen.Proof (zen.not
 (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))) (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))))),
 zen.Rcut
 (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|}))
 (λ ({|v_Vsa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vta|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vta|}) ({|v_Via|}))
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vga|})
 (λ ({|v_Vua|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vga|})))),
 zen.Rnotand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))
 (λ ({|v_Vva|} : zen.Proof (zen.not
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))))),
 zen.Rnotnot
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 (λ ({|v_Vwa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))),
 zen.Rcut
 (zen.equal (zen.iota)
 ({|v_Vga|})
 ({|v_Vga|}))
 (λ ({|v_Vxa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vga|})
 ({|v_Vga|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vya|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vya|})
 ({|v_Vga|}))
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 (λ ({|v_Voa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 ({|v_Vwa|})
 ({|v_Voa|})
)
 (λ ({|v_Vza|} : zen.Proof (zen.equal (zen.iota)
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vga|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vab|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vab|}))
 ({|v_Vga|})
 ({|v_Vga|})
 (λ ({|v_Vbb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 ({|v_Vga|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vga|})
 ({|v_Vbb|})
)
 (λ ({|v_Vza|} : zen.Proof (zen.equal (zen.iota)
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vga|}))),
 zen.Raxiom
 (zen.equal (zen.iota)
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vga|}))
 ({|v_Vza|})
 ({|v_Vua|})
)
 ({|v_Vza|})
)
 ({|v_Vxa|})
)
 (λ ({|v_Vbb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 ({|v_Vga|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vga|})
 ({|v_Vbb|})
)
)
 ({|v_Vva|})
)
 (λ ({|v_Vcb|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 (λ ({|v_Vqa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vaa|}))))))
 ({|v_Vga|})
 (λ ({|v_Vdb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|})))))
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 (λ ({|v_Veb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))) (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))) (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|}))))
 ({|v_Via|})
 (λ ({|v_Vfb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))) (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|})))
 (λ ({|v_Vpa|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 ({|v_Vqa|})
 ({|v_Vpa|})
)
 (λ ({|v_Vgb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|})))),
 zen.Rimply
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))
 (λ ({|v_Vhb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 ({|v_Vma|})
 ({|v_Vhb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vta|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vta|}) ({|v_Via|}))
 ({|v_Vga|})
 ({|v_Vga|})
 (λ ({|v_Vbb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 ({|v_Vga|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vga|})
 ({|v_Vbb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vjb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vjb|}))
 ({|v_Via|})
 ({|v_Via|})
 (λ ({|v_Vkb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|}))
 ({|v_Vsa|})
 ({|v_Vkb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))
 ({|v_Vib|})
 ({|v_Vka|})
)
 ({|v_Vib|})
)
 ({|v_Vib|})
)
 ({|v_Vgb|})
)
 ({|v_Vfb|})
)
 ({|v_Veb|})
)
 ({|v_Vdb|})
)
 ({|v_Vba|})
)
 ({|v_Vcb|})
)
 ({|v_Vra|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vjb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vjb|}))
 ({|v_Via|})
 ({|v_Via|})
 (λ ({|v_Vkb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|}))
 ({|v_Vsa|})
 ({|v_Vkb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))
 ({|v_Vib|})
 ({|v_Vka|})
)
 ({|v_Vib|})
)
 ({|v_Vma|})
)
 (λ ({|v_Vkb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|})))),
 zen.Rcut
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|}))
 (λ ({|v_Vlb|} : zen.Proof (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vaa|}))))))
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 (λ ({|v_Vmb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|})))))
 ({|v_Via|})
 (λ ({|v_Vnb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Vaa|})) (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Vaa|})) (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|}))))
 ({|v_Via|})
 (λ ({|v_Vob|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|})) (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))))),
 zen.Rimply
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|})) (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})))
 (λ ({|v_Vhb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 ({|v_Vma|})
 ({|v_Vhb|})
)
 (λ ({|v_Vpb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|})) (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|}))
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 (λ ({|v_Vqb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|}))
 ({|v_Vlb|})
 ({|v_Vqb|})
)
 (λ ({|v_Vma|} : zen.Proof (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vta|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vta|}) ({|v_Via|}))
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vga|})
 (λ ({|v_Vua|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vga|})))),
 zen.Rnotand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))
 (λ ({|v_Vva|} : zen.Proof (zen.not
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))))),
 zen.Rnotnot
 (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 (λ ({|v_Vwa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))),
 zen.Reqsym
 (zen.iota)
 ({|v_Vga|})
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 ({|v_Vwa|})
 ({|v_Vua|})
)
 ({|v_Vva|})
)
 (λ ({|v_Vcb|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 (λ ({|v_Vqa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vaa|}))))))
 ({|v_Vga|})
 (λ ({|v_Vdb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|})))))
 (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))
 (λ ({|v_Veb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))) (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))) (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vaa|}))))
 ({|v_Via|})
 (λ ({|v_Vfb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))) (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|})))
 (λ ({|v_Vpa|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|})))))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vga|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))))
 ({|v_Vqa|})
 ({|v_Vpa|})
)
 (λ ({|v_Vgb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})) (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|})))),
 zen.Rimply
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))
 (λ ({|v_Vhb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|})))),
 zen.Raxiom
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vga|}))) ({|v_Via|}))
 ({|v_Vma|})
 ({|v_Vhb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))
 ({|v_Vib|})
 ({|v_Vka|})
)
 ({|v_Vgb|})
)
 ({|v_Vfb|})
)
 ({|v_Veb|})
)
 ({|v_Vdb|})
)
 ({|v_Vba|})
)
 ({|v_Vcb|})
)
 ({|v_Vra|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vjb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vga|}) ({|v_Vjb|}))
 ({|v_Via|})
 ({|v_Via|})
 (λ ({|v_Vkb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Via|})
 ({|v_Via|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Via|})
 ({|v_Vkb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vga|}) ({|v_Via|}))
 ({|v_Vib|})
 ({|v_Vka|})
)
 ({|v_Vib|})
)
 ({|v_Vma|})
)
 ({|v_Vpb|})
)
 ({|v_Vob|})
)
 ({|v_Vnb|})
)
 ({|v_Vmb|})
)
 ({|v_Vba|})
)
 (λ ({|v_Vqb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Via|}) ({|v_Via|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Via|})
 ({|v_Vkb|})
)
)
)
)
 ({|v_Vla|})
)
 ({|v_Vja|})
)
 ({|v_Vha|})
)
 ({|v_Vfa|})
)
 ({|v_Vda|})
)
 ({|v_Vx|})
)
 (λ ({|v_Vrb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vaa|}))))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vaa|}))))))
 (λ ({|v_Vsb|} : zen.term (zen.iota)),
 λ ({|v_Vtb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vaa|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vz|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vz|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vaa|})))))
 (λ ({|v_Vub|} : zen.term (zen.iota)),
 λ ({|v_Vvb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vaa|}))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vaa|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vaa|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vaa|}))))
 (λ ({|v_Vwb|} : zen.term (zen.iota)),
 λ ({|v_Vxb|} : zen.Proof (zen.not
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|})))))),
 zen.Rnotimply
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|})))
 (λ ({|v_Vyb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))),
 λ ({|v_Vzb|} : zen.Proof (zen.not
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))))),
 zen.Rnotimply
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|}))
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))
 (λ ({|v_Vac|} : zen.Proof (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|}))),
 λ ({|v_Vbc|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|})))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))))))))
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|})))))))
 (λ ({|v_Vca|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))))))))),
 λ ({|v_Vda|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vu|}) (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.not
 (eprover_trace.{|p|} (eprover_trace.{|s|} (eprover_trace.{|f|} ({|v_Vu|}))) ({|v_Vv|}))))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})))))))
 ({|v_Vsb|})
 (λ ({|v_Vcc|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vv|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))))))
 ({|v_Vub|})
 (λ ({|v_Vdc|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vw|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vw|})))))
 ({|v_Vwb|})
 (λ ({|v_Vec|} : zen.Proof (zen.or
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})))))),
 zen.Ror
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|}))))
 (λ ({|v_Vfc|} : zen.Proof (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))
 ({|v_Vfc|})
 ({|v_Vbc|})
)
 (λ ({|v_Vgc|} : zen.Proof (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|}))))),
 zen.Ror
 (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})))
 (λ ({|v_Vhc|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))
 ({|v_Vyb|})
 ({|v_Vhc|})
)
 (λ ({|v_Vic|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|}))
 ({|v_Vac|})
 ({|v_Vic|})
)
 ({|v_Vgc|})
)
 ({|v_Vec|})
)
 ({|v_Vdc|})
)
 ({|v_Vcc|})
)
 ({|v_Vca|})
)
 ({|v_Vx|})
)
 ({|v_Vzb|})
)
 ({|v_Vxb|})
)
 ({|v_Vvb|})
)
 ({|v_Vtb|})
)
 ({|v_Vrb|})
)
)