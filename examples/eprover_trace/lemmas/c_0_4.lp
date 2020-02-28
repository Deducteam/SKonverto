require logic.zen as zen
require eprover_trace
definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))) (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})))))))) 
 ≔ 
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))) (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|}))))))))

(λ ({|v_Vaa|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))) (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})))))))))),
 zen.Rcut
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))
 (λ ({|v_Vba|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})))))))
 (λ ({|v_Vba|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))),
 λ ({|v_Vca|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|}))))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|}))))))
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 λ ({|v_Vea|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vz|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vz|})))))
 (λ ({|v_Vfa|} : zen.term (zen.iota)),
 λ ({|v_Vga|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vz|}))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vz|}))))
 (λ ({|v_Vha|} : zen.term (zen.iota)),
 λ ({|v_Via|} : zen.Proof (zen.not
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))))),
 zen.Rnotor
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})))
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))
 (λ ({|v_Vja|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))))),
 λ ({|v_Vka|} : zen.Proof (zen.not
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))))),
 zen.Rnotor
 (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|})))
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 (λ ({|v_Vla|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))))),
 λ ({|v_Vma|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))
 (λ ({|v_Vna|} : zen.Proof (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))
 (λ ({|v_Voa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))),
 zen.Rcut
 (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))))
 (λ ({|v_Vpa|} : zen.Proof (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))))),
 zen.Rand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})))
 (λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))),
 λ ({|v_Vra|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vda|})
 ({|v_Vqa|})
)
 ({|v_Vpa|})
)
 (λ ({|v_Vsa|} : zen.Proof (zen.not
 (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})))))),
 zen.Rcut
 (zen.equal (zen.iota)
 ({|v_Vfa|})
 ({|v_Vha|}))
 (λ ({|v_Vta|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vfa|})
 ({|v_Vha|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vua|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vua|}) ({|v_Vfa|}))
 ({|v_Vda|})
 ({|v_Vda|})
 (λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))),
 zen.Rnotand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})))
 (λ ({|v_Vva|} : zen.Proof (zen.not
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))))),
 zen.Rnotnot
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))
 (λ ({|v_Vwa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))),
 zen.Rcut
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))
 (λ ({|v_Vwa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vxa|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vxa|})
 ({|v_Vda|}))
 ({|v_Vda|})
 ({|v_Vda|})
 (λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))
 ({|v_Vwa|})
 ({|v_Vqa|})
)
 (λ ({|v_Vwa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vya|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vya|}))
 ({|v_Vda|})
 ({|v_Vda|})
 (λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vda|})
 ({|v_Vqa|})
)
 (λ ({|v_Vwa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))
 ({|v_Vwa|})
 ({|v_Vqa|})
)
 ({|v_Vwa|})
)
 ({|v_Vwa|})
)
 (λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vda|})
 ({|v_Vqa|})
)
)
 ({|v_Vva|})
)
 (λ ({|v_Vza|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))
 (λ ({|v_Vab|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))
 ({|v_Vda|})
 (λ ({|v_Vbb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})))))
 ({|v_Vda|})
 (λ ({|v_Vcb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|}))))
 ({|v_Vfa|})
 (λ ({|v_Vdb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})))
 (λ ({|v_Vra|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))
 ({|v_Vab|})
 ({|v_Vra|})
)
 (λ ({|v_Veb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))
 (λ ({|v_Vfb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))
 ({|v_Voa|})
 ({|v_Vfb|})
)
 (λ ({|v_Voa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vua|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vua|}) ({|v_Vfa|}))
 ({|v_Vda|})
 ({|v_Vda|})
 (λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vda|})
 ({|v_Vqa|})
)
 (λ ({|v_Voa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vgb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vgb|}))
 ({|v_Vfa|})
 ({|v_Vha|})
 (λ ({|v_Vhb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vfa|})
 ({|v_Vha|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vfa|})
 ({|v_Vha|}))
 ({|v_Vta|})
 ({|v_Vhb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 ({|v_Vib|})
 ({|v_Vma|})
)
 ({|v_Voa|})
)
 ({|v_Voa|})
)
 ({|v_Veb|})
)
 ({|v_Vdb|})
)
 ({|v_Vcb|})
)
 ({|v_Vbb|})
)
 ({|v_Vba|})
)
 ({|v_Vza|})
)
 ({|v_Vsa|})
)
 (λ ({|v_Voa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vgb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vgb|}))
 ({|v_Vfa|})
 ({|v_Vha|})
 (λ ({|v_Vhb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vfa|})
 ({|v_Vha|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vfa|})
 ({|v_Vha|}))
 ({|v_Vta|})
 ({|v_Vhb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 ({|v_Vib|})
 ({|v_Vma|})
)
 ({|v_Voa|})
)
 ({|v_Voa|})
)
 (λ ({|v_Vhb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vfa|})
 ({|v_Vha|})))),
 zen.Rcut
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))
 (λ ({|v_Vna|} : zen.Proof (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))
 ({|v_Vda|})
 (λ ({|v_Vbb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})))))
 ({|v_Vfa|})
 (λ ({|v_Vjb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|}))))
 ({|v_Vha|})
 (λ ({|v_Vkb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))
 (λ ({|v_Vfb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vfa|}))
 ({|v_Voa|})
 ({|v_Vfb|})
)
 (λ ({|v_Vlb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 (λ ({|v_Vmb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))
 ({|v_Vna|})
 ({|v_Vmb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vnb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vnb|}) ({|v_Vha|}))
 ({|v_Vda|})
 ({|v_Vda|})
 (λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))),
 zen.Rnotand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})))
 (λ ({|v_Vva|} : zen.Proof (zen.not
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))))),
 zen.Rnotnot
 (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))
 (λ ({|v_Vwa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|}))),
 zen.Reqsym
 (zen.iota)
 ({|v_Vda|})
 ({|v_Vda|})
 ({|v_Vwa|})
 ({|v_Vqa|})
)
 ({|v_Vva|})
)
 (λ ({|v_Vza|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))
 (λ ({|v_Vab|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))
 ({|v_Vda|})
 (λ ({|v_Vbb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})))))
 ({|v_Vda|})
 (λ ({|v_Vcb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vw|}))))
 ({|v_Vha|})
 (λ ({|v_Vob|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))
 (λ ({|v_Vra|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vda|}))
 ({|v_Vab|})
 ({|v_Vra|})
)
 (λ ({|v_Vpb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})) (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 (λ ({|v_Vma|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 ({|v_Vib|})
 ({|v_Vma|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 ({|v_Vib|})
 ({|v_Vma|})
)
 ({|v_Vpb|})
)
 ({|v_Vob|})
)
 ({|v_Vcb|})
)
 ({|v_Vbb|})
)
 ({|v_Vba|})
)
 ({|v_Vza|})
)
 ({|v_Vsa|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vgb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vgb|}))
 ({|v_Vha|})
 ({|v_Vha|})
 (λ ({|v_Vqb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vha|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vha|})
 ({|v_Vqb|})
)
 (λ ({|v_Vib|} : zen.Proof (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vda|}) ({|v_Vha|}))
 ({|v_Vib|})
 ({|v_Vma|})
)
 ({|v_Vib|})
)
 ({|v_Vib|})
)
 ({|v_Vlb|})
)
 ({|v_Vkb|})
)
 ({|v_Vjb|})
)
 ({|v_Vbb|})
)
 ({|v_Vba|})
)
 (λ ({|v_Vmb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vfa|}) ({|v_Vha|}))
 ({|v_Vna|})
 ({|v_Vmb|})
)
)
)
)
 ({|v_Vja|})
)
 ({|v_Vla|})
)
 ({|v_Vka|})
)
 ({|v_Via|})
)
 ({|v_Vga|})
)
 ({|v_Vea|})
)
 ({|v_Vca|})
)
 ({|v_Vaa|})
)
 (λ ({|v_Vrb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))
 (λ ({|v_Vsb|} : zen.term (zen.iota)),
 λ ({|v_Vtb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})))))
 (λ ({|v_Vub|} : zen.term (zen.iota)),
 λ ({|v_Vvb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|}))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|}))))
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
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})))))))
 (λ ({|v_Vba|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))),
 λ ({|v_Vca|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))) (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|}))))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))
 ({|v_Vsb|})
 (λ ({|v_Vcc|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vv|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})))))
 ({|v_Vub|})
 (λ ({|v_Vdc|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vw|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vw|}))))
 ({|v_Vwb|})
 (λ ({|v_Vec|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|})))
 (λ ({|v_Vfc|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vub|}))
 ({|v_Vyb|})
 ({|v_Vfc|})
)
 (λ ({|v_Vgc|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})) (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|}))
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))
 (λ ({|v_Vhc|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vub|}) ({|v_Vwb|}))
 ({|v_Vac|})
 ({|v_Vhc|})
)
 (λ ({|v_Vic|} : zen.Proof (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vsb|}) ({|v_Vwb|}))
 ({|v_Vic|})
 ({|v_Vbc|})
)
 ({|v_Vgc|})
)
 ({|v_Vec|})
)
 ({|v_Vdc|})
)
 ({|v_Vcc|})
)
 ({|v_Vba|})
)
 ({|v_Vaa|})
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