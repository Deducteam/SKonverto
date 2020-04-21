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
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))) (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})))))))))
 ≔
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))) (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})))))))))

(λ ({|v_Vaa|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))) (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))))))))))),
 zen.Rcut
 (zen.forall (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vda|})))))))
 (λ ({|v_Vea|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vda|})))))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))))))))
 (λ ({|v_Vfa|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))),
 λ ({|v_Vga|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})))))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})))))))
 (λ ({|v_Vha|} : zen.term (zen.iota)),
 λ ({|v_Via|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))))))
 (λ ({|v_Vja|} : zen.term (zen.iota)),
 λ ({|v_Vka|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vz|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vz|})))))
 (λ ({|v_Vla|} : zen.term (zen.iota)),
 λ ({|v_Vma|} : zen.Proof (zen.not
 (zen.or
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))))))),
 zen.Rnotor
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))))
 (λ ({|v_Vna|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|})))),
 λ ({|v_Voa|} : zen.Proof (zen.not
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})))))),
 zen.Rnotor
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})))
 (λ ({|v_Vpa|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))))),
 λ ({|v_Vqa|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 (λ ({|v_Vra|} : zen.Proof (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 (λ ({|v_Vsa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))),
 zen.Rcut
 (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))))
 (λ ({|v_Vta|} : zen.Proof (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))))),
 zen.Rand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))
 (λ ({|v_Vua|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|})))),
 λ ({|v_Vva|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 ({|v_Vsa|})
 ({|v_Vva|})
)
 ({|v_Vta|})
)
 (λ ({|v_Vwa|} : zen.Proof (zen.not
 (zen.{|and|}
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))))),
 zen.Rcut
 (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|}))
 (λ ({|v_Vxa|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vya|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vya|}) ({|v_Vla|}))
 ({|v_Vja|})
 ({|v_Vha|})
 (λ ({|v_Vza|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vja|})
 ({|v_Vha|})))),
 zen.Rnotand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))
 (λ ({|v_Vab|} : zen.Proof (zen.not
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))))),
 zen.Rnotnot
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))
 (λ ({|v_Vbb|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))),
 zen.Rcut
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vha|}))
 (λ ({|v_Vcb|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vha|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vdb|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vdb|})
 ({|v_Vha|}))
 ({|v_Vha|})
 ({|v_Vja|})
 (λ ({|v_Vua|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))
 ({|v_Vbb|})
 ({|v_Vua|})
)
 (λ ({|v_Veb|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vja|})
 ({|v_Vha|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vfb|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vja|})
 ({|v_Vfb|}))
 ({|v_Vha|})
 ({|v_Vha|})
 (λ ({|v_Vgb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vha|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vha|})
 ({|v_Vgb|})
)
 (λ ({|v_Veb|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vja|})
 ({|v_Vha|}))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vja|})
 ({|v_Vha|}))
 ({|v_Veb|})
 ({|v_Vza|})
)
 ({|v_Veb|})
)
 ({|v_Vcb|})
)
 (λ ({|v_Vgb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vha|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vha|})
 ({|v_Vgb|})
)
)
 ({|v_Vab|})
)
 (λ ({|v_Vpa|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 (λ ({|v_Vsa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vda|}))))))
 ({|v_Vha|})
 (λ ({|v_Vhb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|})))))
 ({|v_Vja|})
 (λ ({|v_Vib|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|}))))
 ({|v_Vla|})
 (λ ({|v_Vjb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|})))
 (λ ({|v_Vva|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 ({|v_Vsa|})
 ({|v_Vva|})
)
 (λ ({|v_Vkb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))
 (λ ({|v_Vlb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 ({|v_Vra|})
 ({|v_Vlb|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vya|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vya|}) ({|v_Vla|}))
 ({|v_Vha|})
 ({|v_Vha|})
 (λ ({|v_Vgb|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vha|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vha|})
 ({|v_Vgb|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vnb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vnb|}))
 ({|v_Vla|})
 ({|v_Vla|})
 (λ ({|v_Vob|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|}))
 ({|v_Vxa|})
 ({|v_Vob|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))
 ({|v_Vmb|})
 ({|v_Vna|})
)
 ({|v_Vmb|})
)
 ({|v_Vmb|})
)
 ({|v_Vkb|})
)
 ({|v_Vjb|})
)
 ({|v_Vib|})
)
 ({|v_Vhb|})
)
 ({|v_Vea|})
)
 ({|v_Vpa|})
)
 ({|v_Vwa|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vnb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vnb|}))
 ({|v_Vla|})
 ({|v_Vla|})
 (λ ({|v_Vob|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|})))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|}))
 ({|v_Vxa|})
 ({|v_Vob|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))
 ({|v_Vmb|})
 ({|v_Vna|})
)
 ({|v_Vmb|})
)
 ({|v_Vra|})
)
 (λ ({|v_Vob|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|})))),
 zen.Rcut
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|}))
 (λ ({|v_Vpb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vda|}))))))
 ({|v_Vja|})
 (λ ({|v_Vqb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|})))))
 ({|v_Vla|})
 (λ ({|v_Vrb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|}))))
 ({|v_Vla|})
 (λ ({|v_Vsb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})))
 (λ ({|v_Vlb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 ({|v_Vra|})
 ({|v_Vlb|})
)
 (λ ({|v_Vtb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|}))
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 (λ ({|v_Vub|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|}))
 ({|v_Vpb|})
 ({|v_Vub|})
)
 (λ ({|v_Vra|} : zen.Proof (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vya|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vya|}) ({|v_Vla|}))
 ({|v_Vja|})
 ({|v_Vha|})
 (λ ({|v_Vza|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vja|})
 ({|v_Vha|})))),
 zen.Rnotand
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|})))
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))
 (λ ({|v_Vab|} : zen.Proof (zen.not
 (zen.not
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))))),
 zen.Rnotnot
 (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))
 (λ ({|v_Vbb|} : zen.Proof (zen.equal (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|}))),
 zen.Reqsym
 (zen.iota)
 ({|v_Vha|})
 ({|v_Vja|})
 ({|v_Vbb|})
 ({|v_Vza|})
)
 ({|v_Vab|})
)
 (λ ({|v_Vpa|} : zen.Proof (zen.not
 (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))))),
 zen.Rnotnot
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 (λ ({|v_Vsa|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vda|}))))))
 ({|v_Vha|})
 (λ ({|v_Vhb|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|})))))
 ({|v_Vja|})
 (λ ({|v_Vib|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vda|}))))
 ({|v_Vla|})
 (λ ({|v_Vjb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|})))
 (λ ({|v_Vva|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vja|}))
 ({|v_Vsa|})
 ({|v_Vva|})
)
 (λ ({|v_Vkb|} : zen.Proof (zen.imp
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})) (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|})))),
 zen.Rimply
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))
 (λ ({|v_Vlb|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vja|}) ({|v_Vla|}))
 ({|v_Vra|})
 ({|v_Vlb|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))
 ({|v_Vmb|})
 ({|v_Vna|})
)
 ({|v_Vkb|})
)
 ({|v_Vjb|})
)
 ({|v_Vib|})
)
 ({|v_Vhb|})
)
 ({|v_Vea|})
)
 ({|v_Vpa|})
)
 ({|v_Vwa|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vnb|} : zen.term (zen.iota)),
 eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vnb|}))
 ({|v_Vla|})
 ({|v_Vla|})
 (λ ({|v_Vob|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|v_Vla|})
 ({|v_Vla|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vla|})
 ({|v_Vob|})
)
 (λ ({|v_Vmb|} : zen.Proof (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vha|}) ({|v_Vla|}))
 ({|v_Vmb|})
 ({|v_Vna|})
)
 ({|v_Vmb|})
)
 ({|v_Vra|})
)
 ({|v_Vtb|})
)
 ({|v_Vsb|})
)
 ({|v_Vrb|})
)
 ({|v_Vqb|})
)
 ({|v_Vea|})
)
 (λ ({|v_Vub|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vla|}) ({|v_Vla|})))),
 zen.Rnoteq
 (zen.iota)
 ({|v_Vla|})
 ({|v_Vob|})
)
)
)
)
 ({|v_Vpa|})
)
 ({|v_Vqa|})
)
 ({|v_Voa|})
)
 ({|v_Vma|})
)
 ({|v_Vka|})
)
 ({|v_Via|})
)
 ({|v_Vga|})
)
 ({|v_Vaa|})
)
 (λ ({|v_Vvb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vda|}))))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vba|}) ({|v_Vda|}))))))
 (λ ({|v_Vwb|} : zen.term (zen.iota)),
 λ ({|v_Vxb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vda|})))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vca|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vca|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vda|})))))
 (λ ({|v_Vyb|} : zen.term (zen.iota)),
 λ ({|v_Vzb|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vda|}))))))),
 zen.Rnotall
 (zen.iota)
 (λ ({|v_Vda|} : zen.term (zen.iota)),
 zen.imp
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vda|})) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vda|}))))
 (λ ({|v_Vac|} : zen.term (zen.iota)),
 λ ({|v_Vbc|} : zen.Proof (zen.not
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|})) (zen.imp
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|})) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|})))))),
 zen.Rnotimply
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|}))
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|})) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|})))
 (λ ({|v_Vcc|} : zen.Proof (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|}))),
 λ ({|v_Vdc|} : zen.Proof (zen.not
 (zen.imp
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|})) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|}))))),
 zen.Rnotimply
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|}))
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|}))
 (λ ({|v_Vec|} : zen.Proof (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|}))),
 λ ({|v_Vfc|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|})))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|}))))))))
 (λ ({|v_Vfa|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|})))))))),
 λ ({|v_Vga|} : zen.Proof (zen.not
 (zen.forall (zen.iota)
 (λ ({|v_Vx|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vz|} : zen.term (zen.iota)),
 zen.or
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vz|})) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vx|}) ({|v_Vy|}))) (zen.not
 (eprover_trace.{|p|} ({|v_Vy|}) ({|v_Vz|})))))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vu|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vu|}) ({|v_Vw|}))))))
 ({|v_Vwb|})
 (λ ({|v_Vgc|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vw|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vv|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vv|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vv|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vw|})))))
 ({|v_Vyb|})
 (λ ({|v_Vhc|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vw|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vw|} : zen.term (zen.iota)),
 zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vw|}))) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vw|}))))
 ({|v_Vac|})
 (λ ({|v_Vic|} : zen.Proof (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|}))) (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|}))) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|}))))),
 zen.Ror
 (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|})))
 (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|}))) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|})))
 (λ ({|v_Vjc|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vyb|}))
 ({|v_Vcc|})
 ({|v_Vjc|})
)
 (λ ({|v_Vkc|} : zen.Proof (zen.or
 (zen.not
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|}))) (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|})))),
 zen.Ror
 (zen.not
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|})))
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|}))
 (λ ({|v_Vlc|} : zen.Proof (zen.not
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|})))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vyb|}) ({|v_Vac|}))
 ({|v_Vec|})
 ({|v_Vlc|})
)
 (λ ({|v_Vmc|} : zen.Proof (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|}))),
 zen.Raxiom
 (eprover_trace.{|p|} ({|v_Vwb|}) ({|v_Vac|}))
 ({|v_Vmc|})
 ({|v_Vfc|})
)
 ({|v_Vkc|})
)
 ({|v_Vic|})
)
 ({|v_Vhc|})
)
 ({|v_Vgc|})
)
 ({|v_Vfa|})
)
 ({|v_Vaa|})
)
 ({|v_Vdc|})
)
 ({|v_Vbc|})
)
 ({|v_Vzb|})
)
 ({|v_Vxb|})
)
 ({|v_Vvb|})
)
)