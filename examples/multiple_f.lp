require logic.zen as zen
symbol {|s|} : zen.term (zen.iota) ⇒ zen.term (zen.iota)

symbol {|f|} : zen.term (zen.iota) ⇒ zen.term (zen.iota)

symbol {|a|} : zen.term (zen.iota)

set builtin "skolem_symbol" ≔ {|f|}


definition delta :
 zen.Proof (zen.{|and|}
 (zen.forall (zen.iota)
 (λ ({|v_Vr|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vr|})
 ({|s|} ({|f|} ({|v_Vr|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vs|} : zen.term (zen.iota)),
 zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|v_Vs|})))))))
 ⇒ zen.seq
 ≔ λ ({|formule|} : zen.Proof (zen.{|and|}
 (zen.forall (zen.iota)
 (λ ({|v_Vr|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vr|})
 ({|s|} ({|f|} ({|v_Vr|}))))) (zen.forall (zen.iota)
 (λ ({|v_Vs|} : zen.term (zen.iota)),
 zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|v_Vs|})))))))),
 zen.Rand
 (zen.forall (zen.iota)
 (λ ({|v_Vr|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vr|})
 ({|s|} ({|f|} ({|v_Vr|})))))
 (zen.forall (zen.iota)
 (λ ({|v_Vs|} : zen.term (zen.iota)),
 zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|v_Vs|}))))))
 (λ ({|v_Vt|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vr|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vr|})
 ({|s|} ({|f|} ({|v_Vr|})))))),
 λ ({|v_Vu|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vs|} : zen.term (zen.iota)),
 zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|v_Vs|}))))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vr|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vr|})
 ({|s|} ({|f|} ({|v_Vr|}))))
 ({|a|})
 (λ ({|v_Vv|} : zen.Proof (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|f|} ({|a|}))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vr|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vr|})
 ({|s|} ({|f|} ({|v_Vr|}))))
 ({|f|} ({|a|}))
 (λ ({|v_Vw|} : zen.Proof (zen.equal (zen.iota)
 ({|f|} ({|a|}))
 ({|s|} ({|f|} ({|f|} ({|a|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vs|} : zen.term (zen.iota)),
 zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|v_Vs|})))))
 ({|f|} ({|f|} ({|a|})))
 (λ ({|v_Vx|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|})))))))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vy|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vy|})
 ({|s|} ({|f|} ({|a|}))))
 ({|a|})
 ({|a|})
 (λ ({|v_Vz|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|a|})))),
 zen.Rcut
 (zen.equal (zen.iota)
 ({|a|})
 ({|a|}))
 (λ ({|v_Vaa|} : zen.Proof (zen.equal (zen.iota)
 ({|a|})
 ({|a|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vba|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|v_Vba|})
 ({|a|}))
 ({|a|})
 ({|a|})
 (λ ({|v_Vz|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|a|})))),
 zen.Rnoteq
 (zen.iota)
 ({|a|})
 ({|v_Vz|})
)
 (λ ({|v_Vaa|} : zen.Proof (zen.equal (zen.iota)
 ({|a|})
 ({|a|}))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|a|})
 ({|v_Vca|}))
 ({|a|})
 ({|a|})
 (λ ({|v_Vz|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|a|})))),
 zen.Rnoteq
 (zen.iota)
 ({|a|})
 ({|v_Vz|})
)
 (λ ({|v_Vaa|} : zen.Proof (zen.equal (zen.iota)
 ({|a|})
 ({|a|}))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|a|})
 ({|a|}))
 ({|v_Vaa|})
 ({|v_Vz|})
)
 ({|v_Vaa|})
)
 ({|v_Vaa|})
)
 (λ ({|v_Vz|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|a|})
 ({|a|})))),
 zen.Rnoteq
 (zen.iota)
 ({|a|})
 ({|v_Vz|})
)
)
 (λ ({|v_Vv|} : zen.Proof (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|f|} ({|a|}))))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vca|} : zen.term (zen.iota)),
 zen.equal (zen.iota)
 ({|a|})
 ({|v_Vca|}))
 ({|s|} ({|f|} ({|a|})))
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|})))))
 (λ ({|v_Vda|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|s|} ({|f|} ({|a|})))
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|})))))))),
 zen.Rsubst
 (zen.iota)
 (λ ({|v_Vea|} : zen.term (zen.iota)),
 zen.not
 (zen.equal (zen.iota)
 ({|s|} ({|v_Vea|}))
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|})))))))
 ({|f|} ({|a|}))
 ({|s|} ({|f|} ({|f|} ({|a|}))))
 (λ ({|v_Vfa|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|f|} ({|a|}))
 ({|s|} ({|f|} ({|f|} ({|a|}))))))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|f|} ({|a|}))
 ({|s|} ({|f|} ({|f|} ({|a|})))))
 ({|v_Vw|})
 ({|v_Vfa|})
)
 (λ ({|v_Vga|} : zen.Proof (zen.not
 (zen.equal (zen.iota)
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|})))))
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|})))))))),
 zen.Rnoteq
 (zen.iota)
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|})))))
 ({|v_Vga|})
)
 ({|v_Vda|})
)
 (λ ({|v_Vha|} : zen.Proof (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|}))))))),
 zen.Raxiom
 (zen.equal (zen.iota)
 ({|a|})
 ({|s|} ({|s|} ({|f|} ({|f|} ({|a|}))))))
 ({|v_Vha|})
 ({|v_Vx|})
)
 ({|v_Vv|})
)
 ({|v_Vv|})
)
 ({|v_Vu|})
)
 ({|v_Vt|})
)
 ({|v_Vt|})
)
 ({|formule|})