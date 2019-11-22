
require logic.zen as zen


symbol {|element_of_b|} : zen.term (zen.iota)
symbol {|subset|} : zen.term (zen.iota) ⇒ zen.term (zen.iota) ⇒  zen.prop
symbol {|b|} : zen.term (zen.iota)
symbol {|member|} : zen.term (zen.iota) ⇒ zen.term (zen.iota) ⇒  zen.prop
symbol {|bb|} : zen.term (zen.iota)
symbol {|equal_sets|} : zen.term (zen.iota) ⇒ zen.term (zen.iota) ⇒  zen.prop

definition delta : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.imp
 ({|equal_sets|} ({|b|}) ({|bb|})) ({|subset|} ({|b|}) ({|bb|}))))
 ≔
 zen.nnpp (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.imp
 ({|equal_sets|} ({|b|}) ({|bb|})) ({|subset|} ({|b|}) ({|bb|}))))

(λ ({|v_Vo|} : zen.Proof (zen.not
 (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.imp
 ({|equal_sets|} ({|b|}) ({|bb|})) ({|subset|} ({|b|}) ({|bb|})))))),
 zen.Rnotimply
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|v_Vm|}) ({|v_Vn|}))))))
 (zen.imp
 ({|equal_sets|} ({|b|}) ({|bb|})) ({|subset|} ({|b|}) ({|bb|})))
 (λ ({|v_Vp|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|v_Vm|}) ({|v_Vn|}))))))),
 λ ({|v_Vq|} : zen.Proof (zen.not
 (zen.imp
 ({|equal_sets|} ({|b|}) ({|bb|})) ({|subset|} ({|b|}) ({|bb|}))))),
 zen.Rnotimply
 ({|equal_sets|} ({|b|}) ({|bb|}))
 ({|subset|} ({|b|}) ({|bb|}))
 (λ ({|v_Vr|} : zen.Proof ({|equal_sets|} ({|b|}) ({|bb|}))),
 λ ({|v_Vs|} : zen.Proof (zen.not
 ({|subset|} ({|b|}) ({|bb|})))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|v_Vm|}) ({|v_Vn|})))))
 ({|b|})
 (λ ({|v_Vt|} : zen.Proof (zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|b|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|b|}) ({|v_Vn|})))))),
 zen.Rall
 (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|b|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|b|}) ({|v_Vn|}))))
 ({|bb|})
 (λ ({|v_Vu|} : zen.Proof (zen.or
 ({|subset|} ({|b|}) ({|bb|})) (zen.not
 ({|equal_sets|} ({|b|}) ({|bb|}))))),
 zen.Ror
 ({|subset|} ({|b|}) ({|bb|}))
 (zen.not
 ({|equal_sets|} ({|b|}) ({|bb|})))
 (λ ({|v_Vv|} : zen.Proof ({|subset|} ({|b|}) ({|bb|}))),
 zen.Raxiom
 ({|subset|} ({|b|}) ({|bb|}))
 ({|v_Vv|})
 ({|v_Vs|})
)
 (λ ({|v_Vw|} : zen.Proof (zen.not
 ({|equal_sets|} ({|b|}) ({|bb|})))),
 zen.Raxiom
 ({|equal_sets|} ({|b|}) ({|bb|}))
 ({|v_Vr|})
 ({|v_Vw|})
)
 ({|v_Vu|})
)
 ({|v_Vt|})
)
 ({|v_Vp|})
)
 ({|v_Vq|})
)
 ({|v_Vo|})
)

symbol target_type : zen.Proof (zen.imp
 (zen.forall (zen.iota)
 (λ ({|v_Vm|} : zen.term (zen.iota)),
 zen.forall (zen.iota)
 (λ ({|v_Vn|} : zen.term (zen.iota)),
 zen.or
 ({|subset|} ({|v_Vm|}) ({|v_Vn|})) (zen.not
 ({|equal_sets|} ({|v_Vm|}) ({|v_Vn|})))))) (zen.imp
 ({|equal_sets|} ({|b|}) ({|bb|})) ({|subset|} ({|b|}) ({|bb|}))))

set builtin "target_type" ≔ delta
set builtin "skolem_symbol" ≔ {|bb|}