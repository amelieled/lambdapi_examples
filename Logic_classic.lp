require open amelie.notation
require open amelie.Logic

// Excluded middle
constant symbol excl_mid p : π (p ∨ (¬ p))

theorem neg_elimp p : π (¬ (¬ p)) ⇒ π p
proof
    assume p nnp
    refine disj_elim p (¬p) p _ _ _
    refine excl_mid p
    assume pa
    refine pa
    assume pna
    apply false_elim
    apply neg_elim (¬p) nnp
    apply pna
qed
