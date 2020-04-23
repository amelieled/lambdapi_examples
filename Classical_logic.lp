require open amelie.Notation
require open amelie.Constructive_logic

// Excluded middle
constant symbol excl_mid p : π (p ∨ (¬ p))

theorem neg_elimp p : π (¬ (¬ p)) → π p
proof
    assume p nnp
    refine disj_elim p (¬p) p _ _ _
    refine excl_mid p
    assume pa
    refine pa
    assume pna
    apply false_elim
    apply nnp
    refine pna
qed

symbol excluded_middle (_ : Prop) : Prop
rule excluded_middle $p ↪ $p ∨ ¬$p

//constant symbol peirce p q : π ((p ⊃ q) ⊃ p) → π p // 1
symbol peirce (_ : Prop) (_: Prop) : Prop   // 1
rule peirce $p $q ↪ (($p ⊃ $q) ⊃ $p) ⊃ $p
//definition peirce ≔ Π(p:Prop) (q:Prop), ((π p → π q) → π p) → π p

//constant symbol double_negation_elimination p : π (¬ (¬ p)) → π p
symbol double_negation_elimination (_ :Prop) : Prop     // 2
rule double_negation_elimination $p ↪ (¬ (¬ $p)) ⊃ $p
definition tre ≔ Π(p:Prop), ((π p → π ⊥) → π ⊥) → π p

//constant symbol de_morgan_not_and_not p q : π (¬ (¬ p ∧ ¬q)) → π (p ∨ q)
symbol de_morgan_not_and_not (_ _:Prop) : Prop                  // 3
rule de_morgan_not_and_not $p $q ↪ (¬ (¬ $p ∧ ¬$q)) ⊃ ($p ∨ $q)

//constant symbol implies_to_or p q : π (p ⊃ q) → π (¬p ∨ q)
symbol implies_to_or (_ _:Prop) : Prop              // 4
rule implies_to_or $p $q ↪ ($p ⊃ $q) ⊃ (¬$p ∨ $q)

// Theorem _0_impl_1 : excluded_middle -> peirce.
// Proof.
// unfold peirce. unfold excluded_middle.
// intros Hyp P Q Hyp2.
// assert(P \/ ~ P).
//  { apply Hyp. }
// destruct H as [HP|HnotP].
//   + assumption.
//   + apply Hyp2. intro HP. apply HnotP in HP. contradiction.
// Qed.
//theorem O_impl_1 : Πp q, excl_mid p q → peirce p
//proof
//qed
constant symbol forall_prop : (Prop → Prop) → Prop
rule π (forall_prop $f) ↪ Πx, π ($f x)

//theorem _0_impl_1 : Π(p q r : Prop), (excl_mid p) → (peirce q r)


theorem _0_impl_1 :
π ((forall_prop (λp:Prop, excluded_middle p)) ⊃
       (forall_prop (λp: Prop, (forall_prop (λq: Prop, peirce p q)))))
proof
  assume Hexcl_mid p q Himpl
  apply disj_elim p (¬p)
  // 0. π (p ∨ ¬ p)
  apply Hexcl_mid
  // 1. π p → π p
  assume Hp apply Hp
  // 2. (π p → π ⊥) → π p
  assume Hnotp apply Himpl assume Hp
  apply false_elim apply Hnotp apply Hp// on Coq : apply HnotP in HP. contradiction
qed

// Theorem _1_impl_2 : peirce -> double_negation_elimination.
// Proof.
// unfold peirce. unfold double_negation_elimination.
// intros Hyp P HypnotnotP.
// apply Hyp with False. intro H.
// apply HypnotnotP in H. contradiction.
// Qed.
theorem _1_impl_2 :
π ((forall_prop (λp: Prop, (forall_prop (λq: Prop, peirce p q))))
   ⊃ (forall_prop (λp:Prop, double_negation_elimination p)))
proof
  assume Hpeirce P Hnotnotp
  apply Hpeirce _ ⊥
  assume Hnotp apply false_elim refine Hnotnotp Hnotp // on Coq : apply HypnotnotP in H. contradiction
qed

// Theorem _2_impl_3 : double_negation_elimination -> de_morgan_not_and_not.
// Proof.
// unfold double_negation_elimination. unfold de_morgan_not_and_not.
// intros Hyp P Q Hand.
// apply Hyp.
// intros Hor. apply Hand. split.
//   + intro HP. apply Hor. left. assumption.
//   + intro HQ. apply Hor. right. assumption.
// Qed.
theorem _2_impl_3 :
π ((forall_prop (λp: Prop, (double_negation_elimination p)))
    ⊃ (forall_prop (λp: Prop, (forall_prop (λq: Prop, de_morgan_not_and_not p q)))))
proof
  //0. (Π(x:Prop), ((π x → π ⊥) → π ⊥) → π x) → Π(x:Prop) (x0:Prop), (π (¬ x ∧ ¬ x0) → π ⊥) → π (x ∨ x0)
  assume Hdouble_neg_elim p q Handimpl
  apply Hdouble_neg_elim
  assume Horimpl apply Handimpl apply conj_intro
      assume Hp apply Horimpl refine disj_intro_left _ _ Hp
      assume Hq apply Horimpl refine disj_intro_right _ _ Hq
qed

// Theorem _3_impl_4 : de_morgan_not_and_not -> implies_to_or.
// Proof.
// unfold de_morgan_not_and_not. unfold implies_to_or.
// intros Hyp P Q HypImpl.
// apply Hyp. intro HypAnd. destruct HypAnd as [HypnotnotP HypnotQ].
// apply HypnotnotP. intro HP.
// apply HypnotQ. apply HypImpl. assumption.
// Qed.
theorem _3_impl_4 :
π ((forall_prop (λp: Prop, (forall_prop (λq: Prop, de_morgan_not_and_not p q))))
   ⊃ (forall_prop (λp: Prop, (forall_prop (λq: Prop, implies_to_or p q)))))
proof
  assume Hyp p q Himpl
  apply Hyp assume Hand //refine conj_elim_left p q Hand
  apply imp_elim (¬ p)
  apply conj_elim_left (¬ (¬ p)) (¬ q) apply Hand
  assume Hp apply imp_elim q
  apply conj_elim_right (¬ (¬ p)) (¬ q) apply Hand
  refine Himpl Hp
qed

// Theorem _4_impl_0 :
// implies_to_or -> excluded_middle.
// Proof.
// unfold implies_to_or. unfold excluded_middle.
// intros Hyp1 P. apply or_commut. apply Hyp1.
// intro HypP. assumption.
// Qed.
theorem or_commut : Π(p:Prop) (q : Prop), π (p ∨ q) → π (q ∨ p)
proof
  assume p q HpORq
  apply disj_elim p q
     // 0. π (p ∨ q)
     apply HpORq
     // 1. π p → π (q ∨ p)
     assume Hp refine disj_intro_right q p Hp
     // 2. π q → π (q ∨ p)
     assume Hq apply disj_intro_left q p Hq
qed

theorem _4_impl_0 :
π ((forall_prop (λp: Prop, (forall_prop (λq: Prop, implies_to_or p q)))) ⊃ (forall_prop (λp: Prop, excluded_middle p)))
proof
 assume Hyp p apply or_commut apply Hyp
 assume Hp apply Hp
qed
