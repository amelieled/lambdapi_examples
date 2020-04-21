require open amelie.Notation
require open amelie.Constructive_logic

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
    apply nnp
    refine pna
qed

// Definition excluded_middle := forall P : Prop,
//   P \/ ~ P.

//Definition peirce := forall P Q: Prop,                     (* 1 *)
//  ((P->Q)->P)->P.
constant symbol peirce p q : π ((p ⊃ q) ⊃ p) ⇒ π p // 1
//symbol peirce (_ _:Prop) : Prop
//rule peirce &p &q → ((&p ⊃ &q) ⊃ &p) ⊃ &p

//Definition double_negation_elimination := forall P:Prop,   (* 2 *)
//  ~~P -> P.
//constant symbol double_negation_elimination p : π (¬ (¬ p)) ⇒ π p // 2
symbol double_negation_elimination (_ :Prop) : Prop
rule double_negation_elimination &p → (¬ (¬ &p)) ⊃ &p

//Definition de_morgan_not_and_not := forall P Q:Prop,       (* 3 *)
//  ~(~P /\ ~Q) -> P\/Q.
//constant symbol de_morgan_not_and_not p q : π (¬ (¬ p ∧ ¬q)) ⇒ π (p ∨ q) //3
symbol de_morgan_not_and_not (_ _:Prop) : Prop
rule de_morgan_not_and_not &p &q → (¬ (¬ &p ∧ ¬&q)) ⊃ (&p ∨ &q)

//Definition implies_to_or := forall P Q:Prop,               (* 4 *)
//  (P->Q) -> (~P\/Q).
//constant symbol implies_to_or p q : π (p ⊃ q) ⇒ π (¬p ∨ q)
symbol implies_to_or (_ _:Prop) : Prop
rule implies_to_or &p &q → (&p ⊃ &q) ⊃ (¬&p ∨ &q)

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
//theorem O_impl_1 : ∀p q, excl_mid p q ⇒ peirce p
//proof
//qed
//theorem _0_impl_1 : ∀(p q r : Prop), π (excl_mid p ⊃ peirce q r)
//proof
//  assume p q r Hexcl_mid Himpl
//qed

// Theorem _1_impl_2 : peirce -> double_negation_elimination.
// Proof.
// unfold peirce. unfold double_negation_elimination.
// intros Hyp P HypnotnotP.
// apply Hyp with False. intro H.
// apply HypnotnotP in H. contradiction.
// Qed.

// Theorem _2_impl_3 : double_negation_elimination -> de_morgan_not_and_not.
// Proof.
// unfold double_negation_elimination. unfold de_morgan_not_and_not.
// intros Hyp P Q Hand.
// apply Hyp.
// intros Hor. apply Hand. split.
//   + intro HP. apply Hor. left. assumption.
//   + intro HQ. apply Hor. right. assumption.
// Qed.

// Theorem _3_impl_4 : de_morgan_not_and_not -> implies_to_or.
// Proof.
// unfold de_morgan_not_and_not. unfold implies_to_or.
// intros Hyp P Q HypImpl. 
// apply Hyp. intro HypAnd. destruct HypAnd as [HypnotnotP HypnotQ].
// apply HypnotnotP. intro HP.
// apply HypnotQ. apply HypImpl. assumption.
// Qed.

// Theorem _4_impl_0 : 
// implies_to_or -> excluded_middle.
// Proof.
// unfold implies_to_or. unfold excluded_middle.
// intros Hyp1 P. apply or_commut. apply Hyp1.
// intro HypP. assumption.
// Qed.
