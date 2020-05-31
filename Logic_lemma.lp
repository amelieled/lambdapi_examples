require open amelie.lambdapi_examples.Notation
require open amelie.lambdapi_examples.Constructive_logic
require open amelie.lambdapi_examples.Nat

//Lemma impl_and : forall P Q R : Prop, (P->Q->R) -> (P /\ Q -> R).
//Proof
//intros P Q R Hyp1 Hyp2.
//destruct Hyp2 as [Hp Hq].
//apply Hyp1 ; assumption.
//Qed.
theorem impl_and : ΠP Q R : Prop, π ((P ⊃ (Q ⊃ R)) ⊃ ((P ∧ Q) ⊃ R))
proof
  assume P Q R Himpl Hand
  apply Himpl
  apply conj_elim_left P Q  apply Hand
  apply conj_elim_right P Q apply Hand
qed

//Lemma conj_impl : forall P Q R : Prop, (P /\ Q -> R) -> (P -> Q -> R).
//Proof.
//intros P Q R Hyp1 H1 H2.
//apply Hyp1.
//split ; assumption.
//Qed.
theorem conj_impl : ΠP Q R : Prop, π (((P ∧ Q) ⊃ R) ⊃ (P ⊃ (Q ⊃ R)))
proof
  assume P Q R Hand HP HQ
  // Goal π ((P ∧ Q) ⊃ R)
  apply Hand
  // Goal  π (P ∧ Q)
  apply conj_intro P Q
    apply HP
    apply HQ
qed

//Lemma conj_impl_iff : forall P Q R : Prop,
//   (P /\ Q -> R) <-> (P -> Q -> R).
//Proof.
//split.
//+ apply conj_impl.
//+ apply impl_and.
//Qed.
theorem conj_impl_iff : ΠP Q R : Prop,
π (((P ∧ Q) ⊃ R) ⇔ (P ⊃(Q ⊃ R)))
proof
  assume P Q R
  apply conj_intro
     apply conj_impl P Q R
     apply impl_and P Q
qed

//Lemma impl_not : forall P : Prop, P -> ~ ~ P.
//Proof.
//intros P Hyp.
//unfold not.
//intro Hyp1.
//apply Hyp1.
//assumption.
//Qed.
theorem impl_not : ΠP : Prop, π P → π (¬ (¬ P))
proof
  assume P HP
  //apply neg_intro (¬ P)
  assume HnotP
  //apply neg_elim P
  apply HnotP
  apply HP
qed

//Lemma modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
//Proof.
//intros P Q H1 H2.
//apply H2.
//assumption.
//Qed.
theorem modus_ponens : ΠP Q : Prop, π P → (π P → π Q) → π Q
proof
  assume P Q HP Himp
  apply Himp
  apply HP
qed

// en utilisant [modus_ponens]
//Lemma impl_neg_bis : forall P : Prop, P -> ~ ~ P.
//Proof.
//intro P. unfold not.
//apply modus_ponens.
//Qed.
theorem impl_neg_bis : ΠP : Prop, π P → π (¬ (¬ P))
proof
  assume P
  refine modus_ponens P ⊥
qed

// à partir de [impl_not]
//Lemma P_notP_contradiction : forall P : Prop, ~ (P /\ ~ P).
//Proof.
//intro P.
//unfold not .
//(*apply impl_and.
//apply modus_ponens.*)
//intro H1.
//destruct H1 as [HH1 HH2].
//apply HH2. assumption.
//Qed.
theorem P_notP_contradiction : ΠP : Prop, π (¬(P ∧ ¬P))
proof
  assume P Hand
  //apply neg_intro (P ∧ ¬P)
  apply neg_elim P
     apply conj_elim_right P (¬ P) simpl  apply Hand  //@HIC
     apply conj_elim_left _ (¬P) apply Hand
qed

//Lemma neg_and : forall P Q : Prop, P \/ Q -> ~(~ P /\ ~Q).
//Proof.
//Admitted.
theorem neg_and : ΠP Q : Prop, π (P ∨ Q) → π (¬(¬P ∧ ¬Q))
proof
  assume P Q Hor Hand
  refine disj_elim P Q ⊥ _ _ _
  // Case π (P ∨ Q)
  apply Hor
  // Case π P → π ⊥
  refine conj_elim_left (¬P) (¬Q) _ apply Hand
  // Case π Q → π ⊥
  refine conj_elim_right (¬P) (¬Q) _ apply Hand
qed

//Lemma exists_neg_forall : forall P : nat -> Prop,
//(exists n, P n) ->  ~(forall n,~ (P n)).
//Proof.
//intros P H H1.
//destruct H as [n0 H0].
//specialize (H1 n0).
//contradiction.
//Qed.
theorem exists_neg_forall :
Π(P :ℕ → Prop), π(∃P) → π (¬(∀ (λm:ℕ, ¬ (P m))))
proof
  assume P Hexists Hforall
  //apply H2
  apply ex_elim {nat} P ⊥
  apply Hexists
  refine Hforall // OU assume x H apply Hforall x H
qed
