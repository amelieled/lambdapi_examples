require open amelie.Bool_discriminate
require open amelie.Bool
require open amelie.Logic
require open amelie.Notation

// Check True. (* True : Prop *)
type true // (* true : B *)

// Check True -> False. (* True -> False : Prop *)
type (⊤ ⊃ ⊥) // imp ⊤ ⊥ : Prop

type _ ⇒ _ // ?201 ⇒ ?199 : TYPE

// Lemma bool_trivial : forall (P : bool -> Prop) b, P b -> P b.
// Admitted.
theorem bool_trivial : ∀p:B⇒Prop,∀b, π (p b) ⇒ π (p b)
//π (imp (P b) (P b))
proof
  assume P b H
  apply H
qed

//Lemma bool_ext : forall (P : bool -> Prop), P true /\ P false ->
//  forall b, P b.
//Admitted.
theorem bool_ext :
∀p, π (p true ∧ p false) ⇒ ∀b, π(p b)
proof
  assume P Hp b
  refine bool_ind (λz, P z) _ _ _
  apply conj_elim_left _ (P false)
  refine Hp
  apply conj_elim_right (P true) _
  apply Hp
qed

//Lemma bool_ext2 : forall (P : bool -> Prop), P true -> P false ->
//  forall b, P b.
//Admitted.
theorem bool_ext2 :
∀p, π (p true) ⇒ π (p false) ⇒ ∀b, π (p b)
proof
  assume P HPT HPF b
  refine bool_ind (λz, P z) _ _ _
  apply HPT
  apply HPF
qed

//Lemma andb_prop : forall b1 b2,
//  andb b1 b2 = true -> b1 = true /\ b2 = true.
//Proof.
//  intros b1 b2 H.
//  (* introduit les hypothèses *)
//  split. (* sépare le but en deux sous-buts *)
//  - destruct b1. (* raisonnement par cas *)
//    + reflexivity. (* true = true *)
//    + simpl in H. discriminate H. (* false <> true *)
//  - destruct b2. (* raisonnement par cas *)
//    + reflexivity. (* true = true *)
//    + destruct b1 .  (* raisonnement par cas *)
//      * simpl in H. discriminate H. (* false <> true *)
//      * simpl in H. discriminate H. (* false <> true *)
//Qed.
//theorem andb_prop : // Il me manque un outil pour y arriver avec cet énoncé
//∀b1 b2, π (eq {bool} (andb b1 b2) true) ⇒
//                    π ((eq {bool} b1 true) ∧ (eq {bool} b2 true))
theorem andb_prop b1 b2
  : π (imp (andb b1 b2 = true) ((b1 = true) ∧ (b2 = true)))
proof
  assume b1 b2
  refine bool_ind (λz, imp (andb z b2 = true) ((z = true) ∧ (b2 = true))) _ _ _
  // Case b1 = true
  simpl
  assume H
  apply conj_intro
  reflexivity
  apply H
  // Case b1 = false
  simpl
  assume H
  apply false_elim (false = true ∧ b2 = true)
  apply discr_f_t apply H
qed

//[andb_true_iff : forall b1 b2,andb b1 b2 = true <-> b1 = true /\ b2 = true]
//    Montrer [or_true_iff], un résultat similaire sur [or].
theorem andb_true_iff b1 b2
  : π ((andb b1 b2 = true) ⇔ ((b1 = true) ∧ (b2 = true)))
proof
  assume b1 b2
  refine bool_ind (λz, imp ((andb z b2) =  true)
                           (z = true ∧ b2 = true) ∧
                       imp (z = true ∧ b2 = true)
                           ((andb z b2) = true)) _ _ _
  // Case b1 = true
  simpl
  apply conj_intro
    assume H apply conj_intro
      reflexivity
      apply H
    assume H apply conj_elim_right (true = true) apply H
  // Case b1 = false
  simpl
  apply conj_intro
    assume H
      apply false_elim (false = true ∧ b2 = true)
      apply discr_f_t apply H
  assume H apply conj_elim_left _ (b2 = true) apply H
qed

theorem or_true_iff b1 b2 : π (((or b1 b2) = true) ⇔ (b1 = true ∨ b2 = true))
proof
  assume b1 b2
  refine bool_ind (λz, imp ((or z b2) = true)
                           (z = true ∨ b2 = true) ∧
                       imp (z = true ∨ b2 = true)
                           ((or z b2) = true)) _ _ _
  // Case b1 = true
  simpl
  apply conj_intro
    assume H apply disj_intro_left apply H
    assume H reflexivity
  // Case b1 = false
  simpl
  apply conj_intro
    assume H apply disj_intro_right apply H
    assume H apply disj_elim (false = true) (b2 = true) (b2 = true) apply H
      assume Hfalse apply false_elim (b2 = true) apply discr_f_t apply Hfalse
      assume H2 apply H2
qed
