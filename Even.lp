require open amelie.Notation
require open amelie.Logic
require open amelie.Bool
require open amelie.Nat
require open amelie.Op_bool

//////////////////////////
//  Un exemple de prédicat inductif : even
//////////////////////////

//Definition is_even n := exists p, n = 2 * p.
definition is_even n ≔ ∃(λp, n = (2×p))

//Lemma zero_is_even : is_even 0.
//Proof.
//unfold is_even.
//exists 0. simpl. reflexivity.
//Defined.
theorem zero_is_even : π (is_even 0)
proof
  apply ex_intro (λp, 0 = ((succ (succ 0))×p)) 0
  reflexivity
qed

//Lemma is_even_plus : forall n p,
//   is_even n -> is_even p -> is_even (n + p).
//Proof.
//intros n p Hn Hp.
//unfold is_even in Hn.
//destruct Hn as [k Hk].
//destruct Hp as [t Ht].
//unfold is_even.
//exists (k + t).
//rewrite  mult_plus_distr_l.
//rewrite Hk.  rewrite Ht. reflexivity.
//Qed.
theorem is_even_plus :
  ∀n p, π (is_even n) ⇒ π (is_even p) ⇒ π (is_even (n+p))
proof
  assume n p Hn Hp
  apply ex_elim (λp, n = ((succ (succ 0))×p))   apply Hn assume x Hx
  apply ex_elim (λp0, p = ((succ (succ 0))×p0)) apply Hp assume y Hy
  apply ex_intro (λp0, (n+p) = ((succ (succ 0))×p0)) (x+y)
  rewrite mult_plus_distr_l
  rewrite  Hx rewrite Hy reflexivity
qed

// On rappelle la définition de [even] sous forme d'un prédicat inductif.

//Inductive even : nat -> Prop :=
//| even_0 : even 0
//| even_SS : forall n, even n -> even (succ (succ n)).
symbol even : ℕ ⇒ Prop
constant symbol even_0 : π (even 0)
constant symbol even_SS n : π (imp (even n) (even (succ (succ n))))
constant symbol even_0_coq : π (even 0)
constant symbol even_SS_coq n : π (even n) ⇒ π (even (succ (succ n)))

//Lemma even_4 : even 4.
//Proof.
//apply even_SS. apply even_SS. apply even_0.
//Qed.
// theorem even_4 : π (even 4)
// proof
//   apply imp_elim (even  (succ (succ O))) apply even_S (succ (succ O))
//   apply imp_elim (even  O) apply even_SS O
//   apply even_0
// qed
theorem even_4_coq : π (even 4)
proof
  apply even_SS_coq (succ (succ 0)) apply even_SS_coq 0 apply even_0
qed

//                             ou avec une syntaxe fonctionnelle
//Theorem even_4' : even 4.
//Proof. exact (even_SS 2 (even_SS 0 even_0)).
//Qed.
theorem even_4' : π (even 4)
proof
  apply (even_SS_coq (succ (succ 0)) (even_SS_coq 0 even_0))
qed

//Theorem even_plus4 : forall n, even n -> even (4 + n).
//Proof.
//  intros n. simpl. intros Hn.
//  apply even_SS. apply even_SS. assumption.
//Qed.
//theorem even_plus4 : π (all (λn:N) (imp (even n) (even (plus 4 n))))
theorem even_plus4 : ∀n, π (imp (even n) (even (4+n)))
proof
  assume n Heven
  apply even_SS_coq (succ (succ n))
  apply even_SS_coq n
  apply Heven
qed

symbol even_inject : ∀n, (π (n = 0) ⇒ π (even 0))
  ⇒ (π (∃(λp,n = succ (succ p) ⊃ even p ⊃ even (succ (succ p)))) ⇒ π (even n))
symbol even_inj : ∀n,  π (even n) ⇒ (π (n = 0) ⇒ π (even 0))
  ⇒ (π (∃(λp,n = succ (succ p) ⊃ even p ⊃ even (succ (succ p)))))
//Theorem ev_minus2 : forall n,
//  even n -> even (pred (pred n)).
//Proof.
//  intros n H.
//  inversion H  as [| p Hp].
//  - (* H = even_0 *) simpl. apply even_0.
//  - (* H = even_SS p Hp *) simpl. exact Hp (* ou assumption*).
//Qed.
symbol pred : ℕ ⇒ ℕ
rule pred     0     → 0
 and pred (succ &n) → &n

theorem ev_minus2 : ∀n, π (imp (even n) (even (pred (pred n))))
proof
  assume n Heven
  //apply even_inj
  //apply nat_ind (λz, imp (even z) (even (pred (pred z)))) _ _ n
         //simpl assume Heven0 apply even_0_coq
         //simpl assume x Himpl Hevensuccx //assume n assume Heven
admit//@TODO 5 inversion

//Theorem even5_nonsense :
//  even 5 -> 2 + 2 = 9.
//Proof.
//  intro H.
//  inversion H.
//  inversion H1.
//  inversion H3.
//Qed.
theorem even5_nonsense : π (even 5) ⇒ π ((2+2) = 9)
proof
admit //@TODO 6 inversion

//Lemma ev_even : forall n,
//  even n -> exists k, n = 2 * k.
//Proof.
//  intros n E.
//  induction E as [|k Hk IH].
//  - (* E = even_0 *)
//    exists 0. reflexivity.
//  - (* E = even_SS k Hk
//       with IH : exists k', n' = double k' *)
//    destruct IH as [k' Hk'].
//    rewrite Hk'. exists (succ k'). simpl.
//    succearch plus.
//    rewrite <- plus_n_succm.
//    replace (k' + 0) with k'. reflexivity.
//    apply plus_n_O.
//Qed.
theorem ev_even : ∀n, π (even n) ⇒ π (∃(λk, n = (2×k)))
proof
admit //@TODO 7

//  Prouver les lemmes suivants.

//Lemma even_n_disj_succn : forall n, even n \/ even (succ n).
//Proof.
//induction n.
// * left. constructor.
// * destruct IHn.
//    + right. constructor. assumption.
//    + left. assumption.
//Defined.
theorem even_n_disj_succn : ∀n, π (even n ∨ even (succ n))
proof
  assume n
  apply nat_ind (λz, even z ∨ even (succ z)) _ _ n
  // 0. π (even O ∨ even (succ O))
  apply disj_intro_left apply even_0_coq
  //1. ∀(x:τ nat), π (even x ∨ even (succ x)) ⇒ π (even (succ x) ∨ even (succ (succ x)))
  assume x HypOr
  apply disj_elim (even x) (even (succ x))
        // 0. π (even x ∨ even (succ x))
        apply HypOr
        // 1. π (even x) ⇒ π (even (succ x) ∨ even (succ (succ x)))
        assume Hevenx
        apply disj_intro_right
        apply even_SS_coq x apply Hevenx
        // 2. π (even (succ x)) ⇒ π (even (succ x) ∨ even (succ (succ x)))
        assume Hevensuccx
        apply disj_intro_left apply Hevensuccx
qed

//Lemma even_n_neg_succn : forall n, even n -> ~ even (succ n).
//Proof.
//induction n;intro Hyp1;unfold not;intro Hyp2.
//  * inversion Hyp2.
//  * inversion Hyp2. unfold not in IHn. apply IHn;assumption.
//Defined.
theorem even_n_neg_succn : ∀n, π (even n) ⇒ π (¬ (even (succ n)))
proof
admit //@TODO 8 inversion

//Lemma even_dec : forall n, even n \/ ~ even n.
//Proof.
//intro n.
//assert(even n \/ even (succ n)) by (apply even_n_or_succn).
//destruct H as [| HypN].
//  * left. assumption.
//  * right. intro H. apply even_n_not_succn in H.
//    contradiction.
//Defined.
theorem even_dec : ∀n, π (even n ∨ ¬(even (succ n)))
proof
admit //@TODO 9 assert

//  Induction de 2 en 2.
//Lemma two_steps_induction : forall P : nat -> Prop, P 0 -> P 1 ->
//  (forall n, P n -> P (succ (succ n))) ->
//  forall n, P n.
//Proof.
//  intros P H0 H1 IHn.
//  assert (forall n, P n /\ P (succ n)) as Hn.
//   - induction n.
//      + split;assumption.
//      + decompose [and] IHn0. apply IHn in H.
//        split;assumption.
//   - induction n.
//      + assumption.
//      + assert(P n /\ P (succ n)) by (apply Hn).
//        decompose [and] H. assumption.
//Defined.
theorem two_steps_induction : ∀(p : ℕ ⇒ Prop),
π(p 0) ⇒ π(p 1) ⇒ π (forall (λn, p n ⊃ p (succ (succ n)))) ⇒
π (forall (λn, p n))
proof
  assume p Hp0 Hp1 IHn x //(forall n, P n /\ P (succ n))

admit //@TODO 10 assert

// Définir [evenb : nat -> bool] qui teste si un entier est pair.

//Fixpoint evenb (n:nat) : bool := match n with
//| O => true
//| succ a => negb (evenb a)
symbol evenb : ℕ ⇒ B
rule evenb     0     → true
 and evenb (succ &a) → neg (evenb &a)

//    Prouver les lemmes suivants. succi vous avez besoin de résultats sur les
//    booléens, vous pouvez les trouver dans [Bool]
//    (utiliser [Require Import Bool.]).

//Lemma evenb_correct : forall n, evenb n = true -> even n.
//Proof.
//intros n H. induction n using two_steps_induction.
// + constructor.
// + inversion H.
// + constructor. apply IHn.
//   inversion H.
//   apply Bool.negb_involutive_reverse.
//Defined.
theorem evenb_correct : ∀n, π (evenb n = true) ⇒ π (even n)
proof
admit //@TODO 11 inversion

//Lemma evenb_complete : forall n, even n -> evenb n = true.
//Proof.
//intros n H. induction n using two_steps_induction.
// + constructor.
// + inversion H.
// + inversion H. apply IHn in H1.
//   simpl.
//   rewrite Bool.negb_involutive_reverse.
//   rewrite H1. reflexivity.
//Defined.
theorem evenb_complete : ∀n, π (even n) ⇒  π (evenb n = true)
proof
admit //@TODO 12 inversion

//Definition evenb_spec : forall n, evenb n = true <-> even n.
//Proof.
//split.
// + apply evenb_correct.
// + apply evenb_complete.
//Defined.
theorem evenb_spec : ∀n, π (evenb n = true ⇔ even n)
proof
 assume n
  apply conj_intro
  refine evenb_correct n  //assume Hyp apply evenb_correct n Hyp
  refine evenb_complete n //assume Hyp apply evenb_complete n Hyp
qed

// Prouver [even_dec_bis : forall n, even n \/ ~ even n]
// en utilisant [evenb_spec].

//Lemma even_dec_bis : forall n, even n \/ ~ even n.
//Proof.
//intro n. destruct (evenb n) eqn:H.
// * left. apply evenb_correct;assumption.
// * right. unfold not;intro.
//   apply evenb_complete in H0.
//   rewrite H in H0. inversion H0.
//Defined.
theorem even_dec_bis : ∀n, π (even n ∨ ¬(even n))
proof
admit //@TODO 13 destruct + inversion