require open amelie.lambdapi_examples.Notation
require open amelie.lambdapi_examples.Constructive_logic
require open amelie.lambdapi_examples.Discriminate
require open amelie.lambdapi_examples.Bool
require open amelie.lambdapi_examples.Nat
//require open amelie.Op_bool

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
  Πn p, π (is_even n) → π (is_even p) → π (is_even (n+p))
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
symbol even : ℕ → Prop
constant symbol even_0 : π (even 0)
constant symbol even_SS n : π (imp (even n) (even (succ (succ n))))
constant symbol even_0_coq : π (even 0)
constant symbol even_SS_coq n : π (even n) → π (even (succ (succ n)))

symbol even_ind : Πp, π (p 0) → (Πn, π (even n) → π (p n) → π (p (succ (succ n)))) → Πn, π (even n) → π (p n)

// symbol even_inject : Πn, (π (n = 0) → π (even 0))
//   → (π (∃(λp,n = succ (succ p) ⊃ even p ⊃ even (succ (succ p)))) → π (even n))
// symbol even_inj : Πn,  π (even n) → (π (n = 0) → π (even 0))
//   → (π (∃(λp,n = succ (succ p) ⊃ even p ⊃ even (succ (succ p)))))

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
theorem even_plus4 : Πn, π (imp (even n) (even (4+n)))
proof
  assume n Heven
  apply even_SS_coq (succ (succ n))
  apply even_SS_coq n
  apply Heven
qed

//Theorem ev_minus2 : forall n,
//  even n -> even (pred (pred n)).
//Proof.
//  intros n H.
//  inversion H  as [| p Hp].
//  - (* H = even_0 *) simpl. apply even_0.
//  - (* H = even_SS p Hp *) simpl. exact Hp (* ou assumption*).
//Qed.
symbol pred : ℕ → ℕ
rule pred     0     ↪ 0
 with pred (succ $n) ↪ $n

theorem succ_pred : Πn, π (¬ (n = 0)) → π (succ (pred n) = n) // inutile
proof
  refine nat_ind _ _ _
  // 0. (π (zero = zero) → π ⊥) → π (succ (pred zero) = zero)
  simpl assume Hfalse apply false_elim apply Hfalse reflexivity
  // 1. Π(x:τ nat), ((π (x = zero) → π ⊥) → π (succ (pred x) = x)) → (π (succ x = zero) → π ⊥)
  //                         → π (succ (pred (succ x)) = succ x)
  assume x Hnotzero Hsuccpredx
  reflexivity
qed

symbol even_inv : Πn, π (even (succ (succ n))) → π (even n)
symbol notEven1 : π (even 1) → π (⊥)

theorem ev_minus2 : Πn, π (imp (even n) (even (pred (pred n))))
proof
  //assume n Heven
  refine even_ind _ _ _
  //0. π (even (pred (pred zero)))
  simpl apply even_0
  //1. Π(n:τ nat), π (even n) → π (even (pred (pred n))) → π (even (pred (pred (succ (succ n)))))
  assume n Heven Hpredpred
  simpl apply Heven
qed// @DONE even_1 inversion

//Theorem even5_nonsense :
//  even 5 -> 2 + 2 = 9.
//Proof.
//  intro H.
//  inversion H.
//  inversion H1.
//  inversion H3.
//Qed.
theorem even5_nonsense : π (even 5) → π ((2+2) = 9)
proof
  assume H5
  apply false_elim
  apply notEven1
  apply even_inv (succ zero)
  apply even_inv (succ (succ (succ zero))) apply H5
qed //@DONE even_2 inversion/adaptation

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
//    Search plus.
//    rewrite <- plus_n_Sm.
//    replace (k' + 0) with k'. reflexivity.
//    apply plus_n_O.
//Qed.
theorem ev_even : Πn, π (even n) → π (∃(λk, n = (2×k)))
proof
  refine even_ind _ _ _
  // 0. π (∃ (λk, zero = (succ (succ zero) × k)))
  apply ex_intro _ 0 reflexivity
  // 1. Π(n:τ nat), π (even n) → π (∃ (λk, n = (succ (succ zero) × k))) → π (∃ (λk, succ (succ n) = (succ (succ zero) × k)))
  assume n Hevenn Hex
  apply ex_elim (λk, n = (succ (succ zero) × k)) apply Hex
  assume x Hx apply ex_intro _ (x+1) rewrite Hx simpl
  rewrite plus_n_Sm
//    replace (k' + 0) with k'. reflexivity.
  rewrite plus_n_0 rewrite plus_n_0 simpl
  rewrite plus_n_Sm simpl reflexivity
qed

//  Prouver les lemmes suivants.

//Lemma even_n_disj_succn : forall n, even n \/ even (succ n).
//Proof.
//induction n.
// * left. constructor.
// * destruct IHn.
//    + right. constructor. assumption.
//    + left. assumption.
//Defined.
theorem even_n_disj_succn : Πn, π (even n ∨ even (succ n))
proof
  assume n
  apply nat_ind (λz, even z ∨ even (succ z)) _ _ n
  // 0. π (even O ∨ even (succ O))
  apply disj_intro_left apply even_0_coq
  //1. Π(x:τ nat), π (even x ∨ even (succ x)) → π (even (succ x) ∨ even (succ (succ x)))
  assume x HypOr
  apply disj_elim (even x) (even (succ x))
        // 0. π (even x ∨ even (succ x))
        apply HypOr
        // 1. π (even x) → π (even (succ x) ∨ even (succ (succ x)))
        assume Hevenx
        apply disj_intro_right
        apply even_SS_coq x apply Hevenx
        // 2. π (even (succ x)) → π (even (succ x) ∨ even (succ (succ x)))
        assume Hevensuccx
        apply disj_intro_left apply Hevensuccx
qed

//Lemma even_n_neg_succn : forall n, even n -> ~ even (succ n).
//Proof.
//induction n;intro Hyp1;unfold not;intro Hyp2.
//  * inversion Hyp2.
//  * inversion Hyp2. unfold not in IHn. apply IHn;assumption.
//Defined.
theorem even_n_neg_succn : Πn, π (even n) → π (¬ (even (succ n)))
proof
  refine nat_ind _ _ _
  // 0. π (even zero) → π (even (succ zero)) → π ⊥
  assume Heven0 refine notEven1
  // 1. Π(x:τ nat), (π (even x) → π (even (succ x)) → π ⊥) → π (even (succ x)) → π (even (succ (succ x))) → π ⊥
  assume x IHx Hsucc Hsuccsucc
  apply IHx
        // 0. π (even x)
        apply even_inv x refine Hsuccsucc
        // 1. π (even (succ x))
        apply Hsucc
qed //@DONE even_3 inversion

//Lemma even_dec : forall n, even n \/ ~ even n.
//Proof.
//intro n.
//assert(even n \/ even (succ n)) by (apply even_n_or_succn).
//destruct H as [| HypN].
//  * left. assumption.
//  * right. intro H. apply even_n_not_succn in H.
//    contradiction.
//Defined.
theorem even_dec : Πn, π (even n ∨ ¬(even n))
proof
  assume n
  apply disj_elim (even n) (even (succ n))
  apply even_n_disj_succn n
     // 0. π (even n) → π (even n ∨ ¬ (even (succ n)))
     assume Hn apply disj_intro_left apply Hn
     //1. π (even (succ n)) → π (even n ∨ ¬ (even (succ n)))
     assume Hsuccn apply disj_intro_right
     assume Hn
     refine even_n_neg_succn n Hn Hsuccn
qed

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
theorem assert_for_two_steps_induction : Πp, π (p 0) → π (p 1) →
(Πn, π (p n) → π (p (succ (succ n)))) →
(Πn, π (p n ∧ p (succ n)))
proof
  assume p Hp0 Hp1 Hn
  refine nat_ind _ _ _
  // 0. π (p zero ∧ p (succ zero))
  apply conj_intro refine Hp0 apply Hp1
  // 1. Π(x:τ nat), π (p x ∧ p (succ x)) → π (p (succ x) ∧ p (succ (succ x)))
  assume x Hx
  apply conj_intro
         // 0. π (p (succ x))
         apply conj_elim_right (p x) apply Hx
         //1. π (p (succ (succ x)))
         apply Hn x
         apply conj_elim_left _ (p (succ x)) apply Hx
qed

theorem two_steps_induction : Π(p : ℕ → Prop),
π(p 0) → π(p 1) → π (∀ (λn, p n ⊃ p (succ (succ n)))) →
π (∀ (λn, p n))
proof
  assume p Hp0 Hp1 IHn
  refine nat_ind _ _ _
  // 0. π (p zero)
  apply Hp0
  //1. Π(x:τ nat), π (p x) → π (p (succ x))
  //assert(P n /\ P (succ n)) by (apply Hn).
//        decompose [and] H. assumption
  assume x Hx
  apply conj_elim_right (p x)
  refine assert_for_two_steps_induction p Hp0 Hp1 IHn x
qed

// Définir [evenb : nat -> bool] qui teste si un entier est pair.

//Fixpoint evenb (n:nat) : bool := match n with
//| O => true
//| succ a => negb (evenb a)
symbol evenb : ℕ → 𝔹
rule evenb     0     ↪ true
 with evenb (succ $a) ↪ neg (evenb $a)

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
theorem neg_involutive_reverse : Πb, π (b = neg (neg b))
proof
  refine bool_ind _ _ _
  // 0. π (true = neg (neg true))
  reflexivity
  //1. π (false = neg (neg false))
  reflexivity
qed

theorem evenb_correct : Πn, π (evenb n = true) → π (even n)
proof
  refine two_steps_induction _ _ _ _
  // 0. π (evenb zero = true) → π (even zero)
  assume H0 apply even_0
  // 1. π (evenb (succ zero) = true) → π (even (succ zero))
  simpl assume Hfalsetrue
  apply false_elim apply discr_f_t apply Hfalsetrue
  // 2. Π(x:τ nat), (π (evenb x = true) → π (even x)) → π (evenb (succ (succ x)) = true) → π (even (succ (succ x)))
  simpl assume x IHn Hsuccsucc
  apply even_SS_coq x apply IHn
  rewrite neg_involutive_reverse (evenb x) apply Hsuccsucc
qed//@DONE even_4 inversion

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
theorem neg_involutive_reverse_trash : Πb, π (neg (neg b) = b)
proof
  refine bool_ind _ _ _ reflexivity reflexivity
qed

theorem evenb_complete : Πn, π (even n) →  π (evenb n = true)
proof
  refine two_steps_induction _ _ _ _
  // 0. π (even zero) → π (evenb zero = true)
  assume H0 reflexivity
  // 1. π (even (succ zero)) → π (evenb (succ zero) = true)
  assume Hsucc0 apply false_elim apply notEven1 apply Hsucc0
  // 2. Π(x:τ nat), (π (even x) → π (evenb x = true)) → π (even (succ (succ x))) → π (evenb (succ (succ x)) = true)
  simpl assume x IHn Hsuccsucc
  //apply even_SS_coq x apply IHn
  rewrite neg_involutive_reverse_trash
  apply IHn apply even_inv x apply Hsuccsucc
qed //@DONE even_5 inversion

//Definition evenb_spec : forall n, evenb n = true <-> even n.
//Proof.
//split.
// + apply evenb_correct.
// + apply evenb_complete.
//Defined.
theorem evenb_spec : Πn, π (evenb n = true ⇔ even n)
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
symbol bool_case :
Πp b, π((b = true) ⊃ (p b)) → π((b = false) ⊃ (p b)) → π(p b)

constant symbol eq_ind2 {a} (x y : τ a) : π (x = y) → Πp, π (p x) → π (p y)

theorem even_dec_bis : Πn, π (even n ∨ ¬(even n))
proof
  assume n
  refine bool_case (λb, (even n ∨ ¬(even n))) (evenb n) _ _
  // 0. π (evenb n = true) → π (even n ∨ ¬ (even n))
  assume Hevenbtrue apply disj_intro_left refine evenb_correct n Hevenbtrue
  // 1. π (evenb n = false) → π (even n ∨ ¬ (even n))
  assume Hevenbfalse apply disj_intro_right
  assume Hevenn apply discr_f_t
  refine eq_ind2 (evenb n) false Hevenbfalse (λz, z = true) _
  //rewrite Hevenbfalse
  refine evenb_complete n Hevenn
qed //@DONE even_6 destruct eqn + inversion
