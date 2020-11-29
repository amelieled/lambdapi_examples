require open AL_library.Notation
require open AL_library.Constructive_logic

// Type of natural numbers
constant symbol nat : Set
set declared "ℕ"
definition ℕ ≔ τ nat
constant symbol zero : ℕ
constant symbol succ : ℕ → ℕ

// Enabling builtin natural number literals
set builtin "0"  ≔ zero
set builtin "+1" ≔ succ
assert 42 : ℕ             // example

// Induction principle
symbol nat_ind p : π (p 0) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)
rule nat_ind _  $u _  0      ↪ $u
with nat_ind $p $u $v (succ $n) ↪ $v $n (nat_ind $p $u $v $n)

//symbol nat_ind_math : π (∀ (λp : ℕ → Prop, p 0))
//Π(P :ℕ → Prop), π(∃P) → π (¬(∀ (λm:ℕ, ¬ (P m))))

// Injective principle
symbol nat_inj : Πn m, π ((succ n) = (succ m)) → π (n = m)  // A voir !

///////////////////////////////
// Addition
///////////////////////////////
//Fixpoint plus n m :=
//  match n with
//  | 0 => m
//  | S n' => S (plus n' m)
//  end.
symbol plus : ℕ → ℕ → ℕ
set infix left 6 "+" ≔ plus
assert λx y z,x+y+z ≡ λx y z,(x+y)+z // check that x+y=z is parsed correctly
rule       0 + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y)

// Eval compute in (0 + 1).
compute 0+1

// Eval compute in (plus 1 1).
compute plus 1 1

//Lemma plus_0_n : forall n, 0 + n = n.
//Proof.
//intro n. simpl. reflexivity.
//Qed.
theorem plus_0_n : Πn, π ((0 + n) = n)
proof
  assume n
  reflexivity
qed

// Addition is commutative
//Lemma plus_n_0 : forall n, n + O = n.
//Proof.
//induction n.
//+  simpl. reflexivity.
//+ simpl. rewrite IHn. reflexivity.
//Qed.
theorem plus_n_0 : Πn, π ((n + 0) = n)
proof
  assume n
  refine nat_ind (λz, (z + 0) = z) _ _ _
  // Case n = O
  refine eq_refl 0
  // Case = S n'
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity
qed

//rule $x + 0 ↪ $x

//Lemma plus_n_Sm : forall n m,
//  n + S m = S (n + m).
//Proof.
//induction n ; intro m ; simpl.
//+ reflexivity.
//+ rewrite IHn. reflexivity.
//Qed.
theorem plus_n_Sm : Πn m, π ((n + (succ m)) = (succ (n + m)))
proof
  assume n m
  refine nat_ind (λz, ((z + (succ m)) = (succ (z + m)))) _ _ n
  reflexivity
  simpl
  assume n' Hn'
  rewrite Hn'
  reflexivity
qed

//rule $x + succ $y ↪ succ ($x + $y)

//Lemma plus_comm : forall n m, n+m=m+n.
//Proof.
//induction n ; intros m0.
//+ simpl. rewrite plus_n_0. reflexivity.
//+ simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
//Qed.
theorem plus_comm : Πn m, π((n + m) = (m + n))
proof
  assume n m
  refine nat_ind (λz, ((z + m) = (m + z))) _ _ n
    simpl rewrite plus_n_0 reflexivity
    simpl assume n' Hn' rewrite Hn' rewrite plus_n_Sm reflexivity
qed

// Addition is associative
//Lemma plus_assoc : forall n m p,
//  n+(m+p) = n+m+p.
//Proof.
//induction n ; intros m p.
//+ simpl. reflexivity.
//+ simpl. rewrite IHn. reflexivity.
//Qed.
theorem plus_assoc : Πn m p, π ((n+(m+p)) = (n+m+p))
proof
  assume n m p
  refine nat_ind (λz, (z+(m+p)) = (z+m+p)) _ _ n
  reflexivity
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity
qed

//rule ($x + $y) + $z ↪ $x + ($y + $z)

/////////////////////////////////////
// Multiplication
/////////////////////////////////////
//Fixpoint mult (n m : nat) :  nat :=
//  match n with
//  | O => 0
//  | S n' => m + (mult n' m)
//  end.
symbol mult : ℕ → ℕ → ℕ
set infix left 7 "×" ≔ mult
rule       0 × _  ↪ 0
with succ $x × $y ↪ $y + $x × $y
assert λx y z,x+y×z ≡ λx y z,x+(y×z) // check that x+y×z is parsed correctly

//Lemma mult_0_n : forall n : nat, 0*n=0.
//Proof.
//intros. simpl. reflexivity.
//Qed.
theorem mult_0_n : Πn, π ((0 × n) = 0)
proof
  assume n
  refine eq_refl 0
qed

// Multiplication is commutative
//Lemma mult_n_0 : forall n, n*0= 0.
//Proof.
//induction n.
//+  apply mult_0_n.
//+  simpl. exact IHn.
// (* ou assumption*)
//Qed.
theorem mult_n_0 : Πn, π ((n × 0) = 0)
proof
  refine nat_ind (λz, (z × 0) = 0) _ _
  // Case n = O
  refine eq_refl 0
  // Case = S n'
  assume n' Hn'
  simpl
  apply Hn'
qed

// rule _ × 0 ↪ 0

//Lemma mult_n_Sm : forall n m, n*S m=n+n*m.
//Proof.
//induction n ; intros m0 ; simpl.
//+ reflexivity.
//+ rewrite IHn.
//  do 2 (rewrite plus_assoc).
//  rewrite plus_comm with (n:=n) (m := m0). reflexivity.
//Qed.
theorem mult_n_Sm : Πn m, π ((n × succ m) = (n + n × m))
proof
  assume n m
  refine nat_ind (λz, (z × succ m) = (z + z × m)) _ _ n
    reflexivity
    assume n' Hn' simpl rewrite Hn'
    rewrite plus_assoc rewrite plus_assoc rewrite plus_comm n' m reflexivity
qed

// rule $x × succ $y ↪ $x + $x × $y

//Lemma mult_comm : forall n m, n *m=m*n.
//Proof.
//induction n ; intros m0 ; simpl.
//+ rewrite mult_n_0. reflexivity.
//+ rewrite IHn. rewrite mult_n_Sm.  reflexivity.
//Qed.
theorem mult_comm : Πn m, π ((n×m) = (m×n))
proof
  assume n m
  refine nat_ind (λz, ((z × m) = (m × z))) _ _ n
    rewrite mult_n_0 reflexivity
    assume n' Hn' simpl rewrite Hn'
    rewrite mult_n_Sm reflexivity
qed

// Multiplication distributes over addition

//Lemma mult_plus_distr_r : forall n m p,
//  (n+m)*p = n*p+m*p.
//Proof.
//induction n ; intros m p; simpl.
//+ reflexivity.
//+ rewrite IHn. apply plus_assoc.
//Qed.
theorem mult_plus_distr_r :
Πn m p, π (((n+m)×p) = ((n×p)+(m×p)))
proof
  assume n m p
  refine nat_ind
         (λz, ((z+m)×p) = ((z×p)+(m×p))) _ _ n
    reflexivity
    assume n' Hn' simpl rewrite Hn'
    apply plus_assoc p (n'×p) (m×p) // pas inféré
qed

//rule ($x + $y) × $z ↪ $x × $z + $y × $z

// Prouver directement
//Lemma mult_plus_distr_l : forall n m p,
//  n*(m+p)=n*m+n*p.
//Proof.
//induction n; intros m p ; simpl.
//+ reflexivity.
//+ rewrite IHn.
//    rewrite plus_comm with (n:=p) (m:=n*p).
//    rewrite <- plus_assoc with (n:=m) (m:=n*m) (p:=n*p+p).
//    rewrite plus_comm with (n:=m) (m:=n*m + (n*p + p)).
//    do 2 (rewrite plus_assoc).
//    rewrite plus_comm with (n:=m) (m:=p).
//    rewrite <- plus_assoc with (n:=p + m) (m:=n*m) (p:=n*p).
//    rewrite plus_comm with (n:=p + m) (m:=n*m + n*p).
//    rewrite plus_assoc. reflexivity.
//Qed.
theorem plus_assoc_trash : Πn m p, π ((n+m+p) = (n+(m+p)))
proof
  assume n m p
  refine nat_ind (λz, (z+m+p) = (z+(m+p))) _ _ n
  reflexivity
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity
qed
theorem mult_plus_distr_l :
Πn m p, π ((n×(m+p)) = ((n×m)+(n×p)))
proof
  assume n m p
  refine nat_ind (λz, (z×(m+p)) = ((z×m)+(z×p))) _ _ n
  // 0. π ((zero × (m + p)) = ((zero × m) + (zero × p)))
  reflexivity
  //1. Π(x:τ nat), π ((x × (m + p)) = ((x × m) + (x × p))) →
  //       π ((succ x × (m + p)) = ((succ x × m) + (succ x × p)))
  simpl assume n' IHn' rewrite IHn'
  rewrite plus_comm p (n'×p)
  rewrite plus_assoc_trash m (n'×m) ((n'×p)+p)
  rewrite plus_comm m (n'×m + (n'×p + p))
  rewrite plus_assoc rewrite plus_assoc
  rewrite plus_comm m p
  rewrite plus_assoc_trash (p+m) (n'×m) (n'×p)
  rewrite plus_comm (p + m) (n'×m + n'×p)
  rewrite plus_assoc reflexivity
qed

//  Prouver en utilisant les lemmes précédents
//  (mais bien sûr pas [mult_plus_distr_l])
//Lemma mult_plus_distr_l_bis : forall n m p,
//  n*(m+p)=n*m+n*p.
//Proof.
//intros n m p.
//rewrite mult_comm with (n := n) (m := m).
//rewrite mult_comm with (n := n) (m := p).
//rewrite <- mult_plus_distr_r.
//apply mult_comm.
//Qed.
theorem mult_plus_distr_l_bis :
  Πn m p, π ((mult n (plus m p)) = (plus (mult n m) (mult n p)))
proof
  assume n m p
  rewrite mult_comm n m
  rewrite mult_comm n p
  rewrite mult_comm n (plus m p)
  symmetry
  rewrite mult_plus_distr_r
  reflexivity
qed
// theorem mul_addr x y z : π (z×(x+y) = z×x+z×y)
// proof
//   assume x y z
//   rewrite mul_com
//   rewrite mul_addl
//   rewrite mul_com
//   rewrite [y×_]mul_com
//   reflexivity
// qed

//rule $z × ($x + $y) ↪ $z × $x + $z × $y

// Multiplication is associative
//Lemma mult_assoc : forall n m p, n*(m*p) = (n*m)*p.
//Proof.
//induction n ; intros m p; simpl.
//+ reflexivity.
//+ rewrite IHn. rewrite mult_plus_distr_r. reflexivity.
//Qed.
theorem mult_assoc : Π n m p, π ((n×(m×p)) = ((n×m)×p))
proof
  assume n m p
  refine nat_ind (λz, ((z×(m×p)) = ((z×m)×p))) _ _ n
    reflexivity
    simpl assume n' Hn' // simpl
    rewrite Hn'
    rewrite mult_plus_distr_r // m (mult n' m) p
    reflexivity
qed

//rule ($x × $y) × $z ↪ $x × ($y × $z)

// Doubling function.
definition double n ≔ n×2
