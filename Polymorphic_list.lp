require open amelie.Notation
require open amelie.Bool
require open amelie.Nat
require open amelie.Logic

//////////////////////////////////////
// Type of polymorphic lists
//////////////////////////////////////
// Inductive list {A:Type} : Type :=
// | nil : list A
// | cons : A -> list A -> list A .
constant symbol list : Set ⇒ Set
set declared "𝕃"
definition 𝕃a ≔ τ (list a)
set declared "□"
constant symbol □ {a} : 𝕃a
constant symbol cons {a} : τa ⇒ 𝕃a ⇒ 𝕃a
set infix right 4 "⸬" ≔ cons

assert λA (l:𝕃A) x y, (cons x (cons y l)) ≡ λA (l:𝕃A) x y, (x⸬(y⸬l))

//Check list.
type 𝕃

//Notation "[ x ]" := (cons x nil)./@TODO 4

//Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
// possible ?

// Eval compute in (cons nat 1 (cons nat (S 1) (nil nat))).
compute (1⸬(succ 1)⸬□)

// Eval compute in (cons bool true (cons bool false (nil bool))).
compute (true⸬false ⸬□)

// Definition id (A:Type) (x:A) := x.
definition id A x:A ≔ x

// Induction principle on lists
symbol list_ind {a} (p:𝕃a⇒Prop) :
  π(p □) ⇒ (∀x l,π(p l) ⇒ π(p(x⸬l))) ⇒ ∀l,π(p l)

/////////////////////////////
// Length of a list
/////////////////////////////
// Fixpoint length (A:Type) (l:list A) :=
//  match l with
//  | nil _ => 0
//  | cons _ _ t => S (length A t)
//  end.
symbol length {a} : 𝕃a ⇒ ℕ
rule length □ → 0
and length (_ ⸬ &l) → succ (length &l)

//Eval compute in (length bool
//   (cons bool true
//         (cons bool false (nil bool)))).
compute length (true⸬false ⸬□)

///////////////////////////////////
// Concatenation of two lists
///////////////////////////////////
//Fixpoint app (A:Type) l1 l2 :=
//  match l1 with
//  | nil _ => l2
//  | cons _ a l => cons A a (app A l l2)
//    end.
symbol app {a} : 𝕃a ⇒ 𝕃a ⇒ 𝕃a
set infix right 5 "⋅" ≔ app
rule     □ ⋅ &m     → &m
 and (&x ⸬ &l) ⋅ &m → &x ⸬ (&l ⋅ &m)

assert a (x y z:𝕃a) ⊢ x⋅y⋅z ≡ x⋅(y⋅z)
assert a x l m ⊢ x⸬l⋅m ≡ x⸬(l⋅m)

// Montrer que le nombre d'éléments de la concaténation de deux listes est
// la somme des nombres des éléments de chacune.

// Lemma equal_length : forall l1 l2,
// (length l1) + (length l2) = length (app l1 l2).
// Proof.
// induction l1.
//  * simpl. reflexivity.
//  * simpl. intro l2. rewrite IHl1. reflexivity.
// Defined.
theorem length_app :
  ∀A (l1 l2 : 𝕃A), π (((length l1)+(length l2)) = (length (l1 ⋅ l2)))
proof
  assume A l1 l2
  apply list_ind
        (λz, ((length z)+(length l2)) = (length (z⋅l2))) _ _ l1
  reflexivity
  assume x l2 IHl1
  simpl rewrite IHl1 reflexivity
qed

//rule length (&l ⋅ &m) → length &l + length &m

// Définir la fonction qui renverse une liste (on utilisera la fonction
// précédente app)
// et  montrer que reverse(reverse l) = l pour tout l, par induction sur l
symbol reverse {A} : 𝕃A ⇒ 𝕃A
rule reverse    □     → □
 and reverse  (&v⸬&q) → (reverse &q)⋅(cons &v □)

// Lemma app_nil : forall l, app l [] = l.
// Proof.
// induction l.
//  + simpl. reflexivity.
//  + simpl. rewrite IHl. reflexivity.
// Defined.
theorem app_nil : ∀A (l:𝕃A), π ((l⋅□) = l)
proof
  assume A l
  refine list_ind (λz, (z⋅□) = z) _ _ _
  // 0. π (app nil nil = nil)
  reflexivity
  // 1. ∀(x:τ A) (l0:τ (list A)),
  // π (app l0 nil = l0) ⇒ π (app (x ⸬ l0) nil = (x ⸬ l0))
  assume x l IHl
  simpl
  rewrite IHl
  reflexivity
qed

//rule &m ⋅ □ → &m

// Lemma app_assoc : forall l1 l2 l3,
// app (app l1 l2) l3 = app l1 (app l2 l3).
// Proof.
// induction l1.
//  + simpl. reflexivity.
//  + simpl. intros l2 l3. rewrite IHl1. reflexivity.
// Defined.
theorem app_assoc :
  ∀A (l1 l2 l3 : 𝕃A), π (((l1⋅l2)⋅l3)=(l1⋅(l2⋅l3)))
proof
  assume A l1 l2 l3
  apply list_ind (λz, ((z⋅l2)⋅l3)=(z⋅(l2⋅l3))) _ _ l1
  // 0. π (app (app nil l2) l3 = app nil (app l2 l3))
  reflexivity
  // 1. ∀(x:τ A) (l:τ (list A)), π (app (app l l2) l3 = app l (app l2 l3)) ⇒
  // π (app (app (x ⸬ l) l2) l3 = app (x ⸬ l) (app l2 l3))
  assume A
  simpl
  assume l IHl
  rewrite IHl reflexivity
qed

//rule (&l ⋅ &m) ⋅ &n → &l ⋅ (&m ⋅ &n)

// Lemma special_case : forall l a, cons a l = app [a] l.
// Proof.
// intro l. simpl. reflexivity.
// Defined.
theorem special_case : ∀A (l:𝕃A) a, π (((a⸬□)⋅l)=(a⸬l))
proof
  assume A l x simpl reflexivity
qed

// Lemma reverse_bis_concat : forall l1 l2,
// reverse_bis (app l1 l2) =
// app (reverse_bis l2) (reverse_bis l1).
// Proof.
// induction l1.
//  + simpl. intro l2. rewrite app_nil. reflexivity.
//  + simpl. intro l2.
//    rewrite IHl1.
//    apply app_assoc.
// Defined.
theorem reverse_concat :
  ∀A (l1 l2:𝕃A), π ((reverse (l1⋅l2)) = ((reverse l2)⋅(reverse l1)))
proof
  assume A l1 l2
  apply list_ind
        (λz, (reverse (z⋅l2)) = ((reverse l2)⋅(reverse z))) _ _ l1
  simpl
  //refine eq_sym (reverse l2) (app (reverse l2) nil)
  rewrite app_nil A (reverse l2) reflexivity

  simpl assume x l2 IHl1 rewrite IHl1
  apply app_assoc A (reverse l2) (reverse l3) (x⸬□)
qed

// Lemma fixpoint_prop_bis : forall l,
// reverse_bis (reverse_bis l) = l.
// Proof.
// induction l.
//  * reflexivity.
//  * rewrite special_case.
//    repeat rewrite reverse_bis_concat.
//    simpl. rewrite IHl. reflexivity.
// Defined.
theorem fixpoint_reverse : ∀A (l:𝕃A), π (reverse (reverse l) = l)
proof
  assume A l
  apply list_ind (λz, reverse (reverse z) = z) _ _
  // 0. π (reverse (reverse nil) = nil)
  reflexivity
  // 1. ∀(x:τ A) (l0:τ (list A)),
  // π (reverse (reverse l0) = l0) ⇒ π (reverse (reverse (x ⸬ l0)) = (x ⸬ l0))
  assume x l0 IHl
  simpl rewrite reverse_concat A //(reverse l0) (cons x nil)
  simpl rewrite IHl reflexivity
qed

/////////////////////////////////
// Membership
/////////////////////////////////
//Variable A : Type.
//
//Inductive mem : A -> list A -> Prop :=
//  mem_head : forall x l, mem x (cons x l)
//| mem_tail : forall x y l,
//   mem x l -> mem x (cons y l).
symbol mem {A} : τ A ⇒ 𝕃A ⇒ Prop
constant symbol mem_head {A} (x:τ A)   (l:𝕃A) : π (mem x (x⸬l))
constant symbol mem_tail {A} (x y:τ A) (l:𝕃A) :
  π ((mem x l) ⊃ (mem x (y⸬l)))

symbol notMemnil {A} : ∀(x:τ A), π (mem x □) ⇒ π (⊥)
//symbol mem_inv
// Check app.
type app

//Print app.

//Lemma app_left : forall l1 l2 x,
//mem x l1 -> mem x (app l1 l2).
//Proof.
//induction l1;intros l2 x Hyp.
// * inversion Hyp.
// * inversion Hyp.
//     - subst. constructor.
//     - simpl. constructor. apply IHl1. assumption.
//Defined.
theorem app_left : ∀A (l1 l2: 𝕃A) (x:τ A), π (mem x l1) ⇒ π (mem x (l1⋅l2))
proof
 assume A
  refine list_ind _ _ _
  // 0. ∀(x:τ (list A)) (x0:τ A), π (mem x0 □) ⇒ π (mem x0 (□ ⋅ x))
  assume x x0 Hmemnil apply false_elim apply notMemnil x0 apply Hmemnil
  // 1. ∀(x:τ A) (l:τ (list A)), (∀(x:τ (list A)) (x0:τ A), π (mem x0 l) ⇒ π (mem x0 (l ⋅ x)))
  //            ⇒ ∀(x0:τ (list A)) (x1:τ A), π (mem x1 (x ⸬ l)) ⇒ π (mem x1 ((x ⸬ l) ⋅ x0))
  assume x l1 IHl1 l2 x2 Hl1
  simpl
qed //@TODO 14 inversion

//Lemma app_or : forall l1 l2 x, mem x (app l1 l2) -> mem x l1 \/ mem x l2.
//Proof.
//induction l1;intros l2 x Hyp.
// * simpl in Hyp. right. assumption.
// * inversion Hyp.
//     - subst. left. constructor.
//     - simpl. apply IHl1 in H1.
//       destruct H1 as [| Hypliste].
//          + left. constructor. assumption.
//          + right. assumption.
//Defined.
theorem app_or : ∀A (l1 l2: 𝕃A) (x:τ A),
π (mem x (l1⋅l2) ⊃ (mem x l1) ∨ (mem x l2))
proof
  assume A l1 l2 x
  apply list_ind (λz, mem x (z⋅l2) ⊃ (mem x z) ∨ (mem x l2)) _ _ l1
  // 0. π (mem x (app nil l2)) ⇒ π (mem x nil ∨ mem x l2)
  simpl assume Hmeml2 apply disj_intro_right refine Hmeml2
//1. ∀(x0:τ A) (l:τ (list A)),
//     (π (mem x (app l l2)) ⇒ π (mem x l ∨ mem x l2))
// ⇒ π (mem x (app (x0 ⸬ l) l2)) ⇒ π (mem x (x0 ⸬ l) ∨ mem x l2)
  assume x0 l Hyp1 Hyp2
  simpl
admit //@TODO 15 inversion
