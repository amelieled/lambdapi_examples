// Cours et exercices de la découverte de lambdapi
// Inspiré de la version Coq de Catherine Dubois
// (elle-même inspirée de Software Foundations)

// Tout ce qui est en commentaire est du Coq qui compile.
// Ma traduction vers LP suit.

require open amelie.notation
                                  
////////////////////////////////////
// Avant de prendre la route...
////////////////////////////////////
                                  
// Inductive route : Type :=
// | departementale : route
// | nationale : route
// | autoroute : route.
constant symbol route          : Set
definition R ≔ τ route
constant symbol departementale : R
constant symbol nationale      : R
constant symbol autoroute      : R

// Definition agrandir (r : route) := 
//   match r with
//  | departementale => nationale
//  | nationale => autoroute
//  | autoroute => autoroute
//  end.                        
symbol agrandir : R ⇒ R
rule agrandir departementale → nationale
 and agrandir nationale      → autoroute
 and agrandir autoroute      → autoroute

// Eval compute in (agrandir (agrandir nationale)).
compute agrandir (agrandir nationale)

theorem agrandir_test : // version théorème 
  π (agrandir (agrandir nationale) = autoroute)
proof
  reflexivity
qed

//Inductive terrain : Type :=
//| t_terre : terrain
//| t_route : route -> terrain
//| t_batiment : terrain.
constant symbol terrain    : Set
definition Ter ≔ τ terrain
constant symbol t_terre    : Ter
constant symbol t_route    : R ⇒ Ter
constant symbol t_batiment : Ter

//Check (t_route nationale).
type t_route nationale

/////////////////////////////
// Exercice 1 - De premiers exemples
/////////////////////////////

// ///////////////////////// Booléen

//Check true.
type true

//Print bool.
// ??

//Definition not b :=
//  match b with
//  | true => false
//  | false => true
//  end.
symbol not : B ⇒ B
rule not true → false
 and not false → true

// Definition andb b1 b2 :=
//  match b1 with
//  | true => b2
//  | false => false
//  end.                
symbol andb : B ⇒ B ⇒ B
rule andb false _  → false
 and andb _ false  → false
 and andb &b1 true → &b1
 and andb true &b2 → &b2

// Definition or b1 b2 :=
//   match b1 with
//   | true => true
//   | false => b2
//   end.
symbol or : B ⇒ B ⇒ B
rule or true _  → true
 and or _ true  → true
 and or &b1 false → &b1
 and or false &b2 → &b2

// /////////////////////// Entiers naturels
                  
// Inductive nat : Type :=
// | O : nat
// | S : nat -> nat.
//Cf notation.lp

// Check O.
type O
// Check S. 
type S

//Notation "0" := O.
//Notation "1" := (S O).
//Cf notation.lp
     
//Fixpoint plus n m :=
//  match n with
//  | 0 => m
//  | S n' => S (plus n' m)
//  end.
symbol plus : N ⇒ N ⇒ N

// Notation "n + m" := (plus n m).
set infix right 6 "+" ≔ plus

rule 0 + &m → &m
 and S &v + &m → S (&v + &m)

// Eval compute in (0 + 1).
compute 0+1
                        
// Eval compute in (plus 1 1).
compute plus 1 1

// ///////////////////////////// Liste de booléens

// Inductive list_bool : Type :=
// | nilb : list_bool
// | consb : bool -> list_bool -> list_bool.
constant symbol list_bool : Set
definition Lb ≔ τ list_bool    // équivalent à ce qui a été fait avant o:-)
constant symbol nilb  : Lb
constant symbol consb : B ⇒ Lb ⇒ Lb

// symbol listb_ind p : π (p nilb) ⇒ (∀x l, π (p l) ⇒ π (p (consb x l))) ⇒ ∀l, π (p l) 
                                 
// Check nilb.
type nilb

//Definition example := consb true (consb false (consb true nilb)).
definition example ≔ consb true (consb false (consb true nilb))

//Check example.
type example

// Fixpoint appb l1 l2 :=
//   match l1 with
//   | nilb => l2
//   | consb a l => consb a (appb l l2)
//  end. 
symbol appb : Lb ⇒ Lb ⇒ Lb
rule appb nilb         &l2 → &l2
 and appb (consb &a &l) &l2 → consb &a (appb &l &l2)

// Check appb.
type appb

// ///////////////////////////////////// Suite booléen
     
//Definition apply_neg (f : _ -> _ -> bool) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg (f: _ ⇒ _ ⇒ B) b1 b2 ≔ f (not b1) (not b2)

// Check apply_neg.
type apply_neg

// Definition nor := apply_neg andb.
definition nor ≔ apply_neg andb
                             
// Check nor.
type nor
 
// Definition nor := 
//   apply_neg (fun b1 => fun b2 => b2).
definition nor_lambda ≔ apply_neg (λ_ b2, b2)
 
// Eval compute in (nor true false).
compute nor true false

// Definition idb : bool -> bool := fun b => b.
definition idb : B ⇒ B ≔ λb, b

// identique à
// Definition idb (b : bool) := b.
definition idb_bis b:B ≔ b
                             
//Definition my_first := apply_neg (fun b1 => fun b2 => b1).
definition my_first ≔ apply_neg (λb1 _, b1)
                         
//Eval compute in (my_first true false).
compute (my_first true false)

// ////////////////////////////////// Liste polymorphe

// Inductive list (A:Type) : Type :=
// | nil : list A
// | cons : A -> list A -> list A .

// Traduction de manière stricte :
// constant symbol list : Set ⇒ Set
// definition L a ≔ τ (list a)
// constant symbol nil a : L a
// constant symbol cons a : τ a ⇒ L a ⇒ L a

// Mais j'allège un peu :
constant symbol list : Set ⇒ Set
definition L a ≔ τ (list a)
constant symbol nil {a} : L a
constant symbol cons {a} : τ a ⇒ L a ⇒ L a
set infix right 4 "⸬" ≔ cons
assert λA (l:L A) x y, (cons x (cons y l)) ≡ λA (l:L A) x y, (x⸬(y⸬l))

symbol list_ind {a} p : π(p nil) ⇒ (∀(x:τ a) l, π(p l) ⇒ π( p (x⸬l))) ⇒ ∀l, π(p l)

// Eval compute in (cons nat 1 (cons nat (S 1) (nil nat))).
compute (cons 1 (cons (S 1) nil))

// Eval compute in (cons bool true (cons bool false (nil bool))).
compute (cons true (cons false nil))
					    
// Definition id (A:Type) (x:A) := x.
definition id A x:A ≔ x

// Fixpoint length (A:Type) (l:list A) :=
//  match l with
//  | nil _ => 0
//  | cons _ _ t => S (length A t)
//  end. 
symbol length {A} : L A ⇒ N
rule length nil → 0
 and length (cons _ &t) → S (length &t)
                      
//Eval compute in (length bool 
//   (cons bool true 
//         (cons bool false (nil bool)))).
compute length (cons true (cons false nil))

//Fixpoint app (A:Type) l1 l2 :=
//  match l1 with
//  | nil _ => l2
//  | cons _ a l => cons A a (app A l l2)
//    end. 
symbol app {A} : L A ⇒ L A ⇒ L A
rule app nil &l2        → &l2
 and app (cons &x &l) &l2 → cons &x (app &l &l2)

//Definition apply_neg_gen (A:Type) (f:_->_->A) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg_gen A (f : _ ⇒ _ ⇒ A) b1 b2 ≔
    f (not b1) (not b2)

// Definition nor2 := apply_neg_gen bool  andb.
definition nor2 ≔ apply_neg_gen B andb

// Definition apply_neg_gen2 {A:Type} (f:_->_->A) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg_gen2 {A} (f : _ ⇒ _ ⇒ A) b1 b2 ≔
    f (not b1) (not b2)

// Definition nor3 := apply_neg_gen2 andb.
definition nor3 ≔ apply_neg_gen2 andb

// Definition toto (b1 b2 : bool) := 0. 
definition toto (_ _ : B) ≔ 0

// Eval compute in apply_neg_gen  nat toto true false.
compute apply_neg_gen N toto true false
                                       
// //////////////////////////////////////////// Logique sur les booléens

require open amelie.Logic
definition equiv (p q : Prop) ≔ imp p q ∧ imp q p
set infix left 7 "⇔" ≔ equiv
                       
// Check True. (* True : Prop *)
type true // (* true : B *)                                      

// Check True -> False. (* True -> False : Prop *)
type (imp ⊤ ⊥) // imp ⊤ ⊥ : Prop

type _ ⇒ _ // ?201 ⇒ ?199 : TYPE

// Lemma bool_trivial : forall (P : bool -> Prop) b, P b -> P b.
// Admitted.
theorem bool_trivial : ∀p:B⇒Prop,∀b, π (p b) ⇒ π (p b)
//π (imp (P b) (P b))
proof
  assume P b H
  apply H
qed

// Induction principle on B.
symbol bool_ind : ∀p, π(p true) ⇒ π(p false) ⇒ ∀b, π(p b)

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

// Première preuve

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
//set declared "<>"
//definition diff a b ≔ ¬(eq a b)
//set infix left 6 <> ≔ diff

// symbol false_elim p : π ⊥ ⇒ π p

symbol my_P : B ⇒ Prop
rule my_P true  → ⊤
 and my_P false → ⊥

rule ⊤ → true = true
         
theorem discr : π (false = true) ⇒ π ⊥
proof
  assume H
  apply eq_ind false true H my_P
  reflexivity     
qed

//theorem andb_prop :                        // Il me manque un outil pour y arriver avec cet énoncé
//∀b1 b2, π (eq {bool} (andb b1 b2) true) ⇒
//                    π ((eq {bool} b1 true) ∧ (eq {bool} b2 true))
theorem andb_prop b1 b2 : π (imp (andb b1 b2 = true) ((b1 = true) ∧ (b2 = true)))
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
  apply discr apply H
qed

/////////////////////////////////////
//   Exercice 2 - De premières preuves
/////////////////////////////////////

//   [andb_true_iff : forall b1 b2, andb b1 b2 = true <-> b1 = true /\ b2 = true]
//    Montrer [or_true_iff], un résultat similaire sur [or].  

theorem andb_true_iff b1 b2 : π ((andb b1 b2 = true) ⇔ ((b1 = true) ∧ (b2 = true)))
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
      apply discr apply H
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
      assume Hfalse apply false_elim (b2 = true) apply discr apply Hfalse
      assume H2 apply H2
qed

// //////////////////////////////////////////// Retour sur les entiers naturels

//Lemma plus_0_n : forall n, 0 + n = n.
//Proof.
//intro n. simpl. reflexivity.
//Qed.
theorem plus_0_n : ∀n, π ((plus O n) = n)
proof
  assume n
  reflexivity
qed

// Induction principle
symbol nat_ind p : π (p 0) ⇒ (∀x, π (p x) ⇒ π (p (S x))) ⇒ ∀x, π (p x)

// Injective principle
symbol nat_inj : ∀n m, π ((S n) = (S m)) ⇒ π (n = m)  // A voir !

//Lemma plus_n_0 : forall n, n + O = n.
//Proof.
//induction n.
//+  simpl. reflexivity.
//+ simpl. rewrite IHn. reflexivity.
//Qed.
theorem plus_n_0 : ∀n, π ((plus n O) = n)
proof
  assume n
  refine nat_ind (λz, (plus z O) = z) _ _ _
  // Case n = O
  refine eq_refl O
  // Case = S n'
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity    
qed

//Fixpoint mult (n m : nat) :  nat :=
//  match n with
//  | O => 0
//  | S n' => m + (mult n' m)
//  end.
symbol mult : N ⇒ N ⇒ N
rule mult O _ → 0
 and mult (S &v) &m → plus &m (mult &v &m)

//Notation "n * m" := (mult n m).
set infix left 6 "*" ≔ mult

//Lemma mult_0_n : forall n : nat, 0*n=0.
//Proof.
//intros. simpl. reflexivity.
//Qed.
theorem mult_0_n : ∀n, π ((0*n) = 0)
proof
  assume n
  refine eq_refl O
qed

//Lemma mult_n_0 : forall n, n*0= 0.
//Proof.
//induction n.
//+  apply mult_0_n.
//+  simpl. exact IHn.
// (* ou assumption*)
//Qed.
theorem mult_n_0 : ∀n, π ((n*0) = 0)
proof
  refine nat_ind (λz, (z*0) = 0) _ _
  // Case n = O
  refine eq_refl O
  // Case = S n'
  assume n' Hn'
  simpl
  apply Hn'
qed

//Lemma plus_assoc : forall n m p,
//  n+(m+p) = n+m+p.
//Proof.
//induction n ; intros m p.
//+ simpl. reflexivity. 
//+ simpl. rewrite IHn. reflexivity.
//Qed.
theorem plus_assoc :
//∀(n m p:N), π (eq {nat} (n+(m+p)) (n+m+p))
∀(n m p:N), π ((plus n (plus m p)) = (plus (plus n m) p))
proof
  assume n m p
  //refine nat_ind (λz, eq {nat} (z+(m+p)) (z+m+p)) _ _ n
  refine nat_ind (λz, (plus z (plus m p)) = (plus (plus z m) p)) _ _ n
  reflexivity
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity
qed

//Lemma plus_n_Sm : forall n m,
//  n + S m = S (n + m).
//Proof.
//induction n ; intro m ; simpl.
//+ reflexivity.
//+ rewrite IHn. reflexivity.
//Qed.
theorem plus_n_Sm : ∀n m, π ((plus n (S m)) = (S (plus n m)))
proof
  assume n m
  refine nat_ind (λz, ((plus z (S m)) = (S (plus z m)))) _ _ n
  reflexivity
  simpl
  assume n' Hn'
  rewrite Hn'
  reflexivity
qed

//Lemma plus_comm : forall n m, n+m=m+n.
//Proof.
//induction n ; intros m0.
//+ simpl. rewrite plus_n_0. reflexivity.
//+ simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
//Qed.
theorem plus_comm : ∀n m, π((plus n m) = (plus m n))
proof
  assume n m
  refine nat_ind (λz, ((plus z m) = (plus m z))) _ _ n
    simpl rewrite plus_n_0 reflexivity
    simpl assume n' Hn' rewrite Hn' rewrite plus_n_Sm reflexivity
qed

//Lemma mult_n_Sm : forall n m, n*S m=n+n*m.
//Proof.
//induction n ; intros m0 ; simpl.
//+ reflexivity.
//+ rewrite IHn.
//  do 2 (rewrite plus_assoc).
//  rewrite plus_comm with (n:=n) (m := m0). reflexivity.
//Qed.
//theorem mult_n_Sm : ∀n m, π (eq {nat} (n*S m) (n+n*m))
theorem mult_n_Sm : ∀n m, π ((mult n (S m)) = (plus n (mult n m)))
proof
  assume n m
  refine nat_ind (λz, ((mult z (S m)) = (plus z (mult z m)))) _ _ n
    reflexivity
    assume n' Hn' simpl rewrite Hn'
    rewrite plus_assoc rewrite plus_assoc rewrite plus_comm n' m reflexivity
qed

//Lemma mult_comm : forall n m, n *m=m*n.
//Proof.
//induction n ; intros m0 ; simpl.
//+ rewrite mult_n_0. reflexivity.
//+ rewrite IHn. rewrite mult_n_Sm.  reflexivity.
//Qed.
theorem mult_comm : ∀n m, π ((mult n m) = (mult m n))
proof
  assume n m
  refine nat_ind (λz, ((mult z m) = (mult m z))) _ _ n
    rewrite mult_n_0 reflexivity
    assume n' Hn' simpl rewrite Hn'
    rewrite mult_n_Sm reflexivity
qed

//Lemma mult_plus_distr_r : forall n m p,
//  (n+m)*p = n*p+m*p.
//Proof.
//induction n ; intros m p; simpl.
//+ reflexivity.
//+ rewrite IHn. apply plus_assoc.
//Qed.
theorem mult_plus_distr_r :
∀n m p, π ((mult (plus n m) p) = (plus (mult n p) (mult m p)))
proof
  assume n m p
  refine nat_ind (λz, ((mult (plus z m) p) = (plus (mult z p) (mult m p)))) _ _ n
    reflexivity
    assume n' Hn' simpl rewrite Hn'
    apply plus_assoc p (mult n' p) (mult m p) // pas inféré
qed

//Lemma mult_assoc : forall n m p, n*(m*p) = (n*m)*p.
//Proof.
//induction n ; intros m p; simpl.
//+ reflexivity.
//+ rewrite IHn. rewrite mult_plus_distr_r. reflexivity. 
//Qed.
theorem mult_assoc : ∀ n m p, π ((n*(m*p)) = ((n*m)*p))
proof
  assume n m p
  refine nat_ind (λz, ((z*(m*p)) = ((z*m)*p))) _ _ n
    reflexivity
    simpl assume n' Hn' // simpl
    rewrite Hn'
    rewrite mult_plus_distr_r // m (mult n' m) p
    reflexivity
qed

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
theorem mult_plus_distr_l :
∀n m p, π ((mult n (plus m p)) = (plus (mult n m) (mult n p)))
proof
  assume n m p
  refine nat_ind (λz, (mult z (plus m p)) = (plus (mult z m) (mult z p))) _ _ n
  reflexivity
  simpl assume n' IHn' rewrite IHn'
  rewrite plus_comm p (n'*p)
  symmetry
  //rewrite plus_assoc m (mult n' m) (plus (mult n' p) p)
  //symmetry
  //rewrite plus_comm p (n'*p)
  //symmetry
  //rewrite plus_comm m (plus (mult n' m) (plus (mult n' p) p))
  //rewrite plus_assoc rewrite plus_assoc
  //rewrite plus_comm m p
  //rewrite <- plus_assoc (p + m) (n*m) (n*p)
  //rewrite plus_comm (p + m) (n*m + n*p)
  //rewrite plus_assoc reflexivity
//qed // @TODO_2
admit

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
theorem mult_plus_distr_l_bis : ∀n m p, π ((mult n (plus m p)) = (plus (mult n m) (mult n p)))
proof
  assume n m p
  rewrite mult_comm n m
  rewrite mult_comm n p
  rewrite mult_comm n (plus m p)
  symmetry
  rewrite mult_plus_distr_r
  reflexivity 
qed

////////////////////////////
//  Exercice 3 - Un peu de logique !
////////////////////////////

//Lemma impl_and : forall P Q R : Prop, (P->Q->R) -> (P /\ Q -> R).
//Proof.
//intros P Q R Hyp1 Hyp2.
//destruct Hyp2 as [Hp Hq].
//apply Hyp1 ; assumption.
//Qed.
theorem impl_and : ∀P Q R : Prop, π (imp (imp P (imp Q R)) (imp (P ∧ Q) R))
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
theorem conj_impl : ∀P Q R : Prop, π (imp (imp (P ∧ Q) R) (imp P (imp Q R)))
proof
  assume P Q R Hand HP HQ
  // Goal π (imp (P ∧ Q) R)
  apply Hand
  // Goal  π (P ∧ Q)
  apply conj_intro P Q
    apply HP
    apply HQ
qed
      
//Lemma conj_impl_iff : forall P Q R : Prop, (P /\ Q -> R) <-> (P -> Q -> R).
//Proof.
//split.
//+ apply conj_impl.
//+ apply impl_and.
//Qed.
theorem conj_impl_iff : ∀P Q R : Prop,
π ((imp (P ∧ Q) R) ⇔ (imp P (imp Q R)))  
proof
  assume P Q R
  apply conj_intro
  simpl
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
theorem impl_not : ∀P : Prop, π P ⇒ π (¬ (¬ P))
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
theorem modus_ponens : ∀P Q : Prop, π P ⇒ (π P ⇒ π Q) ⇒ π Q
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
theorem impl_neg_bis : ∀P : Prop, π P ⇒ π (¬ (¬ P))
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
theorem P_notP_contradiction : ∀P : Prop, π (¬(P ∧ ¬P))
proof
  assume P Hand
  //apply neg_intro (P ∧ ¬P)
  // apply neg_elim P
     //apply conj_elim_right P _   apply Hand
     //apply conj_elim_left _ (¬P) apply Hand
admit // @TODO 3 : problème avec les nouvelles règles

//Lemma neg_and : forall P Q : Prop, P \/ Q -> ~(~ P /\ ~Q).
//Proof.
//Admitted.
theorem neg_and : ∀P Q : Prop, π (P ∨ Q) ⇒ π (¬(¬P ∧ ¬Q))
proof
  assume P Q Hor Hand
  refine disj_elim P Q ⊥ _ _ _
  // Case π (P ∨ Q)
  apply Hor
  // Case π P ⇒ π ⊥
  assume HP
      //refine conj_elim_left (¬P) (¬Q) _ apply Hand
      //apply HP
  // Case π Q ⇒ π ⊥
  //assume HQ apply neg_elim Q
     //refine conj_elim_right (¬P) (¬Q) _ apply Hand
     //apply HQ
admit // @TODO 4 probleme avec les nouvelles règles

//Lemma exists_neg_forall : forall P : nat -> Prop, 
//(exists n, P n) ->  ~(forall n,~ (P n)).
//Proof.
//intros P H H1. 
//destruct H as [n0 H0].
//specialize (H1 n0).
//contradiction.
//Qed.
theorem exists_neg_forall : ∀(P : N ⇒ Prop), π(∃P) ⇒ π (¬(forall {nat} (λm:N, ¬ (P m))))
proof
  //assume P H1 H2
//   apply H2
admit
//@TODO 5_probleme de type

////////////////////////
//  Exercice 4 - Retour que les listes polymorphes
////////////////////////

//Check list.
type list

// Notation "[]" := nil. //@TODO 6
// set declared "[]"
// rule [] → nil

//Notation "[ x ]" := (cons x nil).

//Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
// possible ?

//  Montrer que le nombre d'éléments de la concaténation de deux listes est la somme
//  des nombres des éléments de chacune.
     
// Lemma equal_length : forall l1 l2,
// (length l1) + (length l2) = length (app l1 l2).
// Proof.
// induction l1.
//  * simpl. reflexivity.
//  * simpl. intro l2. rewrite IHl1. reflexivity.
// Defined.
theorem sum_length : ∀A (l1 l2 : L A), π ((plus (length l1) (length l2)) = (length (app l1 l2)))
proof
  assume A l1 l2
  apply list_ind (λz, (plus (length z) (length l2)) = (length (app z l2))) _ _ l1
  reflexivity
  assume x l2 IHl1
  simpl apply eq_sym {nat} //symmetry rewrite IHl1
admit //@TODO 7 problem

// Définir la fonction qui renverse une liste (on utilisera la fonction précédente app)
// et  montrer que reverse(reverse l) = l pour tout l, par induction sur l
symbol reverse {A} : L A ⇒ L A
rule reverse nil          → nil
 and reverse (cons &v &q) → app (reverse &q) (cons &v nil)

// Lemma app_nil : forall l, app l [] = l.
// Proof.
// induction l.
//  + simpl. reflexivity.
//  + simpl. rewrite IHl. reflexivity.
// Defined.
theorem app_nil : ∀A (l:L A), π (app l nil = l)
proof
  assume A l
  apply list_ind (λz, app z nil = z) _ _
  // 0. π (app nil nil = nil)
  reflexivity
  // 1. ∀(x:τ A) (l0:τ (list A)), π (app l0 nil = l0) ⇒ π (app (x ⸬ l0) nil = (x ⸬ l0))
  assume x l IHl
  simpl
  // rewrite IHl
  // reflexivity
admit // problem

// Lemma app_assoc : forall l1 l2 l3,
// app (app l1 l2) l3 = app l1 (app l2 l3).
// Proof.
// induction l1.
//  + simpl. reflexivity.
//  + simpl. intros l2 l3. rewrite IHl1. reflexivity.
// Defined.
theorem app_assoc : ∀A (l1 l2 l3 : L A), π (app (app l1 l2) l3 = app l1 (app l2 l3))
proof
  assume A l1 l2 l3
  apply list_ind (λz, app (app z l2) l3 = app z (app l2 l3)) _ _ l1
  // 0. π (app (app nil l2) l3 = app nil (app l2 l3))
  reflexivity
  // 1. ∀(x:τ A) (l:τ (list A)), π (app (app l l2) l3 = app l (app l2 l3)) ⇒
                                          // π (app (app (x ⸬ l) l2) l3 = app (x ⸬ l) (app l2 l3))
  assume A
  simpl
  //assume l IHl
  //rewrite IHl // reflexivity
//qed
admit

// Lemma special_case : forall l a, cons a l = app [a] l.
// Proof.
// intro l. simpl. reflexivity.
// Defined.
theorem special_case : ∀A (l:L A) a, π (cons a l = app (cons a nil) l)
proof
  assume A l x simpl
  //refine eq_refl (list A) (cons x l) // Cannot apply reflexivity
admit

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
theorem reverse_concat : ∀A (l1 l2:L A), π (reverse (app l1 l2) = app (reverse l2) (reverse l1))
proof
  assume A l1 l2
  apply list_ind (λz, reverse (app z l2) = app (reverse l2) (reverse z)) _ _ l1
  simpl
  // refine eq_sym (reverse l2) (app (reverse l2) nil)
  // rewrite app_nil A (reverse l2) reflexivity
  // simpl assume l2 rewrite IHl1 apply app_assoc
admit // problem

// Lemma fixpoint_prop_bis : forall l, 
// reverse_bis (reverse_bis l) = l.
// Proof.
// induction l.
//  * reflexivity.
//  * rewrite special_case.
//    repeat rewrite reverse_bis_concat.
//    simpl. rewrite IHl. reflexivity.
// Defined.
                                                
theorem fixpoint_reverse : ∀A (l:L A), π (reverse (reverse l) = l)
proof
admit//@TODO 8

//////////////////////////
//  Exercice 5 - Prédicat inductif
//////////////////////////

//Definition is_even n := exists p, n = 2 * p.
definition is_even n ≔ ∃(λp, n = (mult 2 p))

//Lemma zero_is_even : is_even 0.
//Proof.
//unfold is_even.
//exists 0. simpl. reflexivity.
//Defined.
theorem zero_is_even : π (is_even 0)
proof
  apply ex_intro (λp, O = mult (S (S O)) p) 0
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
theorem is_even_plus : ∀n p, π (is_even n) ⇒ π (is_even p) ⇒ π (is_even (plus n p))
proof
  assume n p Hn Hp
  apply ex_elim (λp, n = mult (S (S O)) p)   apply Hn assume x Hx
  apply ex_elim (λp0, p = mult (S (S O)) p0) apply Hp assume y Hy
  apply ex_intro (λp0, plus n p = mult (S (S O)) p0) (plus x y)
  rewrite mult_plus_distr_l
  rewrite  Hx rewrite Hy reflexivity
qed

// On rappelle la définition de [even] sous forme d'un prédicat inductif.

//Inductive even : nat -> Prop :=
//| even_0 : even 0
//| even_SS : forall n, even n -> even (S (S n)).
symbol even : N ⇒ Prop
constant symbol even_0 : π (even 0)
constant symbol even_SS n : π (imp (even n) (even (S (S n))))

constant symbol even_0_coq : π (even 0)
constant symbol even_SS_coq n : π (even n) ⇒ π (even (S (S n)))

//Lemma even_4 : even 4.
//Proof.
//apply even_SS. apply even_SS. apply even_0.
//Qed.
// theorem even_4 : π (even 4)
// proof
//   apply imp_elim (even  (S (S O))) apply even_SS (S (S O))
//   apply imp_elim (even  O) apply even_SS O
//   apply even_0
// qed
theorem even_4_coq : π (even 4)
proof
  apply even_SS_coq (S (S O)) apply even_SS_coq O apply even_0
qed

//                             ou avec une syntaxe fonctionnelle
//Theorem even_4' : even 4.
//Proof. exact (even_SS 2 (even_SS 0 even_0)).
//Qed.
theorem even_4' : π (even 4)
proof
  apply (even_SS_coq (S (S O)) (even_SS_coq O even_0))
qed

//Theorem even_plus4 : forall n, even n -> even (4 + n).
//Proof.
//  intros n. simpl. intros Hn.
//  apply even_SS. apply even_SS. assumption.
//Qed.
//theorem even_plus4 : π (all (λn:N) (imp (even n) (even (plus 4 n))))
theorem even_plus4 : ∀n, π (imp (even n) (even (plus 4 n)))
proof
  assume n Heven
  apply even_SS_coq (S (S n))
  apply even_SS_coq n
  apply Heven
qed

symbol even_inject : ∀n, (π (n = 0) ⇒ π (even 0)) ⇒ (π (∃(λp,n = S (S p) ⊃ even p ⊃ even (S (S p)))) ⇒ π (even n))
symbol even_inj : ∀n,  π (even n) ⇒ (π (n = 0) ⇒ π (even 0)) ⇒ (π (∃(λp,n = S (S p) ⊃ even p ⊃ even (S (S p)))))
//Theorem ev_minus2 : forall n,
//  even n -> even (pred (pred n)).
//Proof.
//  intros n H.
//  inversion H  as [| p Hp].
//  - (* H = even_0 *) simpl. apply even_0.
//  - (* H = even_SS p Hp *) simpl. exact Hp (* ou assumption*).
//Qed.
symbol pred : N ⇒ N
rule pred 0      → 0
 and pred (S &n) → &n
                   
theorem ev_minus2 : ∀n, π (imp (even n) (even (pred (pred n))))
proof
  assume n Heven
  apply even_inj
  //apply nat_ind (λz, imp (even z) (even (pred (pred z)))) _ _ n
  //simpl assume Heven0 apply even_0_coq                             
  //simpl assume x Himpl HevenSx //assume n assume Heven
                                  
qed//@TODO 9

//Theorem even5_nonsense :
//  even 5 -> 2 + 2 = 9.
//Proof.
//  intro H.
//  inversion H. 
//  inversion H1.
//  inversion H3.
//Qed.
theorem even5_nonsense : π (even 5) ⇒ π ((plus 2 2) = 9)
proof
admit //@TODO 10

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
//    rewrite Hk'. exists (S k'). simpl.
//    Search plus.
//    rewrite <- plus_n_Sm.
//    replace (k' + 0) with k'. reflexivity.
//    apply plus_n_O.
//Qed.
theorem ev_even : ∀n, π (even n) ⇒ π (∃(λk, n = 2*k))
proof
admit //@TODO 11

//  Prouver les lemmes suivants.

//Lemma even_n_disj_Sn : forall n, even n \/ even (S n).
//Proof.
//Admitted.
theorem even_n_disj_Sn : ∀n, π (even n ∨ even (S n))
proof
admit //@TODO 12

//Lemma even_n_neg_Sn : forall n, even n -> ~ even (S n).
//Proof.
//Admitted.
theorem even_n_neg_Sn : ∀n, π (even n) ⇒ π (¬ (even (S n)))
proof
admit //@TODO 13

//Lemma even_dec : forall n, even n \/ ~ even n.
//Proof.
//Admitted.
theorem even_dec : ∀n, π (even n ∨ ¬(even (S n)))
proof
admit //@TODO 14

//  Induction de 2 en 2.
//Lemma two_steps_induction : forall P : nat -> Prop, P 0 -> P 1 ->
//  (forall n, P n -> P (S (S n))) ->
//  forall n, P n.
//Proof.
//  intros P H0 H1 IHn.
//  assert (forall n, P n /\ P (S n)) as Hn.
//Admitted.
theorem two_steps_induction :
∀(p : N ⇒ Prop), π(p 0) ⇒ π(p 1) ⇒ π (forall (λn, p n ⊃ p (S (S n)))) ⇒ π (forall (λn, p n))
proof
admit //@TODO 15

// Définir [evenb : nat -> bool] qui teste si un entier est pair.

//Fixpoint evenb (n:nat) : bool.
//Admitted.
symbol evenb : N ⇒ B//@TODO 16

//    Prouver les lemmes suivants. Si vous avez besoin de résultats sur les
//    booléens, vous pouvez les trouver dans [Bool]
//    (utiliser [Require Import Bool.]).

//Lemma evenb_correct : forall n, evenb n = true -> even n.
//Proof.
//Admitted.
theorem evenb_correct : ∀n, π (evenb n = true) ⇒ π (even n)
proof
admit //@TODO 17

//Lemma evenb_complete : forall n, even n -> evenb n = true.
//Proof.
//Admitted.
theorem evenb_complte : ∀n, π (even n) ⇒  π (evenb n = true)
proof
admit //@TODO 18
                   
//Definition evenb_spec : forall n, evenb n = true <-> even n.
//Proof.
//Admitted.
theorem evenb_spec : ∀n, π (evenb n = true ⇔ even n)
proof
admit //@TODO 19

// Prouver [even_dec_bis : forall n, even n \/ ~ even n] en utilisant [evenb_spec].

//Lemma even_dec_bis : forall n, even n \/ ~ even n.
//Proof.
//Admitted.
theorem even_dec_bis : ∀n, π (even n ∨ ¬(even n))
proof
admit //@TODO 20

/////////////////////////////////
// Exercice 6 - Dernier retour sur les listes
/////////////////////////////////

//Variable A : Type.
//
//Inductive mem : A -> list A -> Prop :=             //@TODO 21
//  mem_head : forall x l, mem x (cons x l)
//| mem_tail : forall x y l, 
//   mem x l -> mem x (cons y l).
symbol mem {A} : τ A ⇒ L A ⇒ Prop
constant symbol mem_head (x:τ _) l   : π (mem x (cons x l))
constant symbol mem_tail x y l : π (imp (mem x l) (mem x (cons y l))) 
// constant symbol list : Set ⇒ Set
// definition L a ≔ τ (list a)
// constant symbol nil {a} : L a
// constant symbol cons {a} : τ a ⇒ L a ⇒ L a

// Check app.
type app
     
//Print app.

//Lemma app_left : forall l1 l2 x,
//mem x l1 -> mem x (app l1 l2).
//Proof.
//Admitted.
theorem app_left : ∀l1 l2 x, π ((mem x l1) (mem x (app l1 l2)))
proof
admit //@TODO 22

//Lemma app_or : forall l1 l2 x, mem x (app l1 l2) -> mem x l1 \/ mem x l2.
//Proof.
//Admitted.
theorem app_or : ∀l1 l2 x, π ((mem x (app l1 l2)) ((mem x l1) ∨ (mem x l2)))
proof
admit //@TODO 23
