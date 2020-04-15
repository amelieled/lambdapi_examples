require open amelie.Notation
//////////////////////
// Boolean type
//////////////////////
constant symbol bool : Set       // Type of booleans
definition B ≔ τ bool
constant symbol true  : B
constant symbol false : B

// Induction principle on B.
symbol bool_ind : ∀p, π(p true) ⇒ π(p false) ⇒ ∀b, π(p b)
rule bool_ind _ &t _  true  → &t
 and bool_ind _ _  &f false → &f

////////////////////////////////
//  Some operations
////////////////////////////////

// Negation
//Definition not b :=
//  match b with
//  | true => false
//  | false => true
//  end.
symbol neg : B ⇒ B
rule neg true  → false
 and neg false → true

// Disjunction
// Definition or b1 b2 :=
//   match b1 with
//   | true => true
//   | false => b2
//   end.
symbol or : B ⇒ B ⇒ B
set infix left 6 "|" ≔ or
rule true | _  → true
 and _  | true → true
 and false | &b → &b
 and &b | false → &b

// Conjunction
// Definition andb b1 b2 :=
//  match b1 with
//  | true => b2
//  | false => false
//  end.
symbol andb : B ⇒ B ⇒ B
//set infix left 5 "^" ≔ {|and|}
rule andb true  &b    → &b
 and andb &b    true  → &b
 and andb false _     → false
 and andb _     false → false

////////////////////////////////////////////////
//  Some examples of functions definitions
////////////////////////////////////////////////

//Definition apply_neg (f : _ -> _ -> bool) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg (f: _ ⇒ _ ⇒ B) b1 b2 ≔ f (neg b1) (neg b2)

// Check apply_neg.
type apply_neg

// Definition nor := apply_neg andb.
definition nor ≔ apply_neg  andb

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
//Definition apply_neg_gen (A:Type) (f:_->_->A) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg_gen A (f : _ ⇒ _ ⇒ A) b1 b2 ≔
    f (neg b1) (neg b2)

// Definition nor2 := apply_neg_gen bool  andb.
definition nor2 ≔ apply_neg_gen B andb

// Definition apply_neg_gen2 {A:Type} (f:_->_->A) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg_gen2 {A} (f : _ ⇒ _ ⇒ A) b1 b2 ≔
    f (neg b1) (neg b2)

// Definition nor3 := apply_neg_gen2 andb.
definition nor3 ≔ apply_neg_gen2 andb
