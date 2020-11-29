require open AL_library.Notation

//////////////////////
// Boolean type
//////////////////////
constant symbol bool : Set       // Type of booleans
set declared "𝔹"
definition 𝔹 ≔ τ bool
constant symbol true  : 𝔹
constant symbol false : 𝔹

// Induction principle on B.
symbol bool_ind : Πp, π(p true) → π(p false) → Πb, π(p b)
rule bool_ind _ $t _  true  ↪ $t
with bool_ind _ _  $f false ↪ $f

////////////////////////////////
//  Some operations
////////////////////////////////

// Negation
//Definition not b :=
//  match b with
//  | true => false
//  | false => true
//  end.
symbol neg : 𝔹 → 𝔹
rule neg true  ↪ false
with neg false ↪ true

// Disjunction
// Definition or b1 b2 :=
//   match b1 with
//   | true => true
//   | false => b2
//   end.
symbol orb : 𝔹 → 𝔹 → 𝔹
set infix left 6 "|" ≔ orb
rule true | _  ↪ true
with _  | true ↪ true
with false | $b ↪ $b
with $b | false ↪ $b

// Conjunction
// Definition andb b1 b2 :=
//  match b1 with
//  | true => b2
//  | false => false
//  end.
symbol andb : 𝔹 → 𝔹 → 𝔹
set infix left 7 "&" ≔ andb
rule true  & $b    ↪ $b
with $b    & true  ↪ $b
with false & _     ↪ false
with _     & false ↪ false

////////////////////////////////////////////////
//  Some examples of functions definitions
////////////////////////////////////////////////

//Definition apply_neg (f : _ -> _ -> bool) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg (f: _ → _ → 𝔹) b1 b2 ≔ f (neg b1) (neg b2)

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
definition idb : 𝔹 → 𝔹 ≔ λb, b

// identique à
// Definition idb (b : bool) := b.
definition idb_bis b:𝔹 ≔ b

//Definition my_first := apply_neg (fun b1 => fun b2 => b1).
definition my_first ≔ apply_neg (λb1 _, b1)

//Eval compute in (my_first true false).
compute (my_first true false)

//Definition apply_neg_gen (A:Type) (f:_->_->A) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg_gen A (f : _ → _ → A) b1 b2 ≔
    f (neg b1) (neg b2)

// Definition nor2 := apply_neg_gen bool  andb.
definition nor2 ≔ apply_neg_gen 𝔹 andb

// Definition apply_neg_gen2 {A:Type} (f:_->_->A) b1 b2 :=
//  f (not b1) (not b2).
definition apply_neg_gen2 {A} (f : _ → _ → A) b1 b2 ≔
    f (neg b1) (neg b2)

// Definition nor3 := apply_neg_gen2 andb.
definition nor3 ≔ apply_neg_gen2 andb
