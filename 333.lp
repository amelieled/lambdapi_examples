require open amelie.Notation
//require open amelie.small

// //////////////////////// Entiers naturels
/////////////////////////////////////////////
constant symbol nat : Set
set declared "ℕ"
definition ℕ ≔ τ nat
constant symbol zero : ℕ
constant symbol succ : ℕ ⇒ ℕ

// Enabling builtin natural number literals
set builtin "0"  ≔ zero
set builtin "+1" ≔ succ

///////////////////////////////
// Addition
///////////////////////////////
symbol plus : ℕ ⇒ ℕ ⇒ ℕ
set infix left 6 "+" ≔ plus
assert λx y z,x+y+z ≡ λx y z,(x+y)+z // check that x+y=z is parsed correctly
rule       0 + &y → &y
 and succ &x + &y → succ (&x + &y)

// //////////////////////// Logique sur les booléens

//require open amelie.small

// ...

// //////////////////////// Retour sur les entiers naturels

theorem plus_0_n : ∀n, π ((0+n) = n)
proof
  assume n
  refine eq_refl n
qed
