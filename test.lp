require open amelie.Notation
//require open amelie.Logic

// Type of natural numbers
constant symbol nat : Set  // Type of natural numbers
set declared "ℕ"
definition ℕ ≔ τ nat
constant symbol zero : ℕ
constant symbol succ : ℕ ⇒ ℕ

// Enabling builtin natural number literals
set builtin "0"  ≔ zero
set builtin "+1" ≔ succ
// //////////////////////// Entiers naturels
symbol plus : ℕ ⇒ ℕ ⇒ ℕ
rule plus zero      &m → &m
 and plus (succ &v) &m → succ (plus &v &m)

set infix right 6 "+" ≔ plus

// //////////////////////// Logique sur les booléens

require open amelie.Logic

// ...

// //////////////////////// Retour sur les entiers naturels

theorem plus_0_n : ∀n, π ((0+n) = n)
proof
  assume n
  refine eq_refl n
qed
