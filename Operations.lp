require open AL_library.Bool
require open AL_library.Nat

// Boolean equality on N
symbol eqb_nat : ℕ → ℕ → 𝔹
rule eqb_nat     0         0     ↪ true
with eqb_nat (succ $x) (succ $y) ↪ eqb_nat $x $y
with eqb_nat     0     (succ _ ) ↪ false
with eqb_nat (succ _ )     0     ↪ false

// Less or equal than function.
symbol leb_nat : ℕ → ℕ → 𝔹
rule leb_nat     0         0     ↪ true
with leb_nat     0     (succ _)  ↪ true
with leb_nat (succ $m) (succ $n) ↪ leb_nat $m $n
with leb_nat (succ _)      0     ↪ false

// Less than function.
symbol ltb_nat : ℕ → ℕ → 𝔹
rule ltb_nat     0         0     ↪ false
with ltb_nat     0     (succ _)  ↪ true
with ltb_nat (succ $m) (succ $n) ↪ ltb_nat $m $n
with ltb_nat (succ _)      0     ↪ false

// Some examples of functions definitions
// Definition toto (b1 b2 : bool) := 0.
definition toto (_ _ : 𝔹) ≔ 0

// Eval compute in apply_neg_gen  nat toto true false.
compute apply_neg_gen ℕ toto true false
