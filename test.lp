require open amelie.notation
//require open amelie.Logic
                                  
// //////////////////////// Entiers naturels
                  
symbol plus : N ⇒ N ⇒ N
rule plus O      &m → &m
 and plus (S &v) &m → S (plus &v &m)

set infix right 6 "+" ≔ plus
                                  
// //////////////////////// Logique sur les booléens

require open amelie.Logic

// ...

// //////////////////////// Retour sur les entiers naturels

theorem plus_0_n : ∀n, π ((O+n) = n)
proof
  assume n
  refine eq_refl n
qed
