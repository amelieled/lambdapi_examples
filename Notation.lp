// General notations

// Proposition type
constant symbol Prop : TYPE      // Type of propositions
set declared "π"
injective symbol π : Prop → TYPE // Interpretation of propositions in TYPE

// Set type
constant symbol Set : TYPE       // Type of set codes
set declared "τ"
injective symbol τ : Set → TYPE  // Interpretation of set codes in TYPE

// Leibniz equality
constant symbol eq {a} : τ a → τ a → Prop
set infix 8 "=" ≔ eq
constant symbol eq_refl {a} (x : τ a) : π (x = x)
constant symbol eq_ind {a} (x y : τ a) : π (x = y) → Πp, π (p y) → π (p x)

// Set builtins for the rewrite tactic
set builtin "P"     ≔ π
set builtin "T"     ≔ τ
set builtin "eq"    ≔ eq
set builtin "refl"  ≔ eq_refl
set builtin "eqind" ≔ eq_ind

// Properties of Leibniz equality
theorem eq_sym {a} (x y:τ a) : π (x=y) → π (y=x)
proof
  assume a x y xy
  symmetry
  apply xy
qed

// constant symbol pi   : Π (a : U), (T a → U) → U ??
// rule T (pi $a $f) → Π (x : T $a), T ($f x)      ??
