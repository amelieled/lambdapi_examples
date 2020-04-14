require open amelie.notation

// Conjunction
constant symbol conj : Prop ⇒ Prop ⇒ Prop
set infix right 7 "∧" ≔ conj
constant symbol conj_intro p q : π p ⇒ π q ⇒ π (p ∧ q)
symbol conj_elim_left  p q : π (p ∧ q) ⇒ π p
symbol conj_elim_right p q : π (p ∧ q) ⇒ π q
//and_ind : ∀ A B P:Prop, (A→B→P)→A∧B→P
// assert p q r ⊢ p ∧ q ∧ r ≡ p ∧ (q ∧ r)

// Disjunction
constant symbol disj : Prop ⇒ Prop ⇒ Prop
set infix right 6 "∨" ≔ disj
constant symbol disj_intro_left  p q : π p ⇒ π (p ∨ q)
constant symbol disj_intro_right p q : π q ⇒ π (p ∨ q)
symbol disj_elim p q r : π (p ∨ q) ⇒ (π p ⇒ π r) ⇒ (π q ⇒ π r) ⇒ π r

// assert p q r ⊢ p ∨ q ∧ r ≡ p ∨ (q ∧ r) // check that propositions are parsed correctly
  
// False
set declared "⊥"
constant symbol ⊥ : Prop
symbol false_elim p : π ⊥ ⇒ π p

// True
set declared "⊤"
symbol ⊤ : Prop
symbol I : π (⊤)

// Negation
set declared "¬"
constant symbol ¬ : Prop ⇒ Prop
constant symbol neg_intro p : (π p ⇒ π ⊥) ⇒ π (¬p)
symbol neg_elim  p : π (¬ p) ⇒ π p ⇒ π ⊥
rule π (¬ &p) → π &p ⇒ π ⊥

// assert p q ⊢ ¬ p ∧ q ≡ (¬ p) ∧ q

// Intro and Elimination of imp
constant symbol imp : Prop ⇒ Prop ⇒ Prop
set infix right 5 "⊃" ≔ imp
//constant symbol imp_intro p q : (π p ⇒ π q) ⇒ π (imp p q)
//symbol imp_elim  p q : π (imp p q) ⇒ π p ⇒ π q
rule π (&p ⊃ &q) → π &p ⇒ π &q

// assert p q r s ⊢ p ∧ q ⊃ r ∨ s ≡ (p ∧ q) ⊃ (r ∨ s)

// assert a (x y : τ a) ⊢ x = y ∧ x = y ⊃ x = y ∨ x = y ≡ (x = y ∧ x = y) ⊃ (x = y ∨ x = y)

// Universal quantification
constant symbol forall {a} : (τ a ⇒ Prop) ⇒ Prop
rule π (forall &f) → ∀x, π (&f x)

// Existential quantification
set declared "∃"
constant symbol ∃ {a} : (τ a ⇒ Prop) ⇒ Prop
constant symbol ex_intro {a} p (x:τ a) : π (p x) ⇒ π (∃ p)
symbol ex_elim {a} p q : π (∃ p) ⇒ (∀x:τ a, π (p x) ⇒ π q) ⇒ π q

// Set builtins for the rewrite tactic
set builtin "all"   ≔ forall
set builtin "bot"   ≔ ⊥
set builtin "top"   ≔ ⊤
set builtin "imp"   ≔ imp
set builtin "and"   ≔ conj
set builtin "or"    ≔ disj
set builtin "not"   ≔ ¬
