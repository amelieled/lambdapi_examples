require open tests.preuves_Ledein.notation

// Induction principle on B.
symbol bool_ind : ∀ (P:B⇒Prop), π(P true) ⇒ π(P false) ⇒ ∀b, π(P b)
rule bool_ind _ &t _  true  → &t
 and bool_ind _ _  &f false → &f
                              
// Negation
symbol negb : B ⇒ B
rule negb true  → false
 and negb false → true

// Disjunction
symbol orb : B ⇒ B ⇒ B
set infix left 6 "|" ≔ orb
rule true | _  → true
 and _  | true → true
 and false | &b → &b
 and &b | false → &b

// Conjunction
symbol andb : B ⇒ B ⇒ B
rule andb true &b → &b
 and andb &b true → &b
 and andb false _  → false
 and andb _  false → false
