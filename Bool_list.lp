require open AL_library.Notation
require open AL_library.Bool

// Inductive list_bool : Type :=
// | nilb : list_bool
// | consb : bool -> list_bool -> list_bool.
constant symbol list_bool : Set
definition Lb ≔ τ list_bool
constant symbol nilb  : Lb
constant symbol consb : 𝔹 → Lb → Lb

// symbol listb_ind p
//: π (p nilb) → (Πx l, π (p l) → π (p (consb x l))) → Πl, π (p l)
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
symbol appb : Lb → Lb → Lb
rule appb nilb         $l2 ↪ $l2
 with appb (consb $a $l) $l2 ↪ consb $a (appb $l $l2)

// Check appb.
type appb
