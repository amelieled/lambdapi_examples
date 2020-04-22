require open amelie.Bool
require open amelie.Constructive_logic
require open amelie.Notation

//set declared "<>"
//definition diff a b ≔ ¬(eq a b)
//set infix left 6 <> ≔ diff
// symbol false_elim p : π ⊥ → π p

// Discriminate sur les booléens :
symbol my_P : 𝔹 → Prop
rule my_P true  ↪ ⊤
 with my_P false ↪ ⊥

theorem discr_f_t : π (false = true) → π ⊥
proof
  assume H
  apply eq_ind false true H my_P
  apply I
qed

symbol my_P_2 : 𝔹 → Prop
rule my_P_2 false  ↪ ⊤
 with my_P_2 true ↪ ⊥

theorem discr_t_f : π (true = false) → π ⊥
proof
  assume H
  apply eq_ind true false H my_P_2
  apply I
qed

// Tentatives de concision :
symbol if {a} : 𝔹 → a → a → a
rule if true  $t _  ↪ $t
 with if false _  $f ↪ $f

definition my_second_P ≔ λb, if b ⊤ ⊥

theorem discr_2 : π (false = true) → π ⊥
proof
  assume H
  apply eq_ind false true H my_second_P
  apply I
qed

theorem discr_3 : π (false = true) → π ⊥
proof
  assume H
  refine eq_ind false true H my_second_P I
qed

//definition test ≔ λl r, eq_ind l r ((λx y, π(x=y) x y) l r) my_second_P
theorem discrd:  π (false = true) → π ⊥
proof
  assume H
  //apply test false true H
  //apply I
admit

definition test2 ≔ λl r H, eq_ind l r H my_second_P

//definition p ≔ λl r, 

theorem discrd_2  : π (true = false) → π ⊥
proof
  assume H
  //apply test2 true false H
  //apply I
admit
//constant symbol eq_ind {a} (x y : τ a) : π (x = y) → Πp, π (p y) → π (p x)

symbol testj (x y:𝔹) (H:(λx y, π(x=y))x y) : TYPE
//symbol test2 l r 
type testj true

//definition test ≔(λl r, (λb, if b = r ⊤ ⊥)  l = r)

// Discriminate sur les Nat
require open amelie.Nat
symbol my_P_nat : ℕ → Prop
rule my_P_nat 0  ↪ ⊤
 with my_P_nat (succ _) ↪ ⊥

theorem discr_s_0 : Πn, π (succ n = 0) → π ⊥
proof
  assume n H
  apply eq_ind (succ n) 0 H my_P_nat
  apply I
qed

symbol discr_prop : Set → Prop
                          //rule discr_prop $v






//symbol contradiction : Prop → Prop → π ⊥

// Tentative de généralitsation
symbol eq_left {a} {x:τ a} {y:τ a} (H:π(x=y)) : τ a
                                                //rule eq_left _ _ (π($x=_)) ↪ $x
rule eq_left {_} {$x} {_} _ ↪ $x

theorem erer : Πa (x y: τ a) (H:π(x=y)), π (eq_left H = x)
proof
assume a x y H
  reflexivity
qed

symbol eq_right {a} {x:τ a} {y:τ a} (H:π(x=y)) : τ a
rule eq_right {_} {_} {$y} _ ↪ $y

definition test3 {a} {x:τ a} {y:τ a} (H:π(x=y)) ≔
  eq_ind (eq_left H) (eq_right H) H //my_second_P

theorem discrd_34  : π (false = true) → π ⊥
proof
  assume H
  refine test3 H my_second_P I
  //apply test3 H my_second_P
  //apply I
qed

symbol my_P_H {a} {x:τ a} {y:τ a} (H:π(x=y)) : τ a → Prop
rule my_P_H _ (eq_right _) ↪ ⊤
 with my_P_H _ (eq_left  _) ↪ ⊥
// with my_P_H $h (succ _) ↪ ⊥
// with my_P_H $h zero ↪ ⊤
//constant symbol eq_ind {a} (x y : τ a) : π (x = y) → Πp, π (p y) → π (p x)

//definition my_P_3 ≔ nat_ind _ _ _ _

definition last_test {a} {x:τ a} {y:τ a} (H:π(x=y)) ≔
  eq_ind (eq_left H) (eq_right H) H (my_P_H H)

theorem discr_S_0 : Πn, π (succ n = 0) → π ⊥
proof
  assume n H
  //apply last_test H
  //apply I
admit
