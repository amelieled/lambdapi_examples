// Inspiré de Software_Foundations/lf/Basics.html
require open amelie.notation
require open amelie.Bool
require open amelie.Logic

// Polymorphic list
constant symbol list : Set ⇒ Set
definition L a ≔ τ (list a)
constant symbol nil {a} : L a
constant symbol cons {a} : τ a ⇒ L a ⇒ L a
set infix right 4 "⸬" ≔ cons

symbol app {A} : L A ⇒ L A ⇒ L A
rule app nil &l2        → &l2
 and app (cons &x &l) &l2 → cons &x (app &l &l2)
                                    
// Polymorphic if
symbol if {a} : B ⇒ a ⇒ a ⇒ a
rule if true  &t _  → &t
 and if false _  &f → &f

// Boolean egality
symbol beq : N ⇒ N ⇒ B
rule beq    0     0    → true
 and beq (S &x) (S &y) → beq &x &y
 and beq    0   (S _ ) → false
 and beq (S _ ) 0      → false

// Boolean less-than relation on N                  
symbol ble : N ⇒ N ⇒ B
rule ble 0         0      → true
 and ble 0         (S _ ) → true
 and ble (S &x) (S &y)    → ble &x &y
 and ble (S _ )   0       → false

///////////////////////
// Bags via Lists
///////////////////////

////////////
//  Type
////////////
definition bag ≔ L nat

////////////
//  Count
////////////
symbol count : N ⇒ bag ⇒ N       
rule count _ nil           → 0
 and count &x (cons &y &q) →
  if (beq &x &y) (S (count &x &q)) (count &x &q)

definition my_list ≔ 1 ⸬ 2 ⸬ 3 ⸬ 1 ⸬ 4 ⸬ 1 ⸬ nil

theorem test_count1 : π (count 1 my_list = 3)
proof reflexivity qed

theorem test_count2 : π (count 6 my_list = 0)
proof reflexivity qed

////////////
//  Sum
////////////
definition sum : bag ⇒ bag ⇒ bag ≔ app
                                   
definition list123 ≔ 1⸬2⸬3⸬nil
definition list141 ≔ 1⸬4⸬1⸬nil

theorem test_sum1 : π (count 1 (sum list123 list141) = 3)
proof reflexivity qed

////////////
//  Add
////////////
definition add ≔ cons {nat}

theorem test_add1 : π (count 1 (add 1 list141) = 3)
proof reflexivity qed

theorem test_add2 : π (count 5 (add 1 list141) = 0)
proof reflexivity qed

////////////
//  Member
////////////
symbol member : N ⇒ bag ⇒ B
rule member _ nil → false
 and member &v (cons &y &q) → if (beq &v &y) true (member &v &q)
 
theorem test_member1 : π (member 1 list141 = true)
proof reflexivity qed

theorem test_member2 : π (member 2 list141 = false)
proof reflexivity qed

////////////
//  Remove_one
////////////
symbol remove_one : N ⇒ bag ⇒ bag
rule remove_one _  nil          → nil
 and remove_one &v (cons &y &q) → if (beq &v &y) &q (cons &y (remove_one &v &q))
 
theorem test_remove_one1 : π (count 5 (remove_one 5 (2⸬1⸬5⸬4⸬1⸬nil)) = 0)
proof reflexivity qed

theorem test_remove_one2 : π (count 5 (remove_one 5 (2⸬1⸬4⸬1⸬nil)) = 0)
proof reflexivity qed

theorem test_remove_one3 : π (count 4 (remove_one 5 (2⸬1⸬4⸬5⸬1⸬4⸬nil)) = 2)
proof reflexivity qed

theorem test_remove_one4 : π (count 5 (remove_one 5 (2⸬1⸬5⸬4⸬5⸬1⸬4⸬nil)) = 1)
proof reflexivity qed

////////////
//  Remove_all
////////////
symbol remove_all : N ⇒ bag ⇒ bag
rule remove_all _ nil           → nil
 and remove_all &v (cons &y &q) → if (beq &v &y) (remove_all &v &q) (cons &y (remove_all &v &q)) 

theorem test_remove_all1 : π (count 5 (remove_all 5 (2⸬1⸬5⸬4⸬1⸬nil)) = 0)
proof reflexivity qed

theorem test_remove_all2 : π (count 5 (remove_all 5 (2⸬1⸬4⸬1⸬nil)) = 0)
proof reflexivity qed

theorem test_remove_all3 : π (count 4 (remove_all 5 (2⸬1⸬4⸬5⸬1⸬4⸬nil)) = 2)
proof reflexivity qed

theorem test_remove_all4 : π (count 5 (remove_all 5 (2⸬1⸬5⸬4⸬5⸬1⸬4⸬5⸬1⸬4⸬nil)) = 0)
proof reflexivity qed

////////////
//  Subset
////////////
symbol subset : bag ⇒ bag ⇒ B
rule subset nil _ → true
 and subset (cons &x &q1) &b2 →
               {|and|} (ble (count &x (cons &x &q1)) (count &x &b2)) (subset &q1 (remove_one &x &b2))

theorem test_subset1 : π (subset (1⸬2⸬nil) (2⸬list141) = true)
proof reflexivity qed

theorem test_subset2 : π (subset (1⸬2⸬2⸬nil) (2⸬list141) = false)
proof reflexivity qed
