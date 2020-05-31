// Inspiré de Software_Foundations/lf/Basics.html
require open amelie.lambdapi_examples.Operations
require open amelie.lambdapi_examples.Polymorphic_list
require open amelie.lambdapi_examples.Nat
require open amelie.lambdapi_examples.Bool
require open amelie.lambdapi_examples.Constructive_logic
require open amelie.lambdapi_examples.Notation

// Polymorphic if
symbol if {a} : 𝔹 → a → a → a
rule if true  $t _  ↪ $t
 with if false _  $f ↪ $f

///////////////////////
// Bags via Lists
///////////////////////

////////////
//  Type
////////////
//definition bag ≔ 𝕃nat
definition bag ≔ τ (list nat)
////////////
//  Count
////////////
symbol count : ℕ → bag → ℕ
rule count _     □    ↪ 0
 with count $x ($y⸬$q) ↪
        if (eqb_nat $x $y) (succ (count $x $q)) (count $x $q)

definition my_list ≔ 1⸬2⸬3⸬1⸬4⸬1⸬□

theorem test_count1 : π (count 1 my_list = 3)
proof reflexivity qed

theorem test_count2 : π (count 6 my_list = 0)
proof reflexivity qed

////////////
//  Sum
////////////
definition sum : bag → bag → bag ≔ app

definition list123 ≔ 1⸬2⸬3⸬□
definition list141 ≔ 1⸬4⸬1⸬□

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
symbol member : ℕ → bag → 𝔹
rule member _ □ ↪ false
 with member $v ($y⸬$q) ↪ if (eqb_nat $v $y) true (member $v $q)

theorem test_member1 : π (member 1 list141 = true)
proof reflexivity qed

theorem test_member2 : π (member 2 list141 = false)
proof reflexivity qed

////////////
//  Remove_one
////////////
symbol remove_one : ℕ → bag → bag
rule remove_one _     □    ↪ □
 with remove_one $v ($y⸬$q) ↪ if (eqb_nat $v $y) $q ($y⸬(remove_one $v $q))

theorem test_remove_one1 : π (count 5 (remove_one 5 (2⸬1⸬5⸬4⸬1⸬□)) = 0)
proof reflexivity qed

theorem test_remove_one2 : π (count 5 (remove_one 5 (2⸬1⸬4⸬1⸬□)) = 0)
proof reflexivity qed

theorem test_remove_one3 : π (count 4 (remove_one 5 (2⸬1⸬4⸬5⸬1⸬4⸬□)) = 2)
proof reflexivity qed

theorem test_remove_one4 : π (count 5 (remove_one 5 (2⸬1⸬5⸬4⸬5⸬1⸬4⸬□)) = 1)
proof reflexivity qed

////////////
//  Remove_all
////////////
symbol remove_all : ℕ → bag → bag
rule remove_all _ □           ↪ □
 with remove_all $v ($y⸬$q) ↪ if (eqb_nat $v $y) (remove_all $v $q) (cons $y (remove_all $v $q)) 

theorem test_remove_all1 : π (count 5 (remove_all 5 (2⸬1⸬5⸬4⸬1⸬□)) = 0)
proof reflexivity qed

theorem test_remove_all2 : π (count 5 (remove_all 5 (2⸬1⸬4⸬1⸬□)) = 0)
proof reflexivity qed

theorem test_remove_all3 : π (count 4 (remove_all 5 (2⸬1⸬4⸬5⸬1⸬4⸬□)) = 2)
proof reflexivity qed

theorem test_remove_all4 : π (count 5 (remove_all 5 (2⸬1⸬5⸬4⸬5⸬1⸬4⸬5⸬1⸬4⸬□)) = 0)
proof reflexivity qed

////////////
//  Subset
////////////
symbol subset : bag → bag → 𝔹
rule subset    □ _       ↪ true
 with subset ($x⸬$q1) $b2 ↪
         andb (leb_nat (count $x ($x⸬$q1)) (count $x $b2))
                       (subset $q1 (remove_one $x $b2))

theorem test_subset1 : π (subset (1⸬2⸬□) (2⸬list141) = true)
proof reflexivity qed

theorem test_subset2 : π (subset (1⸬2⸬2⸬□) (2⸬list141) = false)
proof reflexivity qed
