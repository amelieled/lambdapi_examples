// Inspiré de Software_Foundations/lf/Basics.html
require open amelie.Notation
require open amelie.Bool
require open amelie.Logic
require open amelie.Bool_discriminate

///////////////////////////////////////
// Definitions of type
///////////////////////////////////////

//Inductive rgb : Type :=
//  | red
//  | green
//  | blue.
constant symbol rgb : Set
constant symbol RGB : TYPE
rule τ rgb → RGB
constant symbol red   : RGB
constant symbol green : RGB
constant symbol blue  : RGB

// Induction principle on RGB.
symbol rgb_ind :
     ∀p, π (p red) ⇒ π (p green) ⇒ π (p blue) ⇒ ∀c, π (p c)


//Inductive color : Type :=
//  | black
//  | white
//  | primary (p : rgb).
constant symbol color : Set
constant symbol C : TYPE
rule τ color → C
constant symbol black : C
constant symbol white : C
constant symbol primary : RGB ⇒ C

// Induction principle on C.
symbol color_ind :
     ∀p, π (p black) ⇒ π (p white) ⇒ (∀n, π (p (primary n))) ⇒ ∀c, π (p c)


//////////////////////////////////////////
// Some functions
//////////////////////////////////////////

//Definition monochrome (c : color) : bool :=
//  match c with
//  | black ⇒ true
//  | white ⇒ true
//  | primary q ⇒ false
//  end.
symbol monochrome : C ⇒ 𝔹
rule monochrome black     → true
 and monochrome white     → true
 and monochrome (primary _) → false

//Definition isred (c : color) : bool :=
//  match c with
//  | black ⇒ false
//  | white ⇒ false
//  | primary red ⇒ true
//  | primary _ ⇒ false
//  end.
symbol isred : C ⇒ 𝔹
rule isred black           → false
 and isred white           → false
 and isred (primary red)   → true
 and isred (primary green) → false
 and isred (primary blue)  → false

// Definition isgreen (c : color) : bool :=
//   match c with
//   | black => false
//   | white => false
//   | primary green => true
//   | primary _ => false
//   end.
symbol isgreen : C ⇒ 𝔹
rule isgreen black           → false
 and isgreen white           → false
 and isgreen (primary green) → true
 and isgreen (primary red)   → false
 and isgreen (primary blue)  → false

// Definition isblue (c : color) : bool :=
//   match c with
//   | black => false
//   | white => false
//   | primary blue => true
//   | primary _ => false
//   end.
symbol isblue : C ⇒ 𝔹
rule isblue black           → false
 and isblue white           → false
 and isblue (primary blue)  → true
 and isblue (primary red)   → false
 and isblue (primary green) → false

////////////////////////////////////
// A proof of : forall c, isred c = true \/ isgreen c = true \/ isblue c = true <-> monochrome c = false
////////////////////////////////////

// Theorem my_color_test :
// forall c, isred c = true \/ isgreen c =true \/ isblue c = true
// <-> monochrome c = false.
// Proof.
// split;intro myHyp.
//  * induction c.
//     + destruct myHyp as [Hred|Hgreen_blue].
//         { discriminate Hred. }
//         { destruct Hgreen_blue as [Hgreen|Hblue].
//             - discriminate Hgreen.
//             - discriminate Hblue.
//         }
//     + destruct myHyp as [Hred|Hgreen_blue].
//         { discriminate Hred. }
//         { destruct Hgreen_blue as [Hgreen|Hblue].
//             - discriminate Hgreen.
//             - discriminate Hblue.
//         }
//     + induction p;reflexivity.
//  * induction c.
//     + discriminate myHyp.
//     + discriminate myHyp.
//     + induction p.
//         - left. reflexivity.
//         - right. left.  reflexivity.
//         - right. right. reflexivity.
// Qed.

///////////////////////////
// Right to left (RGB)
///////////////////////////
theorem right_to_left_rgb : ∀n,
π (monochrome (primary n) = false ⊃ isred (primary n) = true ∨ isgreen (primary n) = true ∨ isblue (primary n) = true)
proof
  refine rgb_ind (λz, monochrome (primary z) = false ⊃
                                  isred (primary z) = true ∨ isgreen (primary z) = true ∨ isblue (primary z) = true) _ _ _
  // Goal red
  simpl
  assume Hyp apply disj_intro_left //(true = true) ((false = true) ∨ (false = true))
  reflexivity
  // Goal green
  simpl
  assume Hyp apply disj_intro_right //(false = true) ((true = true) ∨ (false = true))
  apply disj_intro_left // (true = true) (false = true)
  reflexivity
  // Goal blue
  simpl
  assume Hyp apply disj_intro_right //(false = true) ((false = true) ∨ (true = true))
  apply disj_intro_right //(false = true) (true = true)
  reflexivity
qed

///////////////////////////
// Right to left (color)
///////////////////////////
theorem right_to_left_color :
∀c, π ((monochrome c) = false ⊃ (isred c)=true ∨ (isgreen c)=true ∨ (isblue c)=true)
proof
  assume c
  apply color_ind (λz, (monochrome z) = false ⊃ (isred z)=true ∨ (isgreen z)=true ∨ (isblue z)=true) _ _ _ c
  // Goal black
  simpl assume Htruefalse
  apply false_elim apply discr_f_t symmetry apply Htruefalse
  // Goal white
  simpl assume Htruefalse
  apply false_elim apply discr_f_t symmetry apply Htruefalse
  // Goal primary
  assume rgb
  apply right_to_left_rgb rgb
qed

///////////////////////////
// Left to right (RGB)
///////////////////////////
theorem left_to_right_rgb : ∀(n:RGB),
π ((isred (primary n))=true ∨ (isgreen (primary n))=true ∨ (isblue (primary n))=true
        ⊃ (monochrome (primary n))=false)
proof
  assume n
  apply rgb_ind (λz,(isred (primary z))=true ∨ (isgreen (primary z))=true ∨ (isblue (primary z))=true
        ⊃ (monochrome (primary z))=false) _ _ _ n
  simpl assume Hyp reflexivity
  simpl assume Hyp reflexivity
  simpl assume Hyp reflexivity
qed

///////////////////////////
// Left to right (color)
///////////////////////////
theorem left_to_right_color :
∀c, π ((isred c)=true ∨ (isgreen c)=true ∨ (isblue c)=true ⊃ (monochrome c) = false)
proof
  assume c
  apply color_ind (λz, (isred z)=true ∨ (isgreen z)=true ∨ (isblue z)=true ⊃ (monochrome z)=false) _ _ _ c
  // Goal black
  simpl assume Hor
  apply disj_elim (false = true) ((false = true) ∨ (false = true))
     // 0. π ((false = true) ∨ ((false = true) ∨ (false = true)))
     apply Hor
     // 1. π (false = true) ⇒ π (true = false)
     assume Hfalsetrue symmetry apply Hfalsetrue
     // 2. π ((false = true) ∨ (false = true)) ⇒ π (true = false)
     assume Hor2 apply disj_elim (false = true) (false = true) apply Hor2
           assume Hfalsetrue symmetry apply Hfalsetrue
           assume Hfalsetrue symmetry apply Hfalsetrue
  // Goal white
  simpl assume Hor
  apply disj_elim (false = true) ((false = true) ∨ (false = true))
     // 0. π ((false = true) ∨ ((false = true) ∨ (false = true)))
     apply Hor
     // 1. π (false = true) ⇒ π (true = false)
     assume Hfalsetrue symmetry apply Hfalsetrue
     // 2. π ((false = true) ∨ (false = true)) ⇒ π (true = false)
     assume Hor2 apply disj_elim (false = true) (false = true) apply Hor2
           assume Hfalsetrue symmetry apply Hfalsetrue
           assume Hfalsetrue symmetry apply Hfalsetrue
  // Goal primary
  assume rgb
  apply left_to_right_rgb rgb
qed

///////////////////////////////////
// Version ⇔
///////////////////////////////////

theorem my_color_test :
∀c, π ((isred c = true ∨ isgreen c = true ∨ isblue c = true) ⇔ (monochrome c = false))
proof
  assume c
  simpl
  apply conj_intro
  apply left_to_right_color c
  apply right_to_left_color c
qed




/////////////////////////////
// A weak version of the previous theorem
/////////////////////////////

theorem in_red_bis : ∀c, π (imp (eq {bool} (isred c) true) (eq {bool} (monochrome c) false))
proof
  assume c
  refine color_ind (λn, imp (eq {bool} (isred n) true) (eq {bool} (monochrome n) false)) ?CB[c] ?CW[c] ?CP[c] c
  // Goal : π (imp (eq (isred black) true) (eq (monochrome black) false))
  simpl
  assume Hred
  rewrite Hred
  reflexivity
  // Goal : π (imp (eq (isred white) true) (eq (monochrome white) false))
  simpl
  assume Hred
  rewrite Hred
  reflexivity
  // Goal : ∀(n:RGB), π (imp (eq (isred (primary n)) true) (eq (monochrome (primary n)) false))
  refine rgb_ind (λz, imp (eq {bool} (isred (primary z)) true) (eq {bool} (monochrome (primary z)) false)) ?CR[c] ?CG[c] ?CB[c]
  simpl
  assume Hred
  reflexivity
  //
  simpl
  assume Hred
  reflexivity
  //
  simpl
  assume Hred
  reflexivity
qed
