// Inspiré de Software_Foundations/lf/Basics.html
require open tests.preuves_Ledein.notation
require open tests.preuves_Ledein.Bool
require open tests.preuves_Ledein.Logic

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
   ∀ (P:RGB⇒Prop), π (P red) ⇒ π (P green) ⇒ π (P blue) ⇒ ∀rgb:RGB, π (P rgb)


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
symbol color_ind : ∀ (P:C⇒Prop), π (P black) ⇒ π (P white) ⇒ (∀n, π (P (primary n))) ⇒ ∀c:C, π (P c)


//////////////////////////////////////////
// Some functions         
//////////////////////////////////////////

//Definition monochrome (c : color) : bool :=
//  match c with
//  | black ⇒ true
//  | white ⇒ true
//  | primary q ⇒ false
//  end.
symbol monochrome : C ⇒ B

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
symbol isred : C ⇒ B

rule isred black       → false
 and isred white       → false
 and isred (primary red) → true
 and isred (primary _  ) → false

// Definition isgreen (c : color) : bool :=
//   match c with
//   | black => false
//   | white => false
//   | primary green => true
//   | primary _ => false
//   end.
symbol isgreen : C ⇒ B

rule isgreen black       → false
 and isgreen white       → false
 and isgreen (primary green) → true
 and isgreen (primary _  ) → false
                           
// Definition isblue (c : color) : bool :=
//   match c with
//   | black => false
//   | white => false
//   | primary blue => true
//   | primary _ => false
//   end.
symbol isblue : C ⇒ B

rule isblue black       → false
 and isblue white       → false
 and isblue (primary blue) → true
 and isblue (primary _  ) → false


////////////////////////////////////
// Some properties
////////////////////////////////////

theorem left_rgb : ∀(n:RGB),
π (imp (eq {bool} (monochrome (primary n)) false)
       ((eq {bool} (isred (primary n)) true ∨ eq {bool} (isgreen (primary n)) true) ∨ eq {bool} (isblue (primary n)) true))
proof
  assume c
  refine rgb_ind (λz, imp (eq {bool} (monochrome (primary z)) false)
    ((eq {bool} (isred (primary z)) true ∨ eq {bool} (isgreen (primary z)) true) ∨ eq {bool} (isblue (primary z)) true)) _ _ _ c
  // Goal red
  simpl
qed

theorem in_red_rgb : ∀z, π (imp (eq {bool} (isred (primary z)) true) (eq {bool} (monochrome (primary z)) false))
proof
  refine rgb_ind (λz, imp (eq {bool} (isred (primary z)) true) (eq {bool} (monochrome (primary z)) false)) ?CR ?CG ?CB
  apply imp_intro
  simpl
  assume Hred
  reflexivity   
  //
  apply imp_intro
  simpl
  assume Hred
  reflexivity   
  //
  apply imp_intro
  simpl
  assume Hred
  reflexivity   
qed

// theorem in_red :
//    ∀c, π (eq {bool} (isred c) true) ⇒ π (eq {bool} (monochrome c) false)
// proof
//  assume c Hred
//  // symbol color_ind : ∀ (P:C⇒Prop), π (P black) ⇒ π (P white) ⇒ (∀n, π (P (primary n))) ⇒ ∀c:C, π (P c)
//   refine color_ind (λn, eq {bool} (monochrome n) false) ?CB[c, Hred] ?CW[c, Hred] ?CP[c, Hred] c
//   // Goal : π (eq (monochrome black) false)
//   // Goal : π (eq (monochrome white) false)
//   // Goal : ∀(n:RGB), π (eq (monochrome (primary n)) false)
                                                                                 
// admit

theorem in_red_bis : ∀c, π (imp (eq {bool} (isred c) true) (eq {bool} (monochrome c) false))
proof
  assume c
  refine color_ind (λn, imp (eq {bool} (isred n) true) (eq {bool} (monochrome n) false)) ?CB[c] ?CW[c] ?CP[c] c
  // Goal : π (imp (eq (isred black) true) (eq (monochrome black) false))
  apply imp_intro
  simpl
  assume Hred
  rewrite Hred
  reflexivity
  // Goal : π (imp (eq (isred white) true) (eq (monochrome white) false))
  apply imp_intro
  simpl
  assume Hred
  rewrite Hred
  reflexivity
  // Goal : ∀(n:RGB), π (imp (eq (isred (primary n)) true) (eq (monochrome (primary n)) false))
  refine rgb_ind (λz, imp (eq {bool} (isred (primary z)) true) (eq {bool} (monochrome (primary z)) false)) ?CR[c] ?CG[c] ?CB[c]
  apply imp_intro
  simpl
  assume Hred
  reflexivity   
  //
  apply imp_intro
  simpl
  assume Hred
  reflexivity   
  //
  apply imp_intro
  simpl
  assume Hred
  reflexivity       
qed

// theorem out_red :
// ∀ P, π (eq bool (monochrome p) (true)) ⇒ π (eq bool (isred P) false)
// proof
//  assume p Hmono
//  refine color_ind (λx, eq bool (isred x) false) ?CB[p] ?CW[p] ?CR[p] ?CG[p] ?CB[p] p
// admit

// theorem equiv_red : ∀p,
// P ({|and|} (imp (eq bool (monochrome p) true) (eq bool (isred p) false))
//            (imp (eq bool (isred p) true) (eq bool (monochrome p) false)))


// theorem my_color_test : π (all (λc:C, ((isred c) = true ∨ (isgreen c) =true ∨ (isblue c) = true) ⇔ (monochrome c = false)))
// proof
// qed

definition equiv (A B : Prop) ≔ (imp A B) ∧ (imp B A)
set infix left 7 "⇔" ≔ equiv


theorem left :
∀c, π (imp (eq {bool} (monochrome c) false) ((eq {bool} (isred c) true ∨ eq {bool} (isgreen c) true) ∨ eq {bool} (isblue c) true))
proof
  assume c
  apply color_ind (λz, imp (eq {bool} (monochrome z) false) ((eq {bool} (isred z) true ∨ eq {bool} (isgreen z) true) ∨ eq {bool} (isblue z) true)) _ _ _ c
  // Goal black
  simpl apply imp_intro assume Htruefalse
  apply or_intro_right (eq {bool} false true ∨ eq {bool} false true) (eq {bool} false true) symmetry apply Htruefalse
  // Goal white
  simpl apply imp_intro assume Htruefalse
  apply or_intro_right (eq {bool} false true ∨ eq {bool} false true) (eq {bool} false true) symmetry apply Htruefalse               // Goal primary
  
                                                                                                                                  
qed

theorem right_rgb : ∀(n:RGB),
π (imp ((eq {bool} (isred (primary n)) true ∨ eq {bool} (isgreen (primary n)) true) ∨ eq {bool} (isblue (primary n)) true)
        (eq {bool} (monochrome (primary n)) false))
proof
  assume n
  apply rgb_ind (λz, (imp ((eq {bool} (isred (primary z)) true ∨ eq {bool} (isgreen (primary z)) true) ∨ eq {bool} (isblue (primary z)) true) (eq {bool} (monochrome (primary z)) false))) _ _ _ n
  simpl apply imp_intro assume Hyp reflexivity
  simpl apply imp_intro assume Hyp reflexivity
  simpl apply imp_intro assume Hyp reflexivity
qed

theorem my_color_test :
∀c, π (((eq {bool} (isred c) true) ∨ (eq {bool} (isgreen c) true) ∨ (eq {bool} (isblue c)  true))
              ⇔ (eq {bool} (monochrome c) false))
proof
  assume c
  apply and_intro
  apply color_ind (λz, imp ((eq {bool} (isred z) true ∨ eq {bool} (isgreen z) true) ∨ eq {bool} (isblue z) true) (eq {bool} (monochrome z) false)) _ _ _ c
  // Goal black
  simpl
  apply imp_intro
  assume Hor
  apply or_elim (eq {bool} false true ∨ eq {bool} false true) (eq {bool} false true)
  // Goal π ((eq false true ∨ eq false true) ∨ eq false true)
  apply Hor
  // π (eq false true ∨ eq false true) ⇒ π (eq true false)
  assume Hor2
  apply or_elim (eq {bool} false true) (eq {bool} false true)
     apply Hor2
     assume Hfalsetrue rewrite Hfalsetrue reflexivity
     assume Hfalsetrue rewrite Hfalsetrue reflexivity     
  // π (eq false true) ⇒ π (eq true false)
  assume Hfalsetrue rewrite Hfalsetrue reflexivity

  // Goal white
  simpl
  apply imp_intro
  assume Hor
  apply or_elim (eq {bool} false true ∨ eq {bool} false true) (eq {bool} false true)
  // Goal π ((eq false true ∨ eq false true) ∨ eq false true)
  apply Hor
  // π (eq false true ∨ eq false true) ⇒ π (eq true false)
  assume Hor2
  apply or_elim (eq {bool} false true) (eq {bool} false true)
     apply Hor2
     assume Hfalsetrue rewrite Hfalsetrue reflexivity
     assume Hfalsetrue rewrite Hfalsetrue reflexivity     
  // π (eq false true) ⇒ π (eq true false)
  assume Hfalsetrue rewrite Hfalsetrue reflexivity

  // Goal RGB
  apply right_rgb
qed

                            
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
