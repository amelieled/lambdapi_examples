require open amelie.notation
require open amelie.Bool
require open amelie.Logic

///////////////////////////////////////
// Definitions of type
///////////////////////////////////////
                                  
constant symbol rgb : Set
constant symbol RGB : TYPE
rule τ rgb → RGB
constant symbol red   : RGB
constant symbol green : RGB
constant symbol blue  : RGB

// Induction principle on RGB.
symbol rgb_ind :
   ∀p, π (p red) ⇒ π (p green) ⇒ π (p blue) ⇒ ∀c, π (p c)

constant symbol color : Set
constant symbol C : TYPE
rule τ color → C
constant symbol black : C
constant symbol white : C
constant symbol primary : RGB ⇒ C

// Induction principle on C.
symbol color_ind : ∀p, π (p black) ⇒ π (p white) ⇒ (∀n, π (p (primary n))) ⇒ ∀c, π (p c)

//////////////////////////////////////////
// Some functions         
//////////////////////////////////////////

symbol monochrome : C ⇒ B
rule monochrome black     → true
 and monochrome white     → true
 and monochrome (primary _) → false

symbol isred : C ⇒ B
rule isred black       → false
 and isred white       → false
 and isred (primary red) → true
 and isred (primary _  ) → false

symbol isgreen : C ⇒ B
rule isgreen black       → false
 and isgreen white       → false
 and isgreen (primary green) → true
 and isgreen (primary _  ) → false
                           
symbol isblue : C ⇒ B
rule isblue black       → false
 and isblue white       → false
 and isblue (primary blue) → true
 and isblue (primary _  ) → false

theorem left_rgb : ∀n,
π (monochrome (primary n) = false ⊃ isred (primary n) = true ∨ isgreen (primary n) = true ∨ isblue (primary n) = true)
proof
  assume n
  refine rgb_ind (λz, monochrome (primary z) = false ⊃
                      isred (primary z) = true ∨ isgreen (primary z) = true
                      ∨ isblue (primary z) = true) _ _ _ n
  // Goal red
  simpl
qed
