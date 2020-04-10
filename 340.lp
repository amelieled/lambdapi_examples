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

symbol black_or_white : C ⇒ B
rule black_or_white black     → true
 and black_or_white white     → true
 and black_or_white (primary _) → false

symbol isred : C ⇒ B
rule isred black       → false
 and isred white       → false
 and isred (primary red) → true
 and isred (primary green) → false
 and isred (primary blue) → false

symbol isgreen : C ⇒ B
rule isgreen black       → false
 and isgreen white       → false
 and isgreen (primary red) → false
 and isgreen (primary green) → true
 and isgreen (primary blue) → false
                           
symbol isblue : C ⇒ B
rule isblue black       → false
 and isblue white       → false
 and isblue (primary red) → false
 and isblue (primary green) → false
 and isblue (primary blue) → true

theorem left_rgb : ∀n,
π (black_or_white (primary n) = false ⊃ isred (primary n) = true ∨ isgreen (primary n) = true ∨ isblue (primary n) = true)
proof
  assume n
  refine rgb_ind (λz, black_or_white (primary z) = false ⊃
                      isred (primary z) = true ∨ isgreen (primary z) = true
                      ∨ isblue (primary z) = true) _ _ _ n
  // Goal red
  simpl
admit
