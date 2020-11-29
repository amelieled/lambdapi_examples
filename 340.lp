require open AL_library.Notation
require open AL_library.Bool
require open AL_library.Constructive_logic

///////////////////////////////////////
// Definitions of type
///////////////////////////////////////
constant symbol rgb : Set
constant symbol RGB : TYPE
rule τ rgb ↪ RGB
constant symbol red   : RGB
constant symbol green : RGB
constant symbol blue  : RGB

// Induction principle on RGB.
symbol rgb_ind :
   Πp, π (p red) → π (p green) → π (p blue) → Πc, π (p c)

constant symbol color : Set
constant symbol C : TYPE
rule τ color ↪ C
constant symbol black : C
constant symbol white : C
constant symbol primary : RGB → C

// Induction principle on C.
symbol color_ind : Πp, π (p black) → π (p white) → (Πn, π (p (primary n))) → Πc, π (p c)

//////////////////////////////////////////
// Some functions
//////////////////////////////////////////

symbol black_or_white : C → 𝔹
rule black_or_white black     ↪ true
 with black_or_white white     ↪ true
 with black_or_white (primary _) ↪ false

symbol isred : C → 𝔹
rule isred black       ↪ false
 with isred white       ↪ false
 with isred (primary red) ↪ true
 with isred (primary green) ↪ false
 with isred (primary blue) ↪ false

symbol isgreen : C → 𝔹
rule isgreen black       ↪ false
 with isgreen white       ↪ false
 with isgreen (primary red) ↪ false
 with isgreen (primary green) ↪ true
 with isgreen (primary blue) ↪ false
                           
symbol isblue : C → 𝔹
rule isblue black       ↪ false
 with isblue white       ↪ false
 with isblue (primary red) ↪ false
 with isblue (primary green) ↪ false
 with isblue (primary blue) ↪ true

theorem left_rgb : Πn,
π (black_or_white (primary n) = false ⊃ isred (primary n) = true ∨ isgreen (primary n) = true ∨ isblue (primary n) = true)
proof
  assume n
  refine rgb_ind (λz, black_or_white (primary z) = false ⊃
                      isred (primary z) = true ∨ isgreen (primary z) = true
                      ∨ isblue (primary z) = true) _ _ _ n
  // Goal red
  simpl
admit
