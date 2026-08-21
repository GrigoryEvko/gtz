/-
# Cell H has two downdate producers, and the second is not optional

`Gtz.cellH_exists_dominating_triple_of_posDef` turns a positive gap determinant
of the `y`-trio into a strictly dominating triple, with no admissibility
hypothesis, by reading each trio member as a rank-one downdate of `A_y`.  The
lane recorded the residual as the emptiness of

  `{ corner, A_y ≻ 0, A_z ⊁ 0, T4 ≤ 0, T5 ≤ 0, T6 ≤ 0 }` ,

on the strength of a census in which the `y`-trio fired at every sampled
inhabitant.  **That set is not empty.**  A cell-H inhabitant with all three
`T_i` strictly negative exists, and the reason is structural rather than
numerical: the `y`-trio is the star of ONE inside atom, and it never looks at
the other two.

## What the witness shows

An explicit design (`scratchpad/cells/f59verify2.jl`, verified from its raw
atoms with no shared code) has weights summing to one at `8.9e-16`, Parseval
residual `2.0e-14`, gap spectrum `S_C − 1 = (−4.5e-16, 1.1e-15, 2.948744)` —
a genuine corank-two corner — together with

  `mineig A_y = +0.099371` ,  `mineig A_z = −0.114719` ,
  `T4 = −5561.49` ,  `T5 = −25182.02` ,  `T6 = −16347.39` ,

every leverage at least one.  So it satisfies every hypothesis of the target,
and the `y`-trio does not fire.  It is nevertheless **not a tie**: the triple
`{x, g4, g5}` dominates strictly, at `λmin = +0.048688`.  The target is false,
and the cell-H kill it was meant to certify is untouched.

## The repair

The rescuing triple always contains the inside atom the `y`-trio omits.  So run
the downdate producer a second time, at `A_x` in place of `A_y`
(`Gtz.twoStar_exists_dominating_triple`): if either four-set is positive
definite and its own trio has a positive gap determinant, some triple of the
design dominates strictly.  Nothing new is needed — the rank-one downdate
argument is indifferent to which inside atom is fixed.

[MEASURED on cell-H inhabitants carrying the landed leverage floor: the
`y`-trio fires at 89.256 percent, and every one of the 1935 residual points has
`A_x ≻ 0` with its `x`-trio firing — 1935 of 1935.  **The union covers
18010 of 18010, and every residual point is rescued by a triple through `x`**
(669 by `{x,4,6}`, 657 by `{x,5,6}`, 609 by `{x,4,5}`).  The one-star census
that reported total coverage sampled a chart in which the omitted atom could
not carry the dominator.]
-/
import Gtz.Wave.CellHDowndatePromotion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The star of one fixed atom -/

/-- **THE DOWNDATE PRODUCER AT A FIXED INSIDE ATOM.**  If the four-set built
from the fixed atom and the outside triple is positive definite, a positive gap
determinant anywhere in its star is strict domination.

This is `Gtz.cellH_exists_dominating_triple_of_posDef` with the fixed atom named
rather than assumed to be `y`: the rank-one downdate argument never uses which
inside atom was chosen. -/
theorem star_exists_posDef_of_posDef_of_det_pos {a b c d : Fin 3 → ℝ}
    (hA : (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).PosDef)
    (hdet : 0 < (atomMatrix a + atomMatrix c + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix a + atomMatrix b + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix a + atomMatrix b + atomMatrix c - 1).det) :
    (atomMatrix a + atomMatrix c + atomMatrix d - 1).PosDef
      ∨ (atomMatrix a + atomMatrix b + atomMatrix d - 1).PosDef
      ∨ (atomMatrix a + atomMatrix b + atomMatrix c - 1).PosDef :=
  cellH_exists_dominating_triple_of_posDef hA hdet

/-! ## 2. Two stars -/

/-- **THE TWO-STAR PRODUCER.**  Cell H fixes one inside atom, and its trio is
blind to the other two.  Running the same downdate producer at a second inside
atom covers that blind spot: whichever four-set is positive definite with a
firing trio yields a strictly dominating triple of the design.

The disjunction is over the two stars, not over a probe — no selection rule and
no data-dependent constant appears. -/
theorem twoStar_exists_dominating_triple {x y b c d : Fin 3 → ℝ}
    (hstar : ((atomMatrix y + atomMatrix b + atomMatrix c + atomMatrix d - 1).PosDef
        ∧ (0 < (atomMatrix y + atomMatrix c + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix y + atomMatrix b + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix y + atomMatrix b + atomMatrix c - 1).det))
      ∨ ((atomMatrix x + atomMatrix b + atomMatrix c + atomMatrix d - 1).PosDef
        ∧ (0 < (atomMatrix x + atomMatrix c + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix c - 1).det))) :
    ((atomMatrix y + atomMatrix c + atomMatrix d - 1).PosDef
        ∨ (atomMatrix y + atomMatrix b + atomMatrix d - 1).PosDef
        ∨ (atomMatrix y + atomMatrix b + atomMatrix c - 1).PosDef)
      ∨ ((atomMatrix x + atomMatrix c + atomMatrix d - 1).PosDef
        ∨ (atomMatrix x + atomMatrix b + atomMatrix d - 1).PosDef
        ∨ (atomMatrix x + atomMatrix b + atomMatrix c - 1).PosDef) := by
  rcases hstar with ⟨hA, hdet⟩ | ⟨hA, hdet⟩
  · exact Or.inl (star_exists_posDef_of_posDef_of_det_pos hA hdet)
  · exact Or.inr (star_exists_posDef_of_posDef_of_det_pos hA hdet)

/-- **THE TWO-STAR PRODUCER AS A SINGLE EXISTENTIAL.**  Either star delivers a
positive definite triple gap, so a design meeting cell H at either inside atom
carries a strictly dominating triple. -/
theorem exists_posDef_of_twoStar {x y b c d : Fin 3 → ℝ}
    (hstar : ((atomMatrix y + atomMatrix b + atomMatrix c + atomMatrix d - 1).PosDef
        ∧ (0 < (atomMatrix y + atomMatrix c + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix y + atomMatrix b + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix y + atomMatrix b + atomMatrix c - 1).det))
      ∨ ((atomMatrix x + atomMatrix b + atomMatrix c + atomMatrix d - 1).PosDef
        ∧ (0 < (atomMatrix x + atomMatrix c + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix d - 1).det
          ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix c - 1).det))) :
    ∃ e f g : Fin 3 → ℝ,
      (atomMatrix e + atomMatrix f + atomMatrix g - 1).PosDef := by
  rcases twoStar_exists_dominating_triple hstar with h | h
  · rcases h with h | h | h
    · exact ⟨y, c, d, h⟩
    · exact ⟨y, b, d, h⟩
    · exact ⟨y, b, c, h⟩
  · rcases h with h | h | h
    · exact ⟨x, c, d, h⟩
    · exact ⟨x, b, d, h⟩
    · exact ⟨x, b, c, h⟩

end Gtz
