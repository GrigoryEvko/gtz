/-
# The repaying slot is not a corner statement

The coherent horn is open on two existence facts: some outside pair of the
corner is ADMISSIBLE, and some inside atom REPAYS it, meaning the one-inside
triple it forms strictly dominates.  The landed
`Gtz.tripleGapDet_pos_iff_exactCost` turns the second into the sign of

  `tripleGapDet a b g_e  =  D * (l_e - 1) - r_e' adj(M) r_e` ,

with `M` the gap block of the outside pair, `D = pairGapMinor a b`, and
`r_e = (a . g_e, b . g_e)` the readings of the inside atom.  The identity is the
cofactor expansion of the third Sylvester minor and needs no hypothesis.

This module fixes the SCOPE of that second fact.  It exhibits an exact rational
corner, with a unit axis and an outside pair that is admissible and whose two
atoms are both heavy, at which ALL THREE one-inside gap determinants are
strictly negative (`Gtz.repayScope_all_neg`).  So

  **the corner equation, admissibility and heaviness together do NOT force a
  repaying inside atom** (`Gtz.repayScope_not_forced`).

The horn's second existence fact is therefore not a statement about one corner
and one pair.  It needs the design hypotheses -- Parseval across all six atoms,
and the failing branch of the dual-frame certificate -- and any attempt to prove
it from corner data alone is refuted by this witness.

## The witness, and why it is not an edge case

The corner is `gx = (1,0,0)`, `gy = (0,1,0)`, `gz = (0,0,2)`, so that
`gx gx' + gy gy' + gz gz' = 1 + 3 * u u'` with `u = (0,0,1)` of unit length.
The outside pair is `a = (3/2, 0, 3/2)` and `b = (0, 3/2, 3/2)`, giving
leverages `9/2`, pairing `9/4`, and `pairGapMinor a b = 115/16 > 0`.  The three
determinants are `-63/8`, `-63/8` and `-15/16`.

The witness sits at corner scale `lam = 3`, ABOVE the landed threshold of
`Gtz.corner_pairSum_nonpos_of_lam_le`, so the failure is not the small-scale
regime where the sum law is already known to be blind.  It belongs to a family:
taking `gz = (0,0,m)`, `a = (x,0,z)`, `b = (0,x,z)` with `m^2 = 1 + lam` and
`x > 1`, all three determinants are nonpositive as soon as
`2 z^2 >= (x^2 - 1) * lam`, so a witness exists at EVERY corner scale.  The
instances `lam = 5/4`, `lam = 3` and `lam = 8` were all checked in exact
rational arithmetic.

[MEASURED, and this is the other half of the scope.  On the failing branch of a
genuine `(6,3)` design the fact is never violated: over 505476 sampled
failing-branch corners, EVERY one carries an admissible outside pair with a
repaying inside atom.  Writing the corner as `l_e - 1 = lam * v_e^2` for a unit
`v` and the readings as free vectors -- which is a faithful chart for one corner
and one pair -- the same statement holds at only 54.6 percent of admissible
pairs, and 69.8 percent under a wide scale sweep.  The gap between 54.6 and 100
is exactly the design content this module says is indispensable.]
-/
import Gtz.Wave.CornerAxisElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

namespace RepayScope

/-- The first inside atom of the witness corner. -/
def insideX : Fin 3 → ℝ := ![1, 0, 0]

/-- The second inside atom of the witness corner. -/
def insideY : Fin 3 → ℝ := ![0, 1, 0]

/-- The third inside atom, carrying the whole corner scale. -/
def insideZ : Fin 3 → ℝ := ![0, 0, 2]

/-- The gap axis of the witness corner. -/
def axis : Fin 3 → ℝ := ![0, 0, 1]

/-- The first atom of the witness outside pair. -/
noncomputable def outsideA : Fin 3 → ℝ := ![3 / 2, 0, 3 / 2]

/-- The second atom of the witness outside pair. -/
noncomputable def outsideB : Fin 3 → ℝ := ![0, 3 / 2, 3 / 2]

end RepayScope

open RepayScope

/-! ## 1. The witness is a corner -/

/-- The three inside atoms resolve the identity plus three times the axis. -/
theorem repayScope_corner :
    atomMatrix insideX + atomMatrix insideY + atomMatrix insideZ
      = 1 + (3 : ℝ) • atomMatrix axis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [insideX, insideY, insideZ, axis, atomMatrix, Matrix.cons_val_two]

/-- The axis of the witness is a unit vector. -/
theorem repayScope_axis_unit : leverageOf axis = 1 := by
  norm_num [axis, leverageOf, Fin.sum_univ_three, Matrix.cons_val_two]

/-! ## 2. The outside pair is admissible, and both its atoms are heavy -/

/-- The first outside atom is heavy. -/
theorem repayScope_leverage_a : leverageOf outsideA = 9 / 2 := by
  norm_num [outsideA, leverageOf, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The second outside atom is heavy. -/
theorem repayScope_leverage_b : leverageOf outsideB = 9 / 2 := by
  norm_num [outsideB, leverageOf, Fin.sum_univ_three, Matrix.cons_val_two]

/-- The pairing of the outside pair. -/
theorem repayScope_pairing : outsideA ⬝ᵥ outsideB = 9 / 4 := by
  norm_num [outsideA, outsideB, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

/-- **THE PAIR IS ADMISSIBLE.**  Its second Sylvester minor is `115/16`. -/
theorem repayScope_admissible : pairGapMinor outsideA outsideB = 115 / 16 := by
  rw [pairGapMinor, repayScope_leverage_a, repayScope_leverage_b, repayScope_pairing]
  norm_num

/-! ## 3. No inside atom repays -/

/-- The first inside atom does not repay. -/
theorem repayScope_det_x : tripleGapDet outsideA outsideB insideX = -(63 / 8) := by
  norm_num [tripleGapDet, outsideA, outsideB, insideX, leverageOf, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- The second inside atom does not repay. -/
theorem repayScope_det_y : tripleGapDet outsideA outsideB insideY = -(63 / 8) := by
  norm_num [tripleGapDet, outsideA, outsideB, insideY, leverageOf, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- The third inside atom does not repay either, although it carries the whole
corner scale. -/
theorem repayScope_det_z : tripleGapDet outsideA outsideB insideZ = -(15 / 16) := by
  norm_num [tripleGapDet, outsideA, outsideB, insideZ, leverageOf, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- **ALL THREE ONE-INSIDE GAP DETERMINANTS ARE STRICTLY NEGATIVE.** -/
theorem repayScope_all_neg :
    tripleGapDet outsideA outsideB insideX < 0
      ∧ tripleGapDet outsideA outsideB insideY < 0
      ∧ tripleGapDet outsideA outsideB insideZ < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [repayScope_det_x]; norm_num
  · rw [repayScope_det_y]; norm_num
  · rw [repayScope_det_z]; norm_num

/-! ## 4. The scope theorem -/

/-- **THE REPAYING SLOT IS NOT FORCED BY THE CORNER.**  There are a corner with
a unit axis, and an outside pair that is admissible with both atoms heavy, at
which no inside atom strictly dominates.  So the horn's second existence fact
cannot be derived from the corner equation and admissibility alone: it needs the
design hypotheses.

The witness carries corner scale three, above the threshold at which the landed
sum law is already known to be blind, so this is not that regime. -/
theorem repayScope_not_forced :
    ∃ gx gy gz u a b : Fin 3 → ℝ, ∃ lam : ℝ,
      (atomMatrix gx + atomMatrix gy + atomMatrix gz = 1 + lam • atomMatrix u)
        ∧ leverageOf u = 1
        ∧ 2 < lam
        ∧ 1 < leverageOf a
        ∧ 1 < leverageOf b
        ∧ 0 < pairGapMinor a b
        ∧ tripleGapDet a b gx ≤ 0
        ∧ tripleGapDet a b gy ≤ 0
        ∧ tripleGapDet a b gz ≤ 0 := by
  refine ⟨insideX, insideY, insideZ, axis, outsideA, outsideB, 3,
    repayScope_corner, repayScope_axis_unit, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [repayScope_leverage_a]; norm_num
  · rw [repayScope_leverage_b]; norm_num
  · rw [repayScope_admissible]; norm_num
  · rw [repayScope_det_x]; norm_num
  · rw [repayScope_det_y]; norm_num
  · rw [repayScope_det_z]; norm_num

end Gtz
