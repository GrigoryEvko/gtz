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

/-!
## 5. The corner and its pair do not determine the repayment

The landed column total `Gtz.cornerForm_tripleGapDet_column_total` computes the
FIRST elementary symmetric function of the three one-inside gap determinants
from the corner scale and the pair alone.  This section shows that is the end of
the road: the second and third symmetric functions are NOT functions of that
data, and neither is the repayment itself.

The mechanism is the inside frame.  If `Vc` carries the three inside atoms as
columns then `Vc Vc' = 1 + lam u u'` is unchanged by `Vc -> Vc Q` for orthogonal
`Q`, so every corner invariant survives, while the individual readings of a
fixed outside pair rotate.  Taking `Q` a rational rotation of the first and
third axes turns the witness of section 4, where NO inside atom repays, into a
corner where one does -- with the axis, the scale, the outside pair, all the
pair invariants, and the column total all identical.
-/

namespace RepayScope

/-- The first inside atom of the rotated corner. -/
noncomputable def rotX : Fin 3 → ℝ := ![3 / 5, 0, 8 / 5]

/-- The second inside atom of the rotated corner, unchanged by the rotation. -/
def rotY : Fin 3 → ℝ := ![0, 1, 0]

/-- The third inside atom of the rotated corner. -/
noncomputable def rotZ : Fin 3 → ℝ := ![-(4 / 5), 0, 6 / 5]

end RepayScope

open RepayScope

/-- The rotated triple is a corner with the SAME axis and the SAME scale. -/
theorem repayScope_rot_corner :
    atomMatrix rotX + atomMatrix rotY + atomMatrix rotZ
      = 1 + (3 : ℝ) • atomMatrix axis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotX, rotY, rotZ, axis, atomMatrix, Matrix.cons_val_two]

/-- The rotated corner has a different inside leverage profile. -/
theorem repayScope_rot_leverages :
    leverageOf rotX = 73 / 25 ∧ leverageOf rotY = 1 ∧ leverageOf rotZ = 52 / 25 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [rotX, rotY, rotZ, leverageOf, Fin.sum_univ_three, Matrix.cons_val_two]

/-- On the rotated corner the first inside atom still does not repay. -/
theorem repayScope_rot_det_x :
    tripleGapDet outsideA outsideB rotX = -(1767 / 200) := by
  norm_num [tripleGapDet, outsideA, outsideB, rotX, leverageOf, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- Nor does the second. -/
theorem repayScope_rot_det_y :
    tripleGapDet outsideA outsideB rotY = -(63 / 8) := by
  norm_num [tripleGapDet, outsideA, outsideB, rotY, leverageOf, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- **BUT THE THIRD DOES.**  The same outside pair is repaid on the rotated
corner, by a strictly positive margin. -/
theorem repayScope_rot_det_z :
    tripleGapDet outsideA outsideB rotZ = 9 / 400 := by
  norm_num [tripleGapDet, outsideA, outsideB, rotZ, leverageOf, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-- **THE TWO CORNERS SHARE THEIR COLUMN TOTAL.**  Both equal `-267/16`, as the
landed column total law forces, since the axis, the scale and the pair agree. -/
theorem repayScope_column_totals_agree :
    tripleGapDet outsideA outsideB insideX + tripleGapDet outsideA outsideB insideY
        + tripleGapDet outsideA outsideB insideZ
      = tripleGapDet outsideA outsideB rotX + tripleGapDet outsideA outsideB rotY
        + tripleGapDet outsideA outsideB rotZ := by
  rw [repayScope_det_x, repayScope_det_y, repayScope_det_z,
    repayScope_rot_det_x, repayScope_rot_det_y, repayScope_rot_det_z]
  norm_num

/-- The two corners have DIFFERENT second symmetric functions, so `e2` is not a
function of the corner and the pair. -/
theorem repayScope_esymm_two_differ :
    tripleGapDet outsideA outsideB insideX * tripleGapDet outsideA outsideB insideY
        + tripleGapDet outsideA outsideB insideX * tripleGapDet outsideA outsideB insideZ
        + tripleGapDet outsideA outsideB insideY * tripleGapDet outsideA outsideB insideZ
      ≠ tripleGapDet outsideA outsideB rotX * tripleGapDet outsideA outsideB rotY
        + tripleGapDet outsideA outsideB rotX * tripleGapDet outsideA outsideB rotZ
        + tripleGapDet outsideA outsideB rotY * tripleGapDet outsideA outsideB rotZ := by
  rw [repayScope_det_x, repayScope_det_y, repayScope_det_z,
    repayScope_rot_det_x, repayScope_rot_det_y, repayScope_rot_det_z]
  norm_num

/-- **THE CORNER AND ITS PAIR DO NOT DETERMINE THE REPAYMENT.**  Two corners
share an axis, a scale, an outside pair -- hence every pair invariant, the two
axis readings, and the column total -- yet no inside atom of the first repays the
pair while one of the second does.

So no function of the corner-pair data decides the repayment.  In particular the
column total, which is the only symmetric function of the three determinants the
corner determines, provably cannot: it takes the same value on both sides. -/
theorem repayScope_pairData_undetermined :
    ∃ gx gy gz gx' gy' gz' u a b : Fin 3 → ℝ, ∃ lam : ℝ,
      (atomMatrix gx + atomMatrix gy + atomMatrix gz = 1 + lam • atomMatrix u)
        ∧ (atomMatrix gx' + atomMatrix gy' + atomMatrix gz' = 1 + lam • atomMatrix u)
        ∧ leverageOf u = 1
        ∧ 0 < pairGapMinor a b
        ∧ (tripleGapDet a b gx + tripleGapDet a b gy + tripleGapDet a b gz
            = tripleGapDet a b gx' + tripleGapDet a b gy' + tripleGapDet a b gz')
        ∧ (tripleGapDet a b gx ≤ 0 ∧ tripleGapDet a b gy ≤ 0 ∧ tripleGapDet a b gz ≤ 0)
        ∧ 0 < tripleGapDet a b gz' := by
  refine ⟨insideX, insideY, insideZ, rotX, rotY, rotZ, axis, outsideA, outsideB, 3,
    repayScope_corner, repayScope_rot_corner, repayScope_axis_unit, ?_,
    repayScope_column_totals_agree, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [repayScope_admissible]; norm_num
  · rw [repayScope_det_x]; norm_num
  · rw [repayScope_det_y]; norm_num
  · rw [repayScope_det_z]; norm_num
  · rw [repayScope_rot_det_z]; norm_num

end Gtz
