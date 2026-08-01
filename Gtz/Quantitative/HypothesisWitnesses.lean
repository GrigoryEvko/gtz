/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.SplitTransfer
import Gtz.Quantitative.ChartSecondOrderStep

/-!
# Two hypothesis separations that were carried as prose

A landed theorem is only as strong as the reach of its hypothesis, and two theorems
in this development shipped with a reach that was argued in a docstring rather than
checked.  Both arguments were correct; both are mechanized here, so neither has to be
re-derived by a reader and neither can drift.

## A. Positive definiteness is strictly weaker than the pinch

`Gtz.exists_design_of_frame` (ConverseBridge.lean) manufactures a genuine
`Gtz.WeightedDesign` from ANY family of atoms and ANY positive weight vector whose
frame operator is positive definite.  Its shipped neighbour
`Gtz.exists_whitenedDesign_of_framePinched` (SplitTransfer.lean:1423) does something
similar under `Gtz.FrameOperatorIsPinched` at `etaBound < 1`.  Whether the first is a
duplicate of the second turns entirely on whether its hypothesis is genuinely weaker,
and that was recorded as the one place where a wrong reading would collapse a landed
theorem into a duplicate.

It is genuinely weaker.  `Gtz.spreadFrame`, the diagonal frame operator with spectrum
`{1/10, 5}`, is positive definite and is pinched only at `4 <= etaBound`, so the
shipped theorem cannot be applied to it at all while the new one can.  The separation
is stated below both pointwise and as the existential
`Gtz.exists_posDef_not_frameOperatorIsPinched`.

## B. The curve constraint is block diagonal on its own

`Gtz.exists_acceleration_of_blockDiagonal_velocitySquare` (ChartSecondOrderStep.lean)
produces an acceleration for a velocity whose square is block diagonal for the
projection, and its non-vacuity witness had to establish block-diagonality first
rather than simply exhibiting a velocity.  The reason is that the constraint's LEFT
side is block diagonal whatever the acceleration is, so the constraint cannot be
solved for an arbitrary velocity -- the block-diagonality hypothesis is forced, not
convenient.  That is `Gtz.mul_curveConstraint_mul_one_sub_eq_zero` below, with the
consequence spelled out in `Gtz.blockDiagonal_velocitySquare_of_exists_acceleration`.

Note the direction of the second result: together with the shipped existence lemma it
makes block-diagonality of the velocity square EQUIVALENT to solvability, which is
strictly more than the shipped lemma alone says.

## Provenance

Both were mechanized at the `gtz-g3` mid-run checkpoint, in response to the two
writers who flagged them, and are harvested here rather than left in a scratch probe.
-/

namespace Gtz

open Matrix

/-! ## A. Positive definiteness does not imply the pinch -/

/-- The diagonal frame operator with spectrum `{1/10, 5}`.  Chosen so that the lower
pinch would need `1 - etaBound <= 1/10` and the upper `1 + etaBound >= 5`; the second
is the binding one. -/
noncomputable def spreadFrame : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![1 / 10, 5]

/-- The witness is positive definite, so it satisfies the weaker hypothesis. -/
theorem spreadFrame_posDef : spreadFrame.PosDef := by
  rw [spreadFrame]
  refine (Matrix.posDef_diagonal_iff).mpr ?_
  intro i
  fin_cases i <;> norm_num

/-- **THE PINCH COSTS AT LEAST FOUR HERE.**  Read the upper pinch at the second basis
vector, where the frame operator has the eigenvalue `5`. -/
theorem four_le_etaBound_of_spreadFrame_pinched {etaBound : ℝ}
    (hpinch : FrameOperatorIsPinched spreadFrame etaBound) : 4 ≤ etaBound := by
  obtain ⟨_, hupper⟩ := hpinch
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hupper).2 (Pi.single 1 1)
  simp only [star_trivial] at hform
  have hvalue : (Pi.single 1 1 : Fin 2 → ℝ) ⬝ᵥ
      (((1 + etaBound) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - spreadFrame).mulVec
        (Pi.single 1 1)) = (1 + etaBound) - 5 := by
    simp [spreadFrame, Matrix.mulVec, dotProduct,
      Matrix.diagonal, Matrix.one_apply, Pi.single_apply]
  rw [hvalue] at hform
  linarith

/-- So the shipped hypothesis is unreachable at this frame operator. -/
theorem not_frameOperatorIsPinched_spreadFrame_of_lt_one {etaBound : ℝ}
    (hbelow : etaBound < 1) : ¬ FrameOperatorIsPinched spreadFrame etaBound := by
  intro hpinch
  have hfour := four_le_etaBound_of_spreadFrame_pinched hpinch
  linarith

/-- **THE SEPARATION.**  Some positive definite frame operator is pinched at no bound
below one.  This is the statement that keeps `Gtz.exists_design_of_frame` from being a
restatement of `Gtz.exists_whitenedDesign_of_framePinched`: the two hypotheses are not
interchangeable, and the arrow runs only one way. -/
theorem exists_posDef_not_frameOperatorIsPinched :
    ∃ frameOperator : Matrix (Fin 2) (Fin 2) ℝ, frameOperator.PosDef ∧
      ∀ etaBound : ℝ, etaBound < 1 → ¬ FrameOperatorIsPinched frameOperator etaBound :=
  ⟨spreadFrame, spreadFrame_posDef, fun _ hbelow =>
    not_frameOperatorIsPinched_spreadFrame_of_lt_one hbelow⟩

/-! ## B. The curve constraint's left side is block diagonal -/

/-- **THE CONSTRAINT IS BLOCK DIAGONAL WHATEVER THE ACCELERATION.**  For any
idempotent `projection` and ANY `acceleration`, the combination that the second
derivative of `P s * P s = P s` produces is annihilated by the off-diagonal corner.

Only idempotence is used; nothing is asked of the acceleration. -/
theorem mul_curveConstraint_mul_one_sub_eq_zero {ambient : ℕ}
    (projection acceleration : Matrix (Fin ambient) (Fin ambient) ℝ)
    (hidempotent : projection * projection = projection) :
    projection * (acceleration * projection + projection * acceleration - acceleration) *
        (1 - projection) = 0 := by
  have habsorb : ∀ other : Matrix (Fin ambient) (Fin ambient) ℝ,
      projection * (projection * other) = projection * other := by
    intro other; rw [← Matrix.mul_assoc, hidempotent]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul,
    Matrix.mul_one, Matrix.mul_assoc, habsorb, hidempotent]
  abel

/-- **SO SOLVABILITY FORCES THE HYPOTHESIS.**  If some acceleration satisfies the
curve constraint for a given velocity, that velocity's square is block diagonal for
the projection.  With the shipped
`Gtz.exists_acceleration_of_blockDiagonal_velocitySquare` this makes block-diagonality
EQUIVALENT to solvability, so the hypothesis of the shipped lemma is forced rather
than convenient, and a non-vacuity witness for it genuinely has to establish
block-diagonality first. -/
theorem blockDiagonal_velocitySquare_of_exists_acceleration {ambient : ℕ}
    (projection velocity : Matrix (Fin ambient) (Fin ambient) ℝ)
    (hidempotent : projection * projection = projection)
    (hsolvable : ∃ acceleration : Matrix (Fin ambient) (Fin ambient) ℝ,
      acceleration * projection + projection * acceleration - acceleration
        = -(2 : ℝ) • (velocity * velocity)) :
    projection * (velocity * velocity) * (1 - projection) = 0 := by
  obtain ⟨acceleration, hcurve⟩ := hsolvable
  have hcorner := mul_curveConstraint_mul_one_sub_eq_zero projection acceleration hidempotent
  rw [hcurve] at hcorner
  have hscaled : -(2 : ℝ) • (projection * (velocity * velocity) * (1 - projection)) = 0 := by
    rw [← hcorner]
    simp
  have htwo : (-(2 : ℝ)) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp hscaled).resolve_left htwo

end Gtz
