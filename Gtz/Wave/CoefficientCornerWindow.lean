import Gtz.Wave.TwoSharedPairKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coefficient corner window — corner minors under a diagonal Gram

When the Gram core is diagonal with positive entries, the two capture
windows push down to every two-by-two corner of the coefficient matrix:
the corner determinant is nonnegative, the complementary corner
determinant is nonnegative, and each diagonal entry sits in `[0, 1]`.
The corner minors of the captured form and of its complement carry the
positive diagonal factors, which cancel.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.corner_det_nonneg_of_diagonal_gram` — the corner minor.
* `Gtz.corner_complement_det_nonneg_of_diagonal_gram` — the complement.
* `Gtz.diagonal_window_of_diagonal_gram` — the diagonal window.

## Vacuity

The statements are unconditional matrix facts.
-/

namespace Gtz

open Matrix

variable {basisCount : ℕ}

/-- The two-by-two principal minor of a positive semidefinite matrix is
nonnegative. -/
theorem posSemidef_pair_minor_nonneg
    {X : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hpsd : X.PosSemidef) (firstSlot secondSlot : Fin basisCount) :
    0 ≤ X firstSlot firstSlot * X secondSlot secondSlot
      - X firstSlot secondSlot * X secondSlot firstSlot := by
  classical
  have hsub : (X.submatrix ![firstSlot, secondSlot] ![firstSlot, secondSlot]).PosSemidef :=
    hpsd.submatrix _
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simpa using hdet

/-- **THE CORNER MINOR.**  Under a diagonal Gram with positive entries,
the corner determinant of the coefficient matrix is nonnegative. -/
theorem corner_det_nonneg_of_diagonal_gram
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {gramWeight : Fin basisCount → ℝ}
    (hgramPos : ∀ slotIndex, 0 < gramWeight slotIndex)
    (hXpsd : (M * Matrix.diagonal gramWeight).PosSemidef)
    (firstSlot secondSlot : Fin basisCount) :
    0 ≤ M firstSlot firstSlot * M secondSlot secondSlot
      - M firstSlot secondSlot * M secondSlot firstSlot := by
  have hminor := posSemidef_pair_minor_nonneg hXpsd firstSlot secondSlot
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal,
    Matrix.mul_diagonal] at hminor
  by_contra hneg
  push Not at hneg
  have hproduct : (M firstSlot firstSlot * M secondSlot secondSlot
      - M firstSlot secondSlot * M secondSlot firstSlot)
      * (gramWeight firstSlot * gramWeight secondSlot) < 0 :=
    mul_neg_of_neg_of_pos hneg
      (mul_pos (hgramPos firstSlot) (hgramPos secondSlot))
  nlinarith [hminor, hproduct]

/-- **THE COMPLEMENT MINOR.**  Under a diagonal Gram with positive
entries, the complementary corner determinant is nonnegative. -/
theorem corner_complement_det_nonneg_of_diagonal_gram
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {gramWeight : Fin basisCount → ℝ}
    (hgramPos : ∀ slotIndex, 0 < gramWeight slotIndex)
    (hYpsd : (Matrix.diagonal gramWeight - M * Matrix.diagonal gramWeight).PosSemidef)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot) :
    0 ≤ (1 - M firstSlot firstSlot) * (1 - M secondSlot secondSlot)
      - M firstSlot secondSlot * M secondSlot firstSlot := by
  have hminor := posSemidef_pair_minor_nonneg hYpsd firstSlot secondSlot
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ (Ne.symm hne)]
    at hminor
  by_contra hneg
  push Not at hneg
  have hproduct : ((1 - M firstSlot firstSlot) * (1 - M secondSlot secondSlot)
      - M firstSlot secondSlot * M secondSlot firstSlot)
      * (gramWeight firstSlot * gramWeight secondSlot) < 0 :=
    mul_neg_of_neg_of_pos hneg
      (mul_pos (hgramPos firstSlot) (hgramPos secondSlot))
  nlinarith [hminor, hproduct]

/-- **THE DIAGONAL WINDOW.**  Under a diagonal Gram with positive entries,
each diagonal coefficient sits in `[0, 1]`. -/
theorem diagonal_window_of_diagonal_gram
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {gramWeight : Fin basisCount → ℝ}
    (hgramPos : ∀ slotIndex, 0 < gramWeight slotIndex)
    (hXpsd : (M * Matrix.diagonal gramWeight).PosSemidef)
    (hYpsd : (Matrix.diagonal gramWeight - M * Matrix.diagonal gramWeight).PosSemidef)
    (slotIndex : Fin basisCount) :
    0 ≤ M slotIndex slotIndex ∧ M slotIndex slotIndex ≤ 1 := by
  have hlower := hXpsd.diag_nonneg (i := slotIndex)
  have hupper := hYpsd.diag_nonneg (i := slotIndex)
  rw [Matrix.mul_diagonal] at hlower
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_apply_eq] at hupper
  constructor
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg (hgramPos slotIndex)]
  · by_contra hlarge
    push Not at hlarge
    nlinarith [hgramPos slotIndex]

end Gtz
