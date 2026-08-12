import Gtz.Wave.CoefficientCornerWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corner characteristic — an eigen atom prices the corner determinant

An eigenvector of a two-by-two corner turns the corner determinant into
`d * (trace - d)`.  With the complement minor and the shifted window, the
other eigenvalue sits at most at one, and the determinant is at most `d`.
This bound is the engine of the complete-pair kill.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.corner_det_eq_of_eigen_rows` — **THE CHARACTERISTIC.**
* `Gtz.corner_det_le_of_eigen_rows` — **THE DETERMINANT CAP.**

## Vacuity

The statements are unconditional matrix facts.
-/

namespace Gtz

open Matrix

variable {basisCount : ℕ}

/-- **THE CHARACTERISTIC.**  Two eigen rows with a nonzero vector price
the corner determinant as `d * (trace - d)`. -/
theorem corner_det_eq_of_eigen_rows
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {firstSlot secondSlot : Fin basisCount} {u v d : ℝ}
    (hrowFirst : u * M firstSlot firstSlot + v * M secondSlot firstSlot = d * u)
    (hrowSecond : u * M firstSlot secondSlot + v * M secondSlot secondSlot = d * v)
    (hnz : u ≠ 0 ∨ v ≠ 0) :
    M firstSlot firstSlot * M secondSlot secondSlot
        - M firstSlot secondSlot * M secondSlot firstSlot
      = d * ((M firstSlot firstSlot + M secondSlot secondSlot) - d) := by
  classical
  have hker : (!![M firstSlot firstSlot - d, M secondSlot firstSlot;
      M firstSlot secondSlot, M secondSlot secondSlot - d]
        : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![u, v] = 0 := by
    funext coordIndex
    fin_cases coordIndex
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hrowFirst
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hrowSecond
  have hvne : (![u, v] : Fin 2 → ℝ) ≠ 0 := by
    intro hcontra
    rcases hnz with hu | hv
    · exact hu (by simpa using congrFun hcontra 0)
    · exact hv (by simpa using congrFun hcontra 1)
  have hdetZero : (!![M firstSlot firstSlot - d, M secondSlot firstSlot;
      M firstSlot secondSlot, M secondSlot secondSlot - d]
        : Matrix (Fin 2) (Fin 2) ℝ).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨![u, v], hvne, hker⟩
  rw [Matrix.det_fin_two_of] at hdetZero
  linear_combination hdetZero

/-- **THE DETERMINANT CAP.**  With the complement minor and the shifted
window, the corner determinant of an eigen pair is at most the shifted
weight. -/
theorem corner_det_le_of_eigen_rows
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {firstSlot secondSlot : Fin basisCount} {u v d : ℝ}
    (hrowFirst : u * M firstSlot firstSlot + v * M secondSlot firstSlot = d * u)
    (hrowSecond : u * M firstSlot secondSlot + v * M secondSlot secondSlot = d * v)
    (hnz : u ≠ 0 ∨ v ≠ 0)
    (hdZero : 0 ≤ d) (hdOne : d < 1)
    (hcompl : 0 ≤ (1 - M firstSlot firstSlot) * (1 - M secondSlot secondSlot)
      - M firstSlot secondSlot * M secondSlot firstSlot) :
    M firstSlot firstSlot * M secondSlot secondSlot
      - M firstSlot secondSlot * M secondSlot firstSlot ≤ d := by
  have hchar := corner_det_eq_of_eigen_rows hrowFirst hrowSecond hnz
  have hcomplLinear : 0 ≤ 1 - (M firstSlot firstSlot + M secondSlot secondSlot)
      + (M firstSlot firstSlot * M secondSlot secondSlot
        - M firstSlot secondSlot * M secondSlot firstSlot) := by
    linear_combination hcompl
  have hslack : 0 ≤ 1 - (M firstSlot firstSlot + M secondSlot secondSlot) + d := by
    by_contra hneg
    push Not at hneg
    have hproduct : (1 - (M firstSlot firstSlot + M secondSlot secondSlot) + d)
        * (1 - d) < 0 :=
      mul_neg_of_neg_of_pos hneg (by linarith)
    nlinarith [hcomplLinear, hchar, hproduct]
  nlinarith [mul_nonneg hdZero hslack, hchar]

end Gtz
