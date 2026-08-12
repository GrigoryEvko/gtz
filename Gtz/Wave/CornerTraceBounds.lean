import Gtz.Wave.CompletePairKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corner trace bounds — eigen atoms bound the corner trace

One eigen atom caps the corner trace at one plus the shifted weight: the
complement minor forces the other eigenvalue below one.  Two eigen atoms
with a nonzero cross determinant read the corner trace exactly as the sum
of the two shifted weights.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.corner_mulVec_eigen_of_rows` — the row-to-vector packaging.
* `Gtz.corner_trace_eq_of_two_eigen_atoms` — **THE EXACT READING.**
* `Gtz.corner_trace_le_of_eigen_rows` — **THE TRACE CAP.**

## Vacuity

The statements are unconditional matrix facts.
-/

namespace Gtz

open Matrix

variable {basisCount : ℕ}

/-- The two eigen rows package into one eigenvector equation for the
corner. -/
theorem corner_mulVec_eigen_of_rows
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {firstSlot secondSlot : Fin basisCount} {u v d : ℝ}
    (hrowFirst : u * M firstSlot firstSlot + v * M secondSlot firstSlot = d * u)
    (hrowSecond : u * M firstSlot secondSlot + v * M secondSlot secondSlot = d * v) :
    (!![M firstSlot firstSlot, M secondSlot firstSlot;
        M firstSlot secondSlot, M secondSlot secondSlot]
      : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![u, v] = d • ![u, v] := by
  funext coordIndex
  fin_cases coordIndex
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination hrowFirst
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination hrowSecond

/-- **THE EXACT READING.**  Two eigen atoms with a nonzero cross
determinant read the corner trace as the sum of the two shifted
weights. -/
theorem corner_trace_eq_of_two_eigen_atoms
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {firstSlot secondSlot : Fin basisCount} {u v d uSecond vSecond dSecond : ℝ}
    (hrowFirst : u * M firstSlot firstSlot + v * M secondSlot firstSlot = d * u)
    (hrowSecond : u * M firstSlot secondSlot + v * M secondSlot secondSlot = d * v)
    (hrowThird : uSecond * M firstSlot firstSlot
      + vSecond * M secondSlot firstSlot = dSecond * uSecond)
    (hrowFourth : uSecond * M firstSlot secondSlot
      + vSecond * M secondSlot secondSlot = dSecond * vSecond)
    (hdet : u * vSecond - v * uSecond ≠ 0) :
    M firstSlot firstSlot + M secondSlot secondSlot = d + dSecond := by
  have htrace := trace_eq_add_of_eigen_pair
    (corner_mulVec_eigen_of_rows hrowFirst hrowSecond)
    (corner_mulVec_eigen_of_rows hrowThird hrowFourth)
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      intro hcontra
      apply hdet
      linear_combination hcontra)
  rw [Matrix.trace_fin_two_of] at htrace
  exact htrace

/-- **THE TRACE CAP.**  One eigen atom with the complement minor caps the
corner trace at one plus the shifted weight. -/
theorem corner_trace_le_of_eigen_rows
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {firstSlot secondSlot : Fin basisCount} {u v d : ℝ}
    (hrowFirst : u * M firstSlot firstSlot + v * M secondSlot firstSlot = d * u)
    (hrowSecond : u * M firstSlot secondSlot + v * M secondSlot secondSlot = d * v)
    (hnz : u ≠ 0 ∨ v ≠ 0)
    (hdOne : d < 1)
    (hcompl : 0 ≤ (1 - M firstSlot firstSlot) * (1 - M secondSlot secondSlot)
      - M firstSlot secondSlot * M secondSlot firstSlot) :
    M firstSlot firstSlot + M secondSlot secondSlot ≤ 1 + d := by
  have hchar := corner_det_eq_of_eigen_rows hrowFirst hrowSecond hnz
  have hcomplLinear : 0 ≤ 1 - (M firstSlot firstSlot + M secondSlot secondSlot)
      + (M firstSlot firstSlot * M secondSlot secondSlot
        - M firstSlot secondSlot * M secondSlot firstSlot) := by
    linear_combination hcompl
  by_contra hlarge
  push Not at hlarge
  have hproduct : (1 - (M firstSlot firstSlot + M secondSlot secondSlot) + d)
      * (1 - d) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  nlinarith [hcomplLinear, hchar, hproduct]

end Gtz
