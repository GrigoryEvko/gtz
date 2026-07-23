/-
# The 2×2 PSD entry criterion

For a symmetric real 2×2 matrix: PSD ⟺ both diagonal entries and the
determinant are nonnegative; under positive trace the diagonal clause is
implied and PSD ⟺ det ≥ 0. The forward determinant bound is the quadratic
discriminant (`discrim_le_zero`); the backward direction is the SOS certificate
(trace)·(form) = (X₀₀v₀ + X₀₁v₁)² + (X₀₁v₀ + X₁₁v₁)² + det·(v₀² + v₁²).

This is the rank-2 lane's domination decoder: for a pair matrix S_{cd} − I of
positive trace (Case B heavy atoms), failure to dominate is EXACTLY a negative
determinant — the scalar pair-obstruction K_{cd} > 0 of diary §61.
-/
import Mathlib
import Gtz.Basic
import Gtz.SchurRankOne

namespace Gtz

open Matrix

/-- The quadratic form of a 2×2 matrix, in entries. -/
theorem dot_mulVec_two (X : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    v ⬝ᵥ (X *ᵥ v)
      = X 0 0 * v 0 ^ 2 + (X 0 1 + X 1 0) * (v 0 * v 1) + X 1 1 * v 1 ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- **The 2×2 PSD entry criterion** for symmetric matrices. -/
theorem posSemidef_two_iff {X : Matrix (Fin 2) (Fin 2) ℝ} (hXT : Xᵀ = X) :
    X.PosSemidef ↔
      0 ≤ X 0 0 ∧ 0 ≤ X 1 1 ∧ 0 ≤ X 0 0 * X 1 1 - X 0 1 ^ 2 := by
  have hsym : X 1 0 = X 0 1 := by
    have h := congrFun (congrFun hXT 0) 1
    rwa [Matrix.transpose_apply] at h
  constructor
  · intro hpsd
    have hform : ∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ (X *ᵥ v) := by
      intro v
      have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
      rwa [star_trivial] at h
    have h00 := hform ![1, 0]
    have h11 := hform ![0, 1]
    rw [dot_mulVec_two] at h00 h11
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    have hquad : ∀ s : ℝ,
        0 ≤ X 0 0 * (s * s) + (X 0 1 + X 1 0) * s + X 1 1 := by
      intro s
      have h := hform ![s, 1]
      rw [dot_mulVec_two] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
      nlinarith [h]
    have hdisc := discrim_le_zero hquad
    rw [discrim, hsym] at hdisc
    nlinarith [hdisc]
  · rintro ⟨h00, h11, hdet⟩
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hXT, fun v => ?_⟩
    rw [star_trivial, dot_mulVec_two, hsym]
    rcases eq_or_lt_of_le (add_nonneg h00 h11) with htr0 | htrpos
    · have hX00 : X 0 0 = 0 := by linarith
      have hX11 : X 1 1 = 0 := by linarith
      have hX01 : X 0 1 = 0 := by
        have hsq : X 0 1 ^ 2 ≤ 0 := by nlinarith
        exact pow_eq_zero_iff (n := 2) (by omega) |>.mp
          (le_antisymm hsq (sq_nonneg _))
      rw [hX00, hX11, hX01]
      norm_num
    · nlinarith [sq_nonneg (X 0 0 * v 0 + X 0 1 * v 1),
        sq_nonneg (X 0 1 * v 0 + X 1 1 * v 1),
        mul_nonneg hdet (sq_nonneg (v 0)), mul_nonneg hdet (sq_nonneg (v 1))]

/-- Under positive trace the diagonal clause is implied: PSD ⟺ det ≥ 0. -/
theorem posSemidef_two_iff_of_trace_pos {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hXT : Xᵀ = X) (htr : 0 < X 0 0 + X 1 1) :
    X.PosSemidef ↔ 0 ≤ X 0 0 * X 1 1 - X 0 1 ^ 2 := by
  rw [posSemidef_two_iff hXT]
  constructor
  · exact fun h => h.2.2
  · intro hdet
    refine ⟨?_, ?_, hdet⟩ <;> nlinarith [sq_nonneg (X 0 1)]

end Gtz
