/-
# The 3×3 Sylvester criterion: positive leading minors ⟹ positive definite

The per-cell checker core for the σ_min(J) certificate consumption (subgapv
Lean queue item 3): every exact cell asserts positive definiteness of a
rational symmetric matrix through its LDLᵀ pivots, which are exactly the
leading-principal-minor ratios. Kernel form, division-free: the completed
squares assemble into the SOS identity

`a·m₂·Q(v) = m₂·(a·v₀ + b·v₁ + c·v₂)² + (m₂·v₁ + (ae−bc)·v₂)² + a·m₃·v₂²`

(`m₂ = ad−b²`, `m₃ = det M`), a pure ring identity; positivity of the three
minors then forces `Q(v) > 0` at every nonzero `v` — no eigenvalues, no
square roots, `norm_num`-decidable at rational data. -/
import Mathlib
import Gtz.PsdKit

namespace Gtz

open Matrix

/-- **The 3×3 Sylvester criterion**: a symmetric real 3×3 matrix with
positive leading principal minors is positive definite. -/
theorem posDef_three_of_leading_minors {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hsym : Mᵀ = M)
    (hminorOne : 0 < M 0 0)
    (hminorTwo : 0 < M 0 0 * M 1 1 - M 0 1 ^ 2)
    (hminorThree : 0 < M.det) : M.PosDef := by
  have hentry10 : M 1 0 = M 0 1 := by
    have h := congrFun (congrFun hsym 0) 1
    rwa [Matrix.transpose_apply] at h
  have hentry20 : M 2 0 = M 0 2 := by
    have h := congrFun (congrFun hsym 0) 2
    rwa [Matrix.transpose_apply] at h
  have hentry21 : M 2 1 = M 1 2 := by
    have h := congrFun (congrFun hsym 1) 2
    rwa [Matrix.transpose_apply] at h
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsym, fun v hv => ?_⟩
  rw [star_trivial]
  -- the quadratic form in components
  have hform : v ⬝ᵥ (M *ᵥ v)
      = M 0 0 * v 0 ^ 2 + M 1 1 * v 1 ^ 2 + M 2 2 * v 2 ^ 2
        + 2 * M 0 1 * (v 0 * v 1) + 2 * M 0 2 * (v 0 * v 2)
        + 2 * M 1 2 * (v 1 * v 2) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, hentry10,
      hentry20, hentry21]
    ring
  -- the division-free LDL sum of squares
  have hdet : M.det
      = M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 ^ 2 - M 0 1 ^ 2 * M 2 2
        + 2 * M 0 1 * M 0 2 * M 1 2 - M 0 2 ^ 2 * M 1 1 := by
    rw [Matrix.det_fin_three, hentry10, hentry20, hentry21]
    ring
  have hSOS : M 0 0 * (M 0 0 * M 1 1 - M 0 1 ^ 2) * (v ⬝ᵥ (M *ᵥ v))
      = (M 0 0 * M 1 1 - M 0 1 ^ 2)
          * (M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2) ^ 2
        + ((M 0 0 * M 1 1 - M 0 1 ^ 2) * v 1
            + (M 0 0 * M 1 2 - M 0 1 * M 0 2) * v 2) ^ 2
        + M 0 0 * M.det * v 2 ^ 2 := by
    rw [hform, hdet]
    ring
  have hscalePos : 0 < M 0 0 * (M 0 0 * M 1 1 - M 0 1 ^ 2) :=
    mul_pos hminorOne hminorTwo
  suffices hscaled : 0 < M 0 0 * (M 0 0 * M 1 1 - M 0 1 ^ 2) * (v ⬝ᵥ (M *ᵥ v))
    from (mul_pos_iff_of_pos_left hscalePos).mp hscaled
  rw [hSOS]
  -- split on the LAST nonzero component: exactly one square is forced live
  rcases eq_or_ne (v 2) 0 with htwoZero | htwoLive
  · rcases eq_or_ne (v 1) 0 with honeZero | honeLive
    · -- v₁ = v₂ = 0 forces v₀ ≠ 0: the first square is live
      have hzeroLive : v 0 ≠ 0 := by
        intro hzero
        refine hv (funext fun index => ?_)
        fin_cases index
        · exact hzero
        · exact honeZero
        · exact htwoZero
      have hlinLive : M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2 ≠ 0 := by
        rw [honeZero, htwoZero]
        simpa using mul_ne_zero hminorOne.ne' hzeroLive
      have hfirst : 0 < (M 0 0 * M 1 1 - M 0 1 ^ 2)
          * (M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2) ^ 2 :=
        mul_pos hminorTwo ((sq_nonneg _).lt_of_ne' (pow_ne_zero 2 hlinLive))
      have hthird : 0 ≤ M 0 0 * M.det * v 2 ^ 2 :=
        mul_nonneg (mul_pos hminorOne hminorThree).le (sq_nonneg _)
      linarith [hfirst, hthird,
        sq_nonneg ((M 0 0 * M 1 1 - M 0 1 ^ 2) * v 1
          + (M 0 0 * M 1 2 - M 0 1 * M 0 2) * v 2)]
    · -- v₂ = 0, v₁ ≠ 0: the middle square is live
      have hlinLive : (M 0 0 * M 1 1 - M 0 1 ^ 2) * v 1
          + (M 0 0 * M 1 2 - M 0 1 * M 0 2) * v 2 ≠ 0 := by
        rw [htwoZero]
        simpa using mul_ne_zero hminorTwo.ne' honeLive
      have hmiddle : 0 < ((M 0 0 * M 1 1 - M 0 1 ^ 2) * v 1
          + (M 0 0 * M 1 2 - M 0 1 * M 0 2) * v 2) ^ 2 :=
        (sq_nonneg _).lt_of_ne' (pow_ne_zero 2 hlinLive)
      have hfirst : 0 ≤ (M 0 0 * M 1 1 - M 0 1 ^ 2)
          * (M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2) ^ 2 :=
        mul_nonneg hminorTwo.le (sq_nonneg _)
      have hthird : 0 ≤ M 0 0 * M.det * v 2 ^ 2 :=
        mul_nonneg (mul_pos hminorOne hminorThree).le (sq_nonneg _)
      linarith [hmiddle, hfirst, hthird]
  · -- v₂ ≠ 0: the determinant square is live
    have hthird : 0 < M 0 0 * M.det * v 2 ^ 2 :=
      mul_pos (mul_pos hminorOne hminorThree)
        ((sq_nonneg _).lt_of_ne' (pow_ne_zero 2 htwoLive))
    have hfirst : 0 ≤ (M 0 0 * M 1 1 - M 0 1 ^ 2)
        * (M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2) ^ 2 :=
      mul_nonneg hminorTwo.le (sq_nonneg _)
    linarith [hthird, hfirst,
      sq_nonneg ((M 0 0 * M 1 1 - M 0 1 ^ 2) * v 1
        + (M 0 0 * M 1 2 - M 0 1 * M 0 2) * v 2)]

end Gtz
