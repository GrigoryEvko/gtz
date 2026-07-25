import Gtz.Reduction.RatCertificate
import Gtz.Reduction.BranchTwoRational

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# AUDITOR B, matrix-free complete brick

`Gtz.dominates_of_pairGate` is Sylvester's criterion for a symmetric `3 x 3`
restricted to the case where SOME `2 x 2` principal block is strictly positive
definite; `Gtz.exists_dominatingTriple_withoutStrictGate` is exactly the classical
failure of the strict-leading-minor form on the PSD boundary.

The textbook repair is to use ALL principal minors instead of leading ones.  That
gives a criterion which is matrix-free, exactly rational, and an IFF -- with no
degeneracy gap at all, so the builder's "single most valuable next brick" does not
have to be answered.
-/

namespace Gtz

open Matrix

/-- **PSD from all seven principal minors, rank three.** No strictness anywhere. -/
theorem posSemidef_three_of_principalMinors {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmetric : formᵀ = form)
    (hdiagZero : 0 ≤ form 0 0) (hdiagOne : 0 ≤ form 1 1) (hdiagTwo : 0 ≤ form 2 2)
    (hminorZeroOne : 0 ≤ form 0 0 * form 1 1 - form 0 1 ^ 2)
    (hminorZeroTwo : 0 ≤ form 0 0 * form 2 2 - form 0 2 ^ 2)
    (hminorOneTwo : 0 ≤ form 1 1 * form 2 2 - form 1 2 ^ 2)
    (hdeterminant : 0 ≤ form.det) :
    form.PosSemidef := by
  have hflipOne : form 1 0 = form 0 1 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hflipTwo : form 2 0 = form 0 2 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hflipThree : form 2 1 = form 1 2 := by
    conv_lhs => rw [← hsymmetric]
    rfl
  have hdet : form.det
      = form 0 0 * (form 1 1 * form 2 2 - form 1 2 ^ 2)
        - form 0 1 * (form 0 1 * form 2 2 - form 1 2 * form 0 2)
        + form 0 2 * (form 0 1 * form 1 2 - form 1 1 * form 0 2) := by
    rw [Matrix.det_fin_three, hflipOne, hflipTwo, hflipThree]
    ring
  rw [hdet] at hdeterminant
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe => ?_⟩
  rw [star_trivial]
  have hform : probe ⬝ᵥ (form *ᵥ probe)
      = form 0 0 * probe 0 ^ 2 + form 1 1 * probe 1 ^ 2 + form 2 2 * probe 2 ^ 2
        + 2 * form 0 1 * probe 0 * probe 1 + 2 * form 0 2 * probe 0 * probe 2
        + 2 * form 1 2 * probe 1 * probe 2 := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    rw [hflipOne, hflipTwo, hflipThree]
    ring
  rw [hform]
  rcases eq_or_lt_of_le hdiagZero with hzero | hpos
  · -- the `0 0` entry vanishes, so its whole row does
    have hoffOne : form 0 1 = 0 := by nlinarith [sq_nonneg (form 0 1)]
    have hoffTwo : form 0 2 = 0 := by nlinarith [sq_nonneg (form 0 2)]
    rw [← hzero, hoffOne, hoffTwo]
    rcases eq_or_lt_of_le hdiagOne with hzeroOne | hposOne
    · have hoffThree : form 1 2 = 0 := by nlinarith [sq_nonneg (form 1 2)]
      rw [← hzeroOne, hoffThree]
      nlinarith [sq_nonneg (probe 2), hdiagTwo]
    · nlinarith [sq_nonneg (form 1 1 * probe 1 + form 1 2 * probe 2),
        sq_nonneg (probe 2), mul_nonneg hminorOneTwo (sq_nonneg (probe 2)),
        hposOne]
  · -- the `0 0` entry is positive: complete the square and use `PQ - R^2 = a*det`
    set pivotOne : ℝ := form 0 0 * form 1 1 - form 0 1 ^ 2 with hpivotOne
    set pivotTwo : ℝ := form 0 0 * form 2 2 - form 0 2 ^ 2 with hpivotTwo
    set crossTerm : ℝ := form 0 0 * form 1 2 - form 0 1 * form 0 2 with hcross
    have hschur : pivotOne * pivotTwo - crossTerm ^ 2
        = form 0 0 * (form 0 0 * (form 1 1 * form 2 2 - form 1 2 ^ 2)
            - form 0 1 * (form 0 1 * form 2 2 - form 1 2 * form 0 2)
            + form 0 2 * (form 0 1 * form 1 2 - form 1 1 * form 0 2)) := by
      rw [hpivotOne, hpivotTwo, hcross]; ring
    have hschurNonneg : 0 ≤ pivotOne * pivotTwo - crossTerm ^ 2 := by
      rw [hschur]
      exact mul_nonneg hpos.le hdeterminant
    -- the reduced 2x2 form in the last two coordinates is nonnegative
    have htail : 0 ≤ pivotOne * probe 1 ^ 2
        + 2 * crossTerm * probe 1 * probe 2 + pivotTwo * probe 2 ^ 2 := by
      rcases eq_or_lt_of_le hminorZeroOne with hpivZero | hpivPos
      · have hpivotZero : pivotOne = 0 := hpivZero.symm
        have hcrossZero : crossTerm = 0 := by
          nlinarith [hschurNonneg, hpivotZero, sq_nonneg crossTerm]
        rw [hcrossZero, hpivotZero]
        nlinarith [sq_nonneg (probe 2), hminorZeroTwo]
      · nlinarith [sq_nonneg (pivotOne * probe 1 + crossTerm * probe 2),
          mul_nonneg hschurNonneg (sq_nonneg (probe 2)), hpivPos]
    -- multiply the goal by the positive pivot and complete the square
    have hscaled : form 0 0 * (form 0 0 * probe 0 ^ 2 + form 1 1 * probe 1 ^ 2
          + form 2 2 * probe 2 ^ 2 + 2 * form 0 1 * probe 0 * probe 1
          + 2 * form 0 2 * probe 0 * probe 2 + 2 * form 1 2 * probe 1 * probe 2)
        = (form 0 0 * probe 0 + form 0 1 * probe 1 + form 0 2 * probe 2) ^ 2
          + (pivotOne * probe 1 ^ 2 + 2 * crossTerm * probe 1 * probe 2
              + pivotTwo * probe 2 ^ 2) := by
      rw [hpivotOne, hpivotTwo, hcross]; ring
    nlinarith [hscaled, htail,
      sq_nonneg (form 0 0 * probe 0 + form 0 1 * probe 1 + form 0 2 * probe 2),
      hpos]

/-- **The matrix-free complete rank-three consumer.** For a rational design, a
`3`-subset dominates as soon as the seven principal minors of its rational Gram
shift are nonnegative — seven exact rational comparisons, no matrix supplied, no
strict inequality, no gate, no fresh atom, and NO degeneracy gap. Compare
`ratDominates_of_pairGate`, which is the same criterion with the leading
`2 x 2` minor forced STRICTLY positive, and which is therefore silent exactly on
the locus `exists_dominatingTriple_withoutStrictGate` exhibits. -/
theorem ratDominates_of_principalMinors {m : ℕ} (R : RatDesign m 3)
    (subset : Finset (Fin m))
    (hdiagZero : 0 ≤ ratGram R subset 0 0)
    (hdiagOne : 0 ≤ ratGram R subset 1 1)
    (hdiagTwo : 0 ≤ ratGram R subset 2 2)
    (hminorZeroOne : 0 ≤ ratGram R subset 0 0 * ratGram R subset 1 1
                          - ratGram R subset 0 1 ^ 2)
    (hminorZeroTwo : 0 ≤ ratGram R subset 0 0 * ratGram R subset 2 2
                          - ratGram R subset 0 2 ^ 2)
    (hminorOneTwo : 0 ≤ ratGram R subset 1 1 * ratGram R subset 2 2
                          - ratGram R subset 1 2 ^ 2)
    (hdeterminant : 0 ≤ (ratGram R subset).det) :
    Dominates R.toReal subset := by
  have hentry : ∀ i j, (subsetSum R.toReal subset - 1) i j
      = ((ratGram R subset i j : ℚ) : ℝ) := by
    intro i j
    rw [R.gram_cast subset, Matrix.map_apply]
  have hsymRat : ∀ i j, ratGram R subset i j = ratGram R subset j i := by
    intro i j
    simp only [ratGram, Matrix.of_apply]
    rcases eq_or_ne i j with rfl | hne
    · rfl
    · rw [if_neg hne, if_neg (Ne.symm hne)]
      exact congrArg (· - 0) (Finset.sum_congr rfl fun c _ => mul_comm _ _)
  rw [Dominates]
  refine posSemidef_three_of_principalMinors ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ext i j
    rw [Matrix.transpose_apply, hentry, hentry, hsymRat]
  · rw [hentry]; exact_mod_cast hdiagZero
  · rw [hentry]; exact_mod_cast hdiagOne
  · rw [hentry]; exact_mod_cast hdiagTwo
  · rw [hentry, hentry, hentry]; exact_mod_cast hminorZeroOne
  · rw [hentry, hentry, hentry]; exact_mod_cast hminorZeroTwo
  · rw [hentry, hentry, hentry]; exact_mod_cast hminorOneTwo
  · rw [R.gram_cast subset, det_cast]; exact_mod_cast hdeterminant

/-- **The builder's own counterexample, certified by the matrix-free criterion.**
At `(1,1,0),(1,0,1),(0,1,1)` the Gram shift is the all-ones matrix: every 2x2
principal minor is `0` and the determinant is `0`, so `dominates_of_pairGate`
(which needs a STRICT 2x2 minor) is silent, while the non-strict principal-minor
criterion fires. -/
theorem degenerateWitness_byPrincipalMinors :
    (atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1] + atomMatrix ![0, 1, 1]
      - 1 : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
  have hentry : ∀ i j : Fin 3,
      (atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1] + atomMatrix ![0, 1, 1]
        - 1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply]
  refine posSemidef_three_of_principalMinors ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ext i j; rw [Matrix.transpose_apply, hentry, hentry]
  · rw [hentry]; norm_num
  · rw [hentry]; norm_num
  · rw [hentry]; norm_num
  · rw [hentry, hentry, hentry]; norm_num
  · rw [hentry, hentry, hentry]; norm_num
  · rw [hentry, hentry, hentry]; norm_num
  · rw [Matrix.det_fin_three, hentry, hentry, hentry, hentry, hentry, hentry,
      hentry, hentry, hentry]
    norm_num

end Gtz
