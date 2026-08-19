import Gtz.Wave.SixSetProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The three-atom downdate of the six-set gap: the strictness producer

Every card-3 triple of a `(6,3)` design is the three-atom downdate of the
six-set gap `W = S_univ − 1` at its complement
(`Gtz.tripleGap_eq_sixSet_downdate`).  When `W ≻ 0` — proved at the
corank-two corner by `Gtz.sixSetGap_posDef_of_rankOneGap` — a triple
dominates STRICTLY as soon as every combination of the three complementary
atoms reads the `W⁻¹` metric below its own square norm
(`Gtz.posDef_sub_triple_of_combination_reading`): the Cauchy–Schwarz
inequality of the `W` metric turns the combination readings into the full
quadratic bound.  The design-level producer
(`Gtz.not_isTie_of_sixSet_combination_reading`) exhibits the strict triple
and refutes the tie.

This is the dispatch surface of the projection program: the reduced
certificates of the campaign record produce exactly a complementary triple
whose combination readings stay below one, and this module converts that
certificate into the kernel refutation.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The downdate equation -/

/-- A triple's gap is the six-set gap downdated by the complementary
atoms. -/
theorem tripleGap_eq_sixSet_downdate (D : WeightedDesign m k)
    (R : Finset (Fin m)) :
    subsetSum D Rᶜ - 1
      = (subsetSum D Finset.univ - 1) - ∑ r ∈ R, atomMatrix (D.atom r) := by
  have hsplit : subsetSum D Rᶜ + ∑ r ∈ R, atomMatrix (D.atom r)
      = subsetSum D Finset.univ := by
    rw [subsetSum, subsetSum]
    exact Finset.sum_compl_add_sum R _
  rw [← hsplit]
  abel

/-! ## 2. The combination-reading producer -/

/-- **The three-atom downdate stays positive definite when every
combination of the removed atoms reads the inverse metric below its square
norm.**  Cauchy–Schwarz in the `W` metric: for `y` with reading vector
`ξ = (a·y, b·y, c·y)` and `g` the `ξ`-combination of the atoms,
`(y·g)² ≤ (yᵀWy)·(gᵀW⁻¹g)` and `y·g = |ξ|²`, so the strict reading bound
forces `|ξ|² < yᵀWy`. -/
theorem posDef_sub_triple_of_combination_reading
    (W : Matrix (Fin k) (Fin k) ℝ) (hW : W.PosDef)
    (a b c : Fin k → ℝ)
    (hread : ∀ r s q : ℝ, ¬(r = 0 ∧ s = 0 ∧ q = 0) →
      (r • a + s • b + q • c) ⬝ᵥ (W⁻¹ *ᵥ (r • a + s • b + q • c))
        < r ^ 2 + s ^ 2 + q ^ 2) :
    (W - Matrix.vecMulVec a a - Matrix.vecMulVec b b
      - Matrix.vecMulVec c c).PosDef := by
  classical
  have hWT : Wᵀ = W := PosDef.transpose_eq hW
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hW.det_pos)
  have hWpos : ∀ v : Fin k → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (W *ᵥ v) := by
    intro v hv
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hW).2 hv
    rwa [star_trivial] at this
  have hWnn : ∀ v : Fin k → ℝ, 0 ≤ v ⬝ᵥ (W *ᵥ v) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hWpos v hv).le
  have hvT : ∀ v : Fin k → ℝ,
      (Matrix.vecMulVec v v)ᵀ = Matrix.vecMulVec v v := by
    intro v
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.transpose_apply, mul_comm]
  have hherm : (W - Matrix.vecMulVec a a - Matrix.vecMulVec b b
      - Matrix.vecMulVec c c).IsHermitian := by
    refine isHermitian_of_transpose_eq ?_
    simp only [Matrix.transpose_sub, hWT, hvT]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hherm, fun y hyne => ?_⟩
  rw [star_trivial]
  have hform : y ⬝ᵥ ((W - Matrix.vecMulVec a a - Matrix.vecMulVec b b
        - Matrix.vecMulVec c c) *ᵥ y)
      = y ⬝ᵥ (W *ᵥ y) - (a ⬝ᵥ y) ^ 2 - (b ⬝ᵥ y) ^ 2 - (c ⬝ᵥ y) ^ 2 := by
    simp only [Matrix.sub_mulVec, dotProduct_sub, vecMulVec_mulVec_eq,
      dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm y a, dotProduct_comm y b, dotProduct_comm y c]
    ring
  rw [hform]
  set r : ℝ := a ⬝ᵥ y with hr
  set s : ℝ := b ⬝ᵥ y with hs
  set q : ℝ := c ⬝ᵥ y with hq
  by_cases hzero : r = 0 ∧ s = 0 ∧ q = 0
  · obtain ⟨h1, h2, h3⟩ := hzero
    rw [h1, h2, h3]
    simpa using hWpos y hyne
  · set g : Fin k → ℝ := r • a + s • b + q • c with hg
    set z : Fin k → ℝ := W⁻¹ *ᵥ g with hz
    have hWz : W *ᵥ z = g := by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hu,
        Matrix.one_mulVec]
    have hyg : y ⬝ᵥ g = r ^ 2 + s ^ 2 + q ^ 2 := by
      rw [hg]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm y a, dotProduct_comm y b, dotProduct_comm y c,
        ← hr, ← hs, ← hq]
      ring
    have hQv : z ⬝ᵥ (W *ᵥ z) = g ⬝ᵥ (W⁻¹ *ᵥ g) := by
      rw [hWz, hz, dotProduct_comm]
    have hyWz : y ⬝ᵥ (W *ᵥ z) = r ^ 2 + s ^ 2 + q ^ 2 := by
      rw [hWz, hyg]
    have hzWy : z ⬝ᵥ (W *ᵥ y) = r ^ 2 + s ^ 2 + q ^ 2 := by
      rw [dot_mulVec_comm hWT z y, hyWz]
    have hexpand : ∀ σ : ℝ, (y - σ • z) ⬝ᵥ (W *ᵥ (y - σ • z))
        = (g ⬝ᵥ (W⁻¹ *ᵥ g)) * (σ * σ)
          + (-(2 * (r ^ 2 + s ^ 2 + q ^ 2))) * σ + y ⬝ᵥ (W *ᵥ y) := by
      intro σ
      simp only [sub_dotProduct, smul_dotProduct, Matrix.mulVec_sub,
        Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [hyWz, hzWy, hQv]
      ring
    have hquad : ∀ σ : ℝ, 0 ≤ (g ⬝ᵥ (W⁻¹ *ᵥ g)) * (σ * σ)
        + (-(2 * (r ^ 2 + s ^ 2 + q ^ 2))) * σ + y ⬝ᵥ (W *ᵥ y) := by
      intro σ
      rw [← hexpand σ]
      exact hWnn _
    have hdisc := discrim_le_zero hquad
    rw [discrim] at hdisc
    have hR2 : 0 < r ^ 2 + s ^ 2 + q ^ 2 := by
      rcases not_and_or.mp hzero with h | h
      · positivity
      rcases not_and_or.mp h with h' | h'
      · positivity
      · positivity
    have hQlt : g ⬝ᵥ (W⁻¹ *ᵥ g) < r ^ 2 + s ^ 2 + q ^ 2 := hread r s q hzero
    have hWy : 0 < y ⬝ᵥ (W *ᵥ y) := hWpos y hyne
    nlinarith [hdisc, hQlt, hR2, hWy]

/-! ## 3. The design-level producer -/

/-- **The tie refuter.**  At a `(6,3)` design with `W = S_univ − 1 ≻ 0`, a
card-3 subset `R` whose atom combinations all read `W⁻¹` below their square
norm exhibits the strict dominator `Rᶜ`: the design is not a tie. -/
theorem not_isTie_of_sixSet_combination_reading (D : WeightedDesign 6 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {r1 r2 r3 : Fin 6} (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hread : ∀ r s q : ℝ, ¬(r = 0 ∧ s = 0 ∧ q = 0) →
      (r • D.atom r1 + s • D.atom r2 + q • D.atom r3)
          ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹
            *ᵥ (r • D.atom r1 + s • D.atom r2 + q • D.atom r3))
        < r ^ 2 + s ^ 2 + q ^ 2) :
    ¬ IsTie D := by
  classical
  intro htie
  set R : Finset (Fin 6) := {r1, r2, r3} with hR
  have hcardR : R.card = 3 := by
    rw [hR, Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have hcardRc : Rᶜ.card = 3 := card_compl_eq_three_of_card_eq_three R hcardR
  have hsum : ∑ r ∈ R, atomMatrix (D.atom r)
      = Matrix.vecMulVec (D.atom r1) (D.atom r1)
        + Matrix.vecMulVec (D.atom r2) (D.atom r2)
        + Matrix.vecMulVec (D.atom r3) (D.atom r3) := by
    rw [hR, Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]), Finset.sum_singleton, atomMatrix,
      atomMatrix, atomMatrix]
    abel
  have hgapEq := tripleGap_eq_sixSet_downdate D R
  rw [hsum] at hgapEq
  have hstrict : (subsetSum D Rᶜ - 1).PosDef := by
    have hshape : (subsetSum D Finset.univ - 1)
          - (Matrix.vecMulVec (D.atom r1) (D.atom r1)
            + Matrix.vecMulVec (D.atom r2) (D.atom r2)
            + Matrix.vecMulVec (D.atom r3) (D.atom r3))
        = (subsetSum D Finset.univ - 1)
          - Matrix.vecMulVec (D.atom r1) (D.atom r1)
          - Matrix.vecMulVec (D.atom r2) (D.atom r2)
          - Matrix.vecMulVec (D.atom r3) (D.atom r3) := by
      abel
    rw [hgapEq, hshape]
    exact posDef_sub_triple_of_combination_reading _ hPD _ _ _ hread
  exact htie.2 Rᶜ hcardRc hstrict

end Gtz
