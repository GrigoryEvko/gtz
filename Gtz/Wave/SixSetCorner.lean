import Gtz.Wave.SixSetProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corner block laws of the six-set pivot matrix

At the corank-two corner the six-set gap splits as
`W = lam • u uᵀ + S_out` (`Gtz.sixSetGap_eq_gapAtom_add_outside`): the gap
atom carries the corner direction and the outside atoms carry the rest.
Reading `W⁻¹` through this split produces the exact block laws of the pivot
matrix `P_{cc'} = g_cᵀ W⁻¹ g_{c'}`:

* every outside pivot is capped by one (`Gtz.outside_pivot_le_one`), and the
  `u`-pivot is capped by `1/lam` (`Gtz.uPivot_le_one`) — both because
  removing one PSD summand from `W` leaves a PSD matrix;
* the outside pivots sum to `3 − π_u` where `π_u := lam·uᵀW⁻¹u`
  (`Gtz.outside_pivot_sum`);
* the co-weighted INSIDE pivot sum equals `π_u` plus the weighted outside
  pivot sum (`Gtz.inside_coweight_pivot_sum`) — the trace law splits at the
  corner;
* every atom's outside row mass is its pivot minus `lam` times its squared
  `u`-cross pivot (`Gtz.outside_row_mass`) — the diagonal of the cross-block
  law `P_CD P_DC = P_CC − lam ηηᵀ`.

These are the resources of the ghost certificates: the tie's refusals push
the pivot blocks up, and these laws price what pushing up costs.  Everything
here consumes the corner split, so nothing survives at `lam = 0`; the sums
quantify over the complement, so nothing can be stated at `(5,3)` where the
complement of a triple is a pair.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **The corner split of the six-set gap.**  `W = lam • u uᵀ + S_out`. -/
theorem sixSetGap_eq_gapAtom_add_outside (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    subsetSum D Finset.univ - 1 = lam • atomMatrix u + subsetSum D Cᶜ := by
  have hsplit : subsetSum D C + subsetSum D Cᶜ = subsetSum D Finset.univ := by
    rw [subsetSum, subsetSum, subsetSum]
    exact Finset.sum_add_sum_compl C _
  calc subsetSum D Finset.univ - 1
      = (subsetSum D C - 1) + subsetSum D Cᶜ := by rw [← hsplit]; abel
    _ = lam • atomMatrix u + subsetSum D Cᶜ := by rw [hgap]

/-- The six-set gap dominates the outside atom sum. -/
theorem sixSetGap_sub_outside_posSemidef (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ((subsetSum D Finset.univ - 1) - subsetSum D Cᶜ).PosSemidef := by
  rw [sixSetGap_eq_gapAtom_add_outside D C hgap, add_sub_cancel_right]
  exact (posSemidef_atomMatrix u).smul hlam

/-- **Every outside pivot is capped by one.**  Removing one outside atom
from the six-set gap leaves a PSD matrix, so its reading is at most one. -/
theorem outside_pivot_le_one (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef)
    {d : Fin m} (hd : d ∈ Cᶜ) :
    D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d) ≤ 1 := by
  refine (posSemidef_sub_vecMulVec_iff (subsetSum D Finset.univ - 1) hPD
    (D.atom d)).mp ?_
  have hrest : ((subsetSum D Finset.univ - 1)
      - Matrix.vecMulVec (D.atom d) (D.atom d))
      = lam • atomMatrix u + ∑ d' ∈ Cᶜ.erase d, atomMatrix (D.atom d') := by
    rw [sixSetGap_eq_gapAtom_add_outside D C hgap]
    have hsum : subsetSum D Cᶜ
        = atomMatrix (D.atom d) + ∑ d' ∈ Cᶜ.erase d, atomMatrix (D.atom d') := by
      rw [subsetSum, ← Finset.add_sum_erase Cᶜ _ hd]
    rw [hsum, show atomMatrix (D.atom d)
      = Matrix.vecMulVec (D.atom d) (D.atom d) from rfl]
    abel
  rw [hrest]
  exact ((posSemidef_atomMatrix u).smul hlam).add
    (Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add)
      (Matrix.PosSemidef.zero) (fun d' _ => posSemidef_atomMatrix (D.atom d')))

/-- **The `u`-pivot cap.**  `lam · uᵀW⁻¹u ≤ 1`: the gap atom's own reading
of the six-set metric never exceeds one. -/
theorem uPivot_le_one (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u)) ≤ 1 := by
  have hread := (posSemidef_sub_vecMulVec_iff (subsetSum D Finset.univ - 1)
    hPD (Real.sqrt lam • u)).mp ?_
  · have hsq : Real.sqrt lam • u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹
        *ᵥ (Real.sqrt lam • u))
        = lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u)) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, Real.mul_self_sqrt hlam]
    rwa [hsq] at hread
  · have hatom : Matrix.vecMulVec (Real.sqrt lam • u) (Real.sqrt lam • u)
        = lam • atomMatrix u := by
      rw [show Matrix.vecMulVec (Real.sqrt lam • u) (Real.sqrt lam • u)
        = atomMatrix (Real.sqrt lam • u) from rfl, atomMatrix_smul,
        Real.sq_sqrt hlam]
    rw [hatom, sixSetGap_eq_gapAtom_add_outside D C hgap, add_sub_cancel_left]
    exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add)
      (Matrix.PosSemidef.zero) (fun d' _ => posSemidef_atomMatrix (D.atom d'))

/-- **The outside pivots sum to `3 − π_u`.**  The trace of `W⁻¹S_out` reads
the corner split. -/
theorem outside_pivot_sum (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ d ∈ Cᶜ, D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)
      = 3 - lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u)) := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D Finset.univ - 1 with hW
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have htr := sum_subset_quadForm_eq_trace D Cᶜ W⁻¹
  have hout : subsetSum D Cᶜ = W - lam • atomMatrix u := by
    rw [hW, sixSetGap_eq_gapAtom_add_outside D C hgap]
    abel
  rw [htr, hout, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.nonsing_inv_mul W hu, Matrix.trace_one, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, trace_mul_atomMatrix]
  norm_num

/-- **The inside co-weighted pivot sum.**  The trace law splits at the
corner: `Σ_{e∈C}(1−t_e)P_ee = π_u + Σ_{d∉C} t_d P_dd`. -/
theorem inside_coweight_pivot_sum (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ e ∈ C, (1 - D.weight e)
        * (D.atom e ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom e))
      = lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ u))
        + ∑ d ∈ Cᶜ, D.weight d
            * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)) := by
  classical
  have htrace := sixSet_coweight_pivot_sum D hPD
  rw [← Finset.sum_add_sum_compl C] at htrace
  have hsplit : ∑ d ∈ Cᶜ, (1 - D.weight d)
        * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d))
      = ∑ d ∈ Cᶜ, D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)
        - ∑ d ∈ Cᶜ, D.weight d
            * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsplit, outside_pivot_sum D C hgap hPD] at htrace
  linarith [htrace]

/-- **The outside row mass.**  For any probe vector, the outside readings'
square sum is the probe's own pivot minus `lam` times its squared `u`-cross
reading: the diagonal of `P_CD P_DC = P_CC − lam ηηᵀ`. -/
theorem outside_row_mass (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (v : Fin 3 → ℝ) :
    ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ v)) ^ 2
      = v ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ v)
        - lam * (u ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ v)) ^ 2 := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D Finset.univ - 1 with hW
  have hWsymm : Wᵀ = W := transpose_subsetSum_sub_one D Finset.univ
  have hWinvsymm : (W⁻¹)ᵀ = W⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  set y : Fin 3 → ℝ := W⁻¹ *ᵥ v with hy
  have hterm : ∀ d : Fin m,
      (D.atom d ⬝ᵥ y) ^ 2 = y ⬝ᵥ (atomMatrix (D.atom d) *ᵥ y) := by
    intro d
    rw [atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y (D.atom d)]
    ring
  have hsum : ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ y) ^ 2
      = y ⬝ᵥ (subsetSum D Cᶜ *ᵥ y) := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun d _ => hterm d
  have hout : subsetSum D Cᶜ = W - lam • atomMatrix u := by
    rw [hW, sixSetGap_eq_gapAtom_add_outside D C hgap]
    abel
  have hWy : W *ᵥ y = v := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hu,
      Matrix.one_mulVec]
  have huy : u ⬝ᵥ y = u ⬝ᵥ (W⁻¹ *ᵥ v) := by rw [hy]
  rw [hsum, hout, Matrix.sub_mulVec, dotProduct_sub, hWy,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul]
  have hvy : y ⬝ᵥ v = v ⬝ᵥ (W⁻¹ *ᵥ v) := by
    rw [hy, dotProduct_comm]
  have hyu : y ⬝ᵥ u = u ⬝ᵥ (W⁻¹ *ᵥ v) := by
    rw [hy, dotProduct_comm, dot_mulVec_comm hWinvsymm u v]
  rw [hvy, hyu, huy]
  ring

end Gtz
