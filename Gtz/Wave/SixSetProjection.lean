import Gtz.Wave.CorankTwoNonplanarSystem
import Gtz.Wave.CorankTwoNonplanarDescent
import Gtz.Design.ComplementLeverageLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The six-set gap is positive definite at the corner, and its pivot matrix
is a co-weighted projection

At the corank-two corner with `lam > 0` the six-set gap `W := S_univ − 1` is
positive definite (`Gtz.sixSetGap_posDef_of_rankOneGap`): the split
criterion's `u`-mass is `1 + lam + Σ b_d² > 1`, the mixed block is carried by
the outside atoms alone (the dominator's cross sum vanishes), and the outside
plane cover (`Gtz.outside_plane_cover_of_rankOneGap`) beats Cauchy–Schwarz.

With `W ≻ 0` the pivot matrix `P_{cc'} := g_cᵀ W⁻¹ g_{c'}` carries the whole
tie combinatorics, and it obeys two EXACT laws:

* **the projection identity** (`Gtz.pivot_coweight_projection`):
  `Σ_c (1 − t_c)·P_{ac} P_{cb} = P_{ab}` — because the co-weighted atom sum
  `Σ (1−t_c) g_c g_cᵀ` IS the six-set gap
  (`Gtz.coweight_atomSum_eq_sixSetGap`), so `D₁^{1/2} P D₁^{1/2}` is an
  orthogonal projection of rank three;
* **the descent identity** (`Gtz.sixSet_coweight_pivot_sum`):
  `Σ_c (1 − t_c)·P_{cc} = 3` — its trace.

Every refusal of a card-3 triple `T` is a spectral condition on the
complementary 3×3 block `P_{TᶜTᶜ}` through the three-atom downdate of `W`,
so a `(6,3)` tie at the corner is a rank-three co-weighted projection whose
twenty complementary blocks all reach the co-weight threshold.  The campaign
record carries the reduced form: the corner is the rank-one equation
`diag(1−t_d) − V_out V_outᵀ = p pᵀ` on the projection's frame, the trace law
`tr(G − Γ) = |p|² − 2`, and the boundary pinch
`schur_e(I−G) = t_e` between the complement refusal and the ghost-pair
mixed refusals.

Nothing here can be stated at `(5,3)`: the corner needs the complement
triple.  There is no diamond hazard, by construction.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The co-weighted atom sum is the six-set gap -/

/-- **The co-weighted atom sum is the six-set gap.**  Parseval turns
`Σ_c (1−t_c) g_c g_cᵀ` into `S_univ − 1`. -/
theorem coweight_atomSum_eq_sixSetGap (D : WeightedDesign m k) :
    ∑ c, (1 - D.weight c) • atomMatrix (D.atom c)
      = subsetSum D Finset.univ - 1 := by
  have hsplit : ∑ c, (1 - D.weight c) • atomMatrix (D.atom c)
      = ∑ c, atomMatrix (D.atom c)
        - ∑ c, D.weight c • atomMatrix (D.atom c) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sub_smul, one_smul]
  rw [hsplit, D.isParseval, subsetSum]

/-! ## 2. The six-set gap is positive definite at the corner -/

/-- **The six-set gap is positive definite at the corner.**  For `lam > 0`
the split criterion closes through the outside plane cover: the `u`-mass is
`1 + lam + Σ b_d² > 1` and Cauchy–Schwarz on the outside cross readings
loses strictly to `lam` times the plane cover. -/
theorem sixSetGap_posDef_of_rankOneGap (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) (hne : Cᶜ.Nonempty)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    (subsetSum D Finset.univ - 1).PosDef := by
  classical
  refine (posDef_gap_iff_uSplit D Finset.univ hunit).mpr ⟨?_, ?_⟩
  · -- the u-mass: 1 + lam from the dominator, plus the outside mass
    have hin := uMass_of_rankOneGap D C hunit hgap
    have hsplit : ∑ c, (D.atom c ⬝ᵥ u) ^ 2
        = ∑ c ∈ C, (D.atom c ⬝ᵥ u) ^ 2 + ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ u) ^ 2 :=
      (Finset.sum_add_sum_compl C _).symm
    have hout : 0 ≤ ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ u) ^ 2 :=
      Finset.sum_nonneg fun c _ => sq_nonneg _
    rw [hsplit, hin]
    linarith
  · -- the plane condition: cross² < (B−1)·G
    intro w hw hwne
    have hcrossC := cross_of_rankOneGap D C hunit hw hgap
    have hcross : ∑ c, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)
        = ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w) := by
      rw [← Finset.sum_add_sum_compl C
        (fun c => (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)), hcrossC, zero_add]
    have hplaneC := planeMass_of_rankOneGap D C hw hgap
    have hplane : ∑ c, (D.atom c ⬝ᵥ w) ^ 2
        = w ⬝ᵥ w + ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ w) ^ 2 := by
      rw [← Finset.sum_add_sum_compl C (fun c => (D.atom c ⬝ᵥ w) ^ 2),
        hplaneC]
    have hin := uMass_of_rankOneGap D C hunit hgap
    have hmass : ∑ c, (D.atom c ⬝ᵥ u) ^ 2
        = 1 + lam + ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ u) ^ 2 := by
      rw [← Finset.sum_add_sum_compl C (fun c => (D.atom c ⬝ᵥ u) ^ 2), hin]
    -- Cauchy–Schwarz on the outside cross sum
    have hcs : (∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)) ^ 2
        ≤ (∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ u) ^ 2)
          * ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ w) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Cᶜ _ _
    -- the outside plane cover
    have hcover := outside_plane_cover_of_rankOneGap D C hcard hne hlam.le
      hunit hgap hw hwne
    have hWpos : 0 < w ⬝ᵥ w := dotProduct_self_pos hwne
    have houtm : 0 ≤ ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ u) ^ 2 :=
      Finset.sum_nonneg fun c _ => sq_nonneg _
    rw [hcross, hplane, hmass]
    have hG : 0 < ∑ c ∈ Cᶜ, (D.atom c ⬝ᵥ w) ^ 2 := lt_trans hWpos hcover
    nlinarith [hcs, hcover, hWpos, houtm, hG,
      mul_pos hlam hG, mul_nonneg houtm hWpos.le]

/-! ## 3. The projection identity -/

/-- **The pivot matrix is a co-weighted projection.**  With `W := S_univ − 1`
positive definite, the pivots `P_{cc'} = g_cᵀ W⁻¹ g_{c'}` satisfy the exact
law `Σ_c (1−t_c)·P_{ac}P_{cb} = P_{ab}`: conjugating the co-weighted atom sum
by `W⁻¹` collapses `W⁻¹ W W⁻¹` to `W⁻¹`. -/
theorem pivot_coweight_projection (D : WeightedDesign m k)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (a b : Fin m) :
    ∑ c, (1 - D.weight c)
        * ((D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c))
          * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b)))
      = D.atom a ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom b) := by
  classical
  set W : Matrix (Fin k) (Fin k) ℝ := subsetSum D Finset.univ - 1 with hW
  have hWsymm : Wᵀ = W := transpose_subsetSum_sub_one D Finset.univ
  have hWinvsymm : (W⁻¹)ᵀ = W⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  set x : Fin k → ℝ := W⁻¹ *ᵥ D.atom a with hx
  set y : Fin k → ℝ := W⁻¹ *ᵥ D.atom b with hy
  have hWsum : W = ∑ c, (1 - D.weight c) • atomMatrix (D.atom c) := by
    rw [hW, ← coweight_atomSum_eq_sixSetGap]
  have hpolar : ∑ c, (1 - D.weight c) * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ y))
      = x ⬝ᵥ (W *ᵥ y) := by
    rw [hWsum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul,
      smul_eq_mul, dotProduct_smul, smul_eq_mul, dotProduct_comm x (D.atom c)]
    ring
  have hWy : W *ᵥ y = D.atom b := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hu,
      Matrix.one_mulVec]
  calc ∑ c, (1 - D.weight c)
        * ((D.atom a ⬝ᵥ (W⁻¹ *ᵥ D.atom c)) * (D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom b)))
      = ∑ c, (1 - D.weight c) * ((D.atom c ⬝ᵥ x) * (D.atom c ⬝ᵥ y)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [show D.atom a ⬝ᵥ (W⁻¹ *ᵥ D.atom c)
            = D.atom c ⬝ᵥ x from by rw [hx]; exact dot_mulVec_comm hWinvsymm _ _,
          hy]
    _ = x ⬝ᵥ (W *ᵥ y) := hpolar
    _ = x ⬝ᵥ D.atom b := by rw [hWy]
    _ = D.atom a ⬝ᵥ (W⁻¹ *ᵥ D.atom b) := by
        rw [hx, dotProduct_comm]
        exact dot_mulVec_comm hWinvsymm _ _

/-! ## 4. The descent identity -/

/-- **The co-weighted pivot sum of the six-set is the rank.**
`Σ_c (1−t_c)·g_cᵀ W⁻¹ g_c = 3`: the trace of the projection. -/
theorem sixSet_coweight_pivot_sum (D : WeightedDesign m 3)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) :
    ∑ c, (1 - D.weight c)
        * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c))
      = 3 := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D Finset.univ - 1 with hW
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have hsplit : ∑ c, (1 - D.weight c) * (D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom c))
      = ∑ c, D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom c)
        - ∑ c, D.weight c * (D.atom c ⬝ᵥ (W⁻¹ *ᵥ D.atom c)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hall := sum_subset_quadForm_eq_trace D Finset.univ W⁻¹
  have hweighted := sum_weight_quadForm_eq_trace D W⁻¹
  have hSW : subsetSum D Finset.univ = W + 1 := by rw [hW]; abel
  have htr : Matrix.trace (W⁻¹ * subsetSum D Finset.univ)
      = 3 + Matrix.trace W⁻¹ := by
    rw [hSW, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add,
      Matrix.nonsing_inv_mul W hu, Matrix.trace_one]
    norm_num
  rw [hsplit, hall, htr, hweighted]
  ring


/-! ## 5. The pivot cap -/

/-- **The pivot cap.**  Every atom's six-set pivot is capped by its inverse
co-weight: `(1 − t_c)·g_cᵀ W⁻¹ g_c ≤ 1`.  Dropping the other terms of the
projection identity leaves `P_cc ≥ (1−t_c)·P_cc²`. -/
theorem sixSet_pivot_cap (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hPD : (subsetSum D Finset.univ - 1).PosDef) (c : Fin m) :
    (1 - D.weight c)
        * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c)) ≤ 1 := by
  classical
  have hWsymm : (subsetSum D Finset.univ - 1)ᵀ = subsetSum D Finset.univ - 1 :=
    transpose_subsetSum_sub_one D Finset.univ
  have hWinvsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ
      = (subsetSum D Finset.univ - 1)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  have hproj := pivot_coweight_projection D hPD c c
  have hdiag : D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c)
      = ∑ c', (1 - D.weight c')
          * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c')) ^ 2 := by
    rw [← hproj]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [show D.atom c' ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c)
        = D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c') from
      dot_mulVec_comm hWinvsymm _ _]
    ring
  have hterm : (1 - D.weight c)
        * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c)) ^ 2
      ≤ D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c) := by
    conv_rhs => rw [hdiag]
    exact Finset.single_le_sum
      (f := fun c' => (1 - D.weight c')
        * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c')) ^ 2)
      (fun c' _ => mul_nonneg (by linarith [design_weight_lt_one D hm c'])
        (sq_nonneg _)) (Finset.mem_univ c)
  have hPnn : 0 ≤ D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c) := by
    rw [hdiag]
    exact Finset.sum_nonneg fun c' _ =>
      mul_nonneg (by linarith [design_weight_lt_one D hm c']) (sq_nonneg _)
  rcases eq_or_lt_of_le hPnn with heq | hpos
  · rw [← heq]
    norm_num
  · nlinarith [hterm, hpos]

end Gtz
