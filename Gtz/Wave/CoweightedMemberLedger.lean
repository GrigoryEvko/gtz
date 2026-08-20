import Gtz.Wave.HeavyInsideDeterminantForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-!
# The higher ledgers of a subset

Parseval writes the COWEIGHTED member sum of any subset as its gap plus the
excluded atoms (`Gtz.coweighted_member_sum_eq`):

  `Σ_{a∈F}(1 − t_a)·g_ag_aᵀ = (S_F − 1) + Σ_{c∉F} t_c·g_cg_cᵀ` .

The campaign has used only the TRACE of this identity — the coweight ledger
`Σ_{a∈F}(1−t_a)r_a = 3 + Σ_{c∉F}t_c r_c`.  A `3×3` symmetric matrix has
THREE invariants, and the other two are new laws.

Its DETERMINANT is the second one.  On the left Cauchy-Binet turns the
determinant of a weighted sum of four rank-one atoms into a positive
combination of squared triple products (`Gtz.det_sum_four_atomMatrix`):

  `det(Σ_a w_a v_av_aᵀ) = Σ_{a<b<c} w_aw_bw_c·((v_a × v_b)·v_c)²` ,

and every summand is the Gram determinant of a TRIPLE of members — the very
objects whose sign is the member floor
(`Gtz.member_floor_iff_gapDet_erase_nonpos`).  On the right the landed
three-atom expansion turns `det(A + t_x g_xg_xᵀ + t_z g_zg_zᵀ)` into the gap
determinant, the two adjugate readings of the excluded atoms, and one cross
term (`Gtz.coweighted_member_det_law`):

  `det A + t_x·g_xᵀ(adj A)g_x + t_z·g_zᵀ(adj A)g_z
     + t_x t_z·(g_x × g_z)ᵀ A (g_x × g_z)` .

## What is new

The trace ledger sees only the DIAGONAL readings.  The determinant ledger
sees the triple products, so it couples the member floors to the excluded
pair with no inverse anywhere, and every term it carries is a square.  It is
the first law of the campaign that is quadratic in the excluded weights and
still exact.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. A rank-one atom has no determinant and no adjugate -/

/-- A rank-one atom of `ℝ³` is singular. -/
theorem det_atomMatrix_fin_three (v : Fin 3 → ℝ) : (atomMatrix v).det = 0 := by
  simp [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- Every `2×2` minor of a rank-one atom of `ℝ³` vanishes, so its adjugate is
zero. -/
theorem adjugate_atomMatrix_fin_three (v : Fin 3 → ℝ) :
    (atomMatrix v).adjugate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, atomMatrix, Matrix.vecMulVec_apply] <;> ring

/-- A weighted rank-one atom reads a vector as its weighted squared pairing. -/
theorem quadForm_smul_atomMatrix (w : ℝ) (v u : Fin 3 → ℝ) :
    u ⬝ᵥ ((w • atomMatrix v) *ᵥ u) = w * (u ⬝ᵥ v) ^ 2 := by
  simp [atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.smul_apply]
  ring

/-! ## 2. Cauchy-Binet at four atoms -/

/-- **CAUCHY-BINET AT FOUR ATOMS.**  The determinant of a weighted sum of
four rank-one atoms of `ℝ³` is the positive combination of the squared
triple products of the four triples:

  `det(Σ_a w_a v_av_aᵀ) = Σ_{a<b<c} w_aw_bw_c·((v_a × v_b)·v_c)²` .

Every summand is a square, so no term cancels. -/
theorem det_sum_four_atomMatrix (w₁ w₂ w₃ w₄ : ℝ) (v₁ v₂ v₃ v₄ : Fin 3 → ℝ) :
    (w₁ • atomMatrix v₁ + w₂ • atomMatrix v₂ + w₃ • atomMatrix v₃
      + w₄ • atomMatrix v₄).det
      = w₁ * w₂ * w₃ * (crossProduct v₁ v₂ ⬝ᵥ v₃) ^ 2
        + w₁ * w₂ * w₄ * (crossProduct v₁ v₂ ⬝ᵥ v₄) ^ 2
        + w₁ * w₃ * w₄ * (crossProduct v₁ v₃ ⬝ᵥ v₄) ^ 2
        + w₂ * w₃ * w₄ * (crossProduct v₂ v₃ ⬝ᵥ v₄) ^ 2 := by
  have hshape : w₁ • atomMatrix v₁ + w₂ • atomMatrix v₂ + w₃ • atomMatrix v₃
      + w₄ • atomMatrix v₄
      = (w₄ • atomMatrix v₄) + w₁ • atomMatrix v₁ + w₂ • atomMatrix v₂
        + w₃ • atomMatrix v₃ := by abel
  rw [hshape, det_add_three_atomMatrix_fin_three (w₄ • atomMatrix v₄) w₁ w₂ w₃ v₁ v₂ v₃]
  rw [Matrix.det_smul, det_atomMatrix_fin_three, Matrix.adjugate_smul,
    adjugate_atomMatrix_fin_three]
  simp only [smul_zero, Matrix.zero_mulVec, dotProduct_zero,
    quadForm_smul_atomMatrix, mul_zero, add_zero, zero_add]
  ring

/-! ## 3. The coweighted member sum and its determinant -/

/-- **THE COWEIGHTED MEMBER SUM.**  Parseval writes the coweighted members of
a subset as its gap plus the excluded atoms. -/
theorem coweighted_member_sum_eq (D : WeightedDesign m 3) (F : Finset (Fin m)) :
    ∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)
      = (subsetSum D F - 1) + ∑ c ∈ Fᶜ, D.weight c • atomMatrix (D.atom c) := by
  rw [subsetSum_sub_one_eq_insider_sub_outsider D F]
  abel

/-- **THE DETERMINANT LEDGER.**  When exactly two atoms are excluded, the
determinant of the coweighted member sum expands with no inverse:

  `det(Σ_{a∈F}(1−t_a)g_ag_aᵀ) = det A + t_x·g_xᵀ(adj A)g_x + t_z·g_zᵀ(adj A)g_z
      + t_x t_z·(g_x × g_z)ᵀ A (g_x × g_z)` ,  `A = S_F − 1` . -/
theorem coweighted_member_det_law (D : WeightedDesign m 3) (F : Finset (Fin m))
    {x z : Fin m} (hxz : x ≠ z) (hcompl : (Fᶜ : Finset (Fin m)) = {x, z}) :
    (∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)).det
      = (subsetSum D F - 1).det
        + (D.weight x
              * (D.atom x ⬝ᵥ ((subsetSum D F - 1).adjugate *ᵥ D.atom x))
            + D.weight z
              * (D.atom z ⬝ᵥ ((subsetSum D F - 1).adjugate *ᵥ D.atom z)))
        + D.weight x * D.weight z
            * (crossProduct (D.atom x) (D.atom z)
                ⬝ᵥ ((subsetSum D F - 1)
                    *ᵥ crossProduct (D.atom x) (D.atom z))) := by
  classical
  have hxs : x ∉ ({z} : Finset (Fin m)) := by simp [hxz]
  have hsum := coweighted_member_sum_eq D F
  rw [hcompl, Finset.sum_insert hxs, Finset.sum_singleton] at hsum
  have hexp := det_add_three_atomMatrix_fin_three (subsetSum D F - 1)
    (D.weight x) (D.weight z) 0 (D.atom x) (D.atom z) (D.atom x)
  rw [hsum]
  have hshape : subsetSum D F - 1
        + (D.weight x • atomMatrix (D.atom x) + D.weight z • atomMatrix (D.atom z))
      = subsetSum D F - 1 + D.weight x • atomMatrix (D.atom x)
        + D.weight z • atomMatrix (D.atom z) + (0 : ℝ) • atomMatrix (D.atom x) := by
    rw [← add_assoc]
    simp
  rw [hshape, hexp]
  ring

/-! ## 4. The master identity and the co-annihilator fixed point

The relation `P·Dm·P = P` is the SQUARE of a sharper one.  Parseval gives
`V·Dm·Vᵀ = A` at once, so

  `P · Dm · Vᵀ = Vᵀ A⁻¹ (V Dm Vᵀ) = Vᵀ A⁻¹ A = Vᵀ` .

Reading it against a probe `w ∈ ℝ³` turns it into one scalar law for every
atom and every probe (`Gtz.reading_defect_probe`):

  `Σ_b (δ_b − t_b)·P_ab·(g_b·w) = g_a·w` .

When the probe ANNIHILATES every excluded atom the negative half drops out,
and the coweighted reading operator fixes the pairing vector
(`Gtz.coweighted_reading_fixed_point`):

  `Σ_{b∈F}(1 − t_b)·P_ab·(g_b·w) = g_a·w` .

At the corner the excluded pair is `{x, z}` and the cross product `g_x × g_z`
annihilates both, so the vector of TRIPLE PRODUCTS `[g_b, g_x, g_z]` is a
fixed point of the coweighted reading operator
(`Gtz.corner_tripleProduct_fixed_point`).  That is a weight-carrying linear
law with no counterpart in the campaign: the trace ledger sees only the
diagonal, and this sees the whole coweighted row against a distinguished
direction. -/

/-- **THE MASTER IDENTITY.**  `P · Dm · Vᵀ = Vᵀ` — the reading matrix
composed with the weight defect fixes the transposed atom matrix.  Squaring
it against `A⁻¹V` on the right gives `P·Dm·P = P`. -/
theorem reading_defect_atoms (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) :
    readingMatrix D F * weightDefect D F * (atomsMatrix D)ᵀ = (atomsMatrix D)ᵀ := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  set V : Matrix (Fin 3) (Fin m) ℝ := atomsMatrix D with hV
  have hgap : V * weightDefect D F * Vᵀ = A := by
    rw [hV, hA]; exact atoms_weightDefect_eq_gap D F
  calc readingMatrix D F * weightDefect D F * Vᵀ
      = Vᵀ * A⁻¹ * (V * weightDefect D F * Vᵀ) := by
        simp only [readingMatrix, ← hV, ← hA, Matrix.mul_assoc]
    _ = Vᵀ * (A⁻¹ * A) := by rw [hgap]; simp only [Matrix.mul_assoc]
    _ = Vᵀ := by rw [Matrix.nonsing_inv_mul A hdet, Matrix.mul_one]

/-- **THE PROBE FORM.**  One scalar law for every atom and every probe:

  `Σ_b (δ_b − t_b)·P_ab·(g_b·w) = g_a·w` . -/
theorem reading_defect_probe (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) (a : Fin m) (w : Fin 3 → ℝ) :
    ∑ b, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
        * (readingMatrix D F a b * (D.atom b ⬝ᵥ w))
      = D.atom a ⬝ᵥ w := by
  classical
  have hcol : ∀ i : Fin 3,
      ∑ b, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
          * (readingMatrix D F a b * D.atom b i)
        = D.atom a i := by
    intro i
    have h := congrFun (congrFun (reading_defect_atoms D F hdet) a) i
    rw [Matrix.mul_apply] at h
    simp only [weightDefect, Matrix.mul_diagonal, atomsMatrix,
      Matrix.transpose_apply, Matrix.of_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hswap : ∑ b, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
        * (readingMatrix D F a b * (D.atom b ⬝ᵥ w))
      = ∑ i, (∑ b, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
          * (readingMatrix D F a b * D.atom b i)) * w i := by
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hswap]
  exact Finset.sum_congr rfl fun i _ => by rw [hcol i]

/-- **THE CO-ANNIHILATOR FIXED POINT.**  A probe that annihilates every
EXCLUDED atom is fixed by the coweighted reading operator:

  `Σ_{b∈F}(1 − t_b)·P_ab·(g_b·w) = g_a·w` . -/
theorem coweighted_reading_fixed_point (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hdet : IsUnit (subsetSum D F - 1).det)
    (w : Fin 3 → ℝ) (hw : ∀ c ∉ F, D.atom c ⬝ᵥ w = 0) (a : Fin m) :
    ∑ b ∈ F, (1 - D.weight b)
        * (readingMatrix D F a b * (D.atom b ⬝ᵥ w))
      = D.atom a ⬝ᵥ w := by
  classical
  rw [← reading_defect_probe D F hdet a w, ← Finset.sum_add_sum_compl F]
  have h1 : ∀ b ∈ F, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
      * (readingMatrix D F a b * (D.atom b ⬝ᵥ w))
      = (1 - D.weight b) * (readingMatrix D F a b * (D.atom b ⬝ᵥ w)) := by
    intro b hb; simp only [hb, ite_true]
  have h2 : ∀ b ∈ Fᶜ, ((if b ∈ F then (1 : ℝ) else 0) - D.weight b)
      * (readingMatrix D F a b * (D.atom b ⬝ᵥ w)) = 0 := by
    intro b hb
    rw [hw b (Finset.mem_compl.mp hb)]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero,
    add_zero]

/-- **THE TRIPLE PRODUCTS ARE A FIXED POINT.**  When exactly two atoms are
excluded, their cross product annihilates both, so the vector of triple
products against the excluded pair is fixed by the coweighted reading
operator:

  `Σ_{b∈F}(1 − t_b)·P_ab·[g_b, g_x, g_z] = [g_a, g_x, g_z]` . -/
theorem corner_tripleProduct_fixed_point (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hdet : IsUnit (subsetSum D F - 1).det)
    {x z : Fin m} (hxz : x ≠ z) (hcompl : (Fᶜ : Finset (Fin m)) = {x, z})
    (a : Fin m) :
    ∑ b ∈ F, (1 - D.weight b)
        * (readingMatrix D F a b
            * (D.atom b ⬝ᵥ crossProduct (D.atom x) (D.atom z)))
      = D.atom a ⬝ᵥ crossProduct (D.atom x) (D.atom z) := by
  classical
  refine coweighted_reading_fixed_point D F hdet _ (fun c hc => ?_) a
  have hcmem : c ∈ (Fᶜ : Finset (Fin m)) := Finset.mem_compl.mpr hc
  rw [hcompl] at hcmem
  rcases Finset.mem_insert.mp hcmem with rfl | hc'
  · exact dot_self_cross (D.atom c) (D.atom z)
  · rw [Finset.mem_singleton.mp hc']
    exact dot_cross_self (D.atom x) (D.atom z)

/-! ## 5. The adjugate compound and the reading form of the ledger -/

/-- **THE ADJUGATE COMPOUND.**  For any `3×3` matrix the second compound of
the adjugate is the determinant times the matrix itself, read on a cross
product:

  `det M · ((u × v)ᵀ M (u × v))
     = (uᵀ(adj M)u)(vᵀ(adj M)v) − (uᵀ(adj M)v)(vᵀ(adj M)u)` .

A polynomial identity: no inverse, no positivity. -/
theorem det_mul_cross_quadForm (M : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) :
    M.det * (crossProduct u v ⬝ᵥ (M *ᵥ crossProduct u v))
      = (u ⬝ᵥ (M.adjugate *ᵥ u)) * (v ⬝ᵥ (M.adjugate *ᵥ v))
        - (u ⬝ᵥ (M.adjugate *ᵥ v)) * (v ⬝ᵥ (M.adjugate *ᵥ u)) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  ring

/-! ## 6. The overshoot -/

/-- **THE COWEIGHTED MEMBERS OVERSHOOT THE GAP.**  At a positive definite gap
with exactly two excluded atoms, the determinant of the coweighted member sum
is at least the gap determinant: the two adjugate readings and the cross term
are all nonnegative. -/
theorem coweighted_member_det_ge_gapDet (D : WeightedDesign m 3)
    (F : Finset (Fin m)) {x z : Fin m} (hxz : x ≠ z)
    (hcompl : (Fᶜ : Finset (Fin m)) = {x, z})
    (hpd : (subsetSum D F - 1).PosDef) :
    (subsetSum D F - 1).det
      ≤ (∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)).det := by
  classical
  have hdet : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hadj : (subsetSum D F - 1).adjugate
      = (subsetSum D F - 1).det • (subsetSum D F - 1)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hdet, one_smul]
  have hsm : ∀ (c : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ),
      v ⬝ᵥ ((c • M) *ᵥ v) = c * (v ⬝ᵥ (M *ᵥ v)) := by
    intro c M v
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hpsd := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpd.posSemidef).2
  have hx : 0 ≤ D.weight x
      * (D.atom x ⬝ᵥ ((subsetSum D F - 1).adjugate *ᵥ D.atom x)) := by
    rw [hadj, hsm]
    exact mul_nonneg (D.weight_pos x).le
      (mul_nonneg hpd.det_pos.le (inverseForm_nonneg hpd (D.atom x)))
  have hz : 0 ≤ D.weight z
      * (D.atom z ⬝ᵥ ((subsetSum D F - 1).adjugate *ᵥ D.atom z)) := by
    rw [hadj, hsm]
    exact mul_nonneg (D.weight_pos z).le
      (mul_nonneg hpd.det_pos.le (inverseForm_nonneg hpd (D.atom z)))
  have hcross : 0 ≤ D.weight x * D.weight z
      * (crossProduct (D.atom x) (D.atom z)
          ⬝ᵥ ((subsetSum D F - 1) *ᵥ crossProduct (D.atom x) (D.atom z))) :=
    mul_nonneg (mul_nonneg (D.weight_pos x).le (D.weight_pos z).le) (hpsd _)
  rw [coweighted_member_det_law D F hxz hcompl]
  linarith

/-! ## 7. The determinant ledger in reading coordinates

Dividing the determinant ledger by the gap determinant turns both sides into
readings.  Writing `τ = t_x r_x + t_z r_z` for the excluded reading total and
`π = t_x t_z (r_x r_z − P_xz²)` for the excluded reading Gram, the law is

  `det(Σ_{a∈F}(1−t_a)g_ag_aᵀ) = det(S_F − 1)·(1 + τ + π)` .

Combined with Cauchy-Binet at four atoms the left side is the coweighted sum
of the FOUR TRIPLE GRAM DETERMINANTS of the members, and by
`Gtz.member_floor_iff_gapDet_erase_nonpos` those four triples are exactly the
ones whose failure is the four member floors.  So the law couples the whole
floor system to the two excluded atoms in one equation.

It is the SECOND invariant of the coweighted member sum.  The campaign has
used only the first — the trace, which is the coweight ledger
`Σ_{a∈F}(1−t_a)r_a = 3 + τ`.  The third invariant is `Σ_{a<b}(1−t_a)(1−t_b)
(r_ar_b − P_ab²) = 3 + 2τ + π`, and the fourth is that the coweighted reading
matrix is singular.  Together they pin the whole characteristic polynomial of
the coweighted member reading matrix in terms of `τ` and `π` alone. -/

/-- The adjugate reading of a positive definite gap is the determinant times
the inverse reading. -/
theorem adjugate_reading (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hpd : (subsetSum D F - 1).PosDef) (g : Fin 3 → ℝ) :
    g ⬝ᵥ ((subsetSum D F - 1).adjugate *ᵥ g)
      = (subsetSum D F - 1).det * (g ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ g)) := by
  have hdet : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hadj : (subsetSum D F - 1).adjugate
      = (subsetSum D F - 1).det • (subsetSum D F - 1)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hdet, one_smul]
  rw [hadj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The adjugate cross reading of a positive definite gap. -/
theorem adjugate_cross_reading (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hpd : (subsetSum D F - 1).PosDef) (g h : Fin 3 → ℝ) :
    g ⬝ᵥ ((subsetSum D F - 1).adjugate *ᵥ h)
      = (subsetSum D F - 1).det * (g ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ h)) := by
  have hdet : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hadj : (subsetSum D F - 1).adjugate
      = (subsetSum D F - 1).det • (subsetSum D F - 1)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hdet, one_smul]
  rw [hadj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **THE CROSS TERM IS THE EXCLUDED READING GRAM.**  At a positive definite
gap the cross product of the two excluded atoms reads the gap as the
determinant times their reading Gram:

  `(g_x × g_z)ᵀ A (g_x × g_z) = det A · (r_x r_z − P_xz²)` . -/
theorem cross_quadForm_eq_readingGram (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hpd : (subsetSum D F - 1).PosDef) (g h : Fin 3 → ℝ) :
    crossProduct g h ⬝ᵥ ((subsetSum D F - 1) *ᵥ crossProduct g h)
      = (subsetSum D F - 1).det
        * ((g ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ g))
              * (h ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ h))
            - (g ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ h)) ^ 2) := by
  have hne : (subsetSum D F - 1).det ≠ 0 := ne_of_gt hpd.det_pos
  have hkey := det_mul_cross_quadForm (subsetSum D F - 1) g h
  rw [adjugate_reading D F hpd g, adjugate_reading D F hpd h,
    adjugate_cross_reading D F hpd g h, adjugate_cross_reading D F hpd h g,
    inv_reading_symm hpd h g] at hkey
  have hcancel : (subsetSum D F - 1).det
      * (crossProduct g h ⬝ᵥ ((subsetSum D F - 1) *ᵥ crossProduct g h))
      = (subsetSum D F - 1).det
        * ((subsetSum D F - 1).det
            * ((g ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ g))
                  * (h ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ h))
                - (g ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ h)) ^ 2)) := by
    rw [hkey]; ring
  exact mul_left_cancel₀ hne hcancel

/-- **THE DETERMINANT LEDGER, IN READINGS.**  The second invariant of the
coweighted member sum, with the excluded pair entering through its reading
total and its reading Gram:

  `det(Σ_{a∈F}(1−t_a)g_ag_aᵀ)
      = det A · (1 + t_x r_x + t_z r_z + t_x t_z (r_x r_z − P_xz²))` .

By `Gtz.det_sum_four_atomMatrix` the left side is the coweighted sum of the
four triple Gram determinants of the members, so this one equation ties every
member floor to the excluded pair. -/
theorem coweighted_member_det_reading_ledger (D : WeightedDesign m 3)
    (F : Finset (Fin m)) {x z : Fin m} (hxz : x ≠ z)
    (hcompl : (Fᶜ : Finset (Fin m)) = {x, z})
    (hpd : (subsetSum D F - 1).PosDef) :
    (∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)).det
      = (subsetSum D F - 1).det
        * (1
            + D.weight x
                * (D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom x))
            + D.weight z
                * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z))
            + D.weight x * D.weight z
                * ((D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom x))
                      * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z))
                    - (D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)) ^ 2)) := by
  rw [coweighted_member_det_law D F hxz hcompl,
    adjugate_reading D F hpd (D.atom x), adjugate_reading D F hpd (D.atom z),
    cross_quadForm_eq_readingGram D F hpd (D.atom x) (D.atom z)]
  ring

end Gtz
