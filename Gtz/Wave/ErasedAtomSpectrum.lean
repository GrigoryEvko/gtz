import Gtz.Wave.PencilWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The erased-atom spectrum

On a `Z1`-proper corner the erased atom `g_x` is orthogonal to the two
inside atoms and has unit norm.  This module shows that the corner data
makes `g_x` an EXACT EIGENVECTOR of every weighted moment in sight, and
extracts the rigidity that the eigenvector forces on the dual readings.

The laws:

* `Gtz.corner_subsetSum_mulVec_erased` — the corner triple sum fixes the
  erased atom, and the corner gap kills it.
* `Gtz.corner_weightedComplement_eigen` — THE EIGENVECTOR LAW: the
  weighted outside moment `N = Σ_{d∉C} t_d·g_dg_dᵀ` obeys
  `N·g_x = (1−t_x)·g_x`.  Parseval plus the two orthogonalities and the
  unit norm, nothing else.
* `Gtz.weightedComplement_det_eigen` / `Gtz.weightedComplement_adjugate_eigen`
  — the determinant and adjugate transports of the eigenvector: `1−t_x`
  is a root of the characteristic polynomial of `N`, and the adjugate
  reads the complementary product on `g_x`.
* `Gtz.corner_outsideDual_reading` — THE DUAL RIGIDITY at `(6,3)`: the
  unweighted-outside dual reading of the erased atom is pinned by the
  weights, `(1−t_x)·(g_dᵀMo⁻¹g_x) = t_d·(g_d·g_x)` for each outside `d`.
* `Gtz.corner_erasedDual_quota` — the quota: `(1−t_x)²·(g_xᵀMo⁻¹g_x)
  = Σ_d t_d²·(g_d·g_x)²`.
* `Gtz.bothLight_y_floor_iff_z_floor` — ON THE BOTH-LIGHT CELL THE
  `z`-FLOOR IS FREE: at two positive definite four-set gaps the `y`-floor
  and the `z`-floor are the same statement, both equal to the sign of the
  outside gap determinant.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The erased atom under the corner sums -/

/-- **The corner triple sum fixes the erased atom.**  Unit norm and the two
orthogonalities alone: `S_C·g_x = g_x`. -/
theorem corner_subsetSum_mulVec_erased {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ D.atom x = D.atom x := by
  rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton,
    Matrix.add_mulVec, Matrix.add_mulVec,
    show atomMatrix (D.atom x) *ᵥ D.atom x
      = (D.atom x ⬝ᵥ D.atom x) • D.atom x from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom y) *ᵥ D.atom x
      = (D.atom y ⬝ᵥ D.atom x) • D.atom y from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom z) *ᵥ D.atom x
      = (D.atom z ⬝ᵥ D.atom x) • D.atom z from vecMulVec_mulVec_eq _ _ _,
    dotProduct_comm (D.atom y), dotProduct_comm (D.atom z),
    hxunit, hxy0, hxz0]
  simp

/-- **The corner gap kills the erased atom**: `(S_C − 1)·g_x = 0`. -/
theorem corner_gap_mulVec_erased {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ D.atom x = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec,
    corner_subsetSum_mulVec_erased D hxy hxz hyz hxunit hxy0 hxz0, sub_self]

/-! ## 2. The eigenvector law -/

/-- **THE EIGENVECTOR LAW.**  The weighted outside moment has the erased
atom as an exact eigenvector, at eigenvalue one minus the erased weight:

  `(Σ_{d ∈ Cᶜ} t_d·g_dg_dᵀ)·g_x = (1 − t_x)·g_x` .

Parseval writes the outside moment as the identity minus the weighted
inside moment; the unit norm and the two orthogonalities collapse the
inside action on `g_x` to `t_x·g_x`. -/
theorem corner_weightedComplement_eigen {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d • atomMatrix (D.atom d)) *ᵥ D.atom x
      = (1 - D.weight x) • D.atom x := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun c => D.weight c • atomMatrix (D.atom c))
  rw [D.isParseval] at hsplit
  have hout : (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d • atomMatrix (D.atom d))
      = 1 - ∑ c ∈ ({x, y, z} : Finset (Fin m)),
          D.weight c • atomMatrix (D.atom c) := by
    rw [← hsplit]
    abel
  rw [hout, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec,
    show atomMatrix (D.atom x) *ᵥ D.atom x
      = (D.atom x ⬝ᵥ D.atom x) • D.atom x from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom y) *ᵥ D.atom x
      = (D.atom y ⬝ᵥ D.atom x) • D.atom y from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom z) *ᵥ D.atom x
      = (D.atom z ⬝ᵥ D.atom x) • D.atom z from vecMulVec_mulVec_eq _ _ _,
    dotProduct_comm (D.atom y), dotProduct_comm (D.atom z),
    hxunit, hxy0, hxz0]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The weighted inside moment scales the erased atom by its own
weight**: `(t_x·G_x + t_y·G_y + t_z·G_z)·g_x = t_x·g_x`. -/
theorem corner_weightedInside_eigen {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m}
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    (D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
        + D.weight z • atomMatrix (D.atom z)) *ᵥ D.atom x
      = D.weight x • D.atom x := by
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec,
    show atomMatrix (D.atom x) *ᵥ D.atom x
      = (D.atom x ⬝ᵥ D.atom x) • D.atom x from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom y) *ᵥ D.atom x
      = (D.atom y ⬝ᵥ D.atom x) • D.atom y from vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom z) *ᵥ D.atom x
      = (D.atom z ⬝ᵥ D.atom x) • D.atom z from vecMulVec_mulVec_eq _ _ _,
    dotProduct_comm (D.atom y), dotProduct_comm (D.atom z),
    hxunit, hxy0, hxz0]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 3. The determinant and adjugate transports -/

/-- **THE CHARACTERISTIC ROOT.**  One minus the erased weight is a root of
the characteristic polynomial of the weighted outside moment. -/
theorem weightedComplement_det_eigen {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    ((∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d • atomMatrix (D.atom d))
      - (1 - D.weight x) • 1).det = 0 := by
  by_contra hdet
  have hker : ((∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d • atomMatrix (D.atom d))
      - (1 - D.weight x) • 1) *ᵥ D.atom x = 0 := by
    rw [Matrix.sub_mulVec,
      corner_weightedComplement_eigen D hxy hxz hyz hxunit hxy0 hxz0,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hzero := Matrix.eq_zero_of_mulVec_eq_zero hdet hker
  rw [hzero] at hxunit
  simp at hxunit

/-- **THE ADJUGATE TRANSPORT.**  At an invertible weighted outside moment
the adjugate reads the complementary eigenvalue product on the erased atom:

  `(1 − t_x)·(adj N·g_x) = det N·g_x` . -/
theorem weightedComplement_adjugate_eigen {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0)
    (hdet : (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.weight d • atomMatrix (D.atom d)).det ≠ 0) :
    (1 - D.weight x) • ((∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d • atomMatrix (D.atom d)).adjugate *ᵥ D.atom x)
      = (∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d • atomMatrix (D.atom d)).det • D.atom x := by
  classical
  set N : Matrix (Fin 3) (Fin 3) ℝ :=
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d • atomMatrix (D.atom d) with hNDef
  have heig : N *ᵥ D.atom x = (1 - D.weight x) • D.atom x := by
    rw [hNDef]
    exact corner_weightedComplement_eigen D hxy hxz hyz hxunit hxy0 hxz0
  have happ : N *ᵥ ((1 - D.weight x) • (N.adjugate *ᵥ D.atom x))
      = N *ᵥ (N.det • D.atom x) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, heig]
    rw [smul_comm]
  have hdiff : N *ᵥ ((1 - D.weight x) • (N.adjugate *ᵥ D.atom x)
      - N.det • D.atom x) = 0 := by
    rw [Matrix.mulVec_sub, happ, sub_self]
  have hzero := Matrix.eq_zero_of_mulVec_eq_zero hdet hdiff
  rw [sub_eq_zero] at hzero
  exact hzero

/-! ## 4. The dual rigidity at `(6,3)` -/

/-- **THE DUAL RIGIDITY.**  At `(6,3)` the outside atoms are a basis and
the eigenvector law pins every dual reading of the erased atom against the
UNWEIGHTED outside sum `Mo`:

  `(1 − t_x)·(g_dᵀMo⁻¹g_x) = t_d·(g_d·g_x)`  for each outside atom `d`.

The dual reading against the unweighted geometry is the weighted plain
reading, rescaled by the eigenvalue.  Division-free. -/
theorem corner_outsideDual_reading (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin 6))).PosDef)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    ∀ j : Fin 3,
      (1 - D.weight x)
          * (D.atom (![d4, d5, d6] j) ⬝ᵥ
            ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ D.atom x))
        = D.weight (![d4, d5, d6] j)
            * (D.atom (![d4, d5, d6] j) ⬝ᵥ D.atom x) := by
  classical
  set Mo : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({d4, d5, d6} : Finset (Fin 6)) with hMoDef
  set V : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun i j => D.atom (![d4, d5, d6] j) i with hVDef
  have hVVt : V * Vᵀ = Mo := by
    rw [hMoDef, subsetSum, Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton]
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hVDef,
      Matrix.of_apply, Fin.sum_univ_three, atomMatrix,
      Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    ring
  have hdetV : IsUnit V.det := by
    have hdet : Mo.det = V.det * V.det := by
      rw [← hVVt, Matrix.det_mul, Matrix.det_transpose]
    have hpos := hMo.det_pos
    rw [hdet] at hpos
    exact isUnit_iff_ne_zero.mpr fun hzero => by
      rw [hzero, mul_zero] at hpos
      exact lt_irrefl 0 hpos
  have hVinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdetV
  have hcol : ∀ j : Fin 3, V *ᵥ Pi.single j 1 = D.atom (![d4, d5, d6] j) := by
    intro j
    rw [Matrix.mulVec_single_one]
    ext i
    simp [hVDef]
  have hetaOut : ∀ j : Fin 3,
      V⁻¹ *ᵥ D.atom (![d4, d5, d6] j) = Pi.single j 1 := by
    intro j
    rw [← hcol j, Matrix.mulVec_mulVec, hVinv, Matrix.one_mulVec]
  -- the weighted outside sum in chart form
  have hNVt : V * Matrix.diagonal
        ![D.weight d4, D.weight d5, D.weight d6] * Vᵀ
      = D.weight d4 • atomMatrix (D.atom d4)
        + D.weight d5 • atomMatrix (D.atom d5)
        + D.weight d6 • atomMatrix (D.atom d6) := by
    rw [diagonal_eq_sum_single_atoms]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    rw [congr_atomMatrix, congr_atomMatrix, congr_atomMatrix,
      show V *ᵥ Pi.single 0 1 = D.atom d4 from by simpa using hcol 0,
      show V *ᵥ Pi.single 1 1 = D.atom d5 from by simpa using hcol 1,
      show V *ᵥ Pi.single 2 1 = D.atom d6 from by simpa using hcol 2]
  -- the eigen law at the enumerated complement
  have heig63 : (D.weight d4 • atomMatrix (D.atom d4)
      + D.weight d5 • atomMatrix (D.atom d5)
      + D.weight d6 • atomMatrix (D.atom d6)) *ᵥ D.atom x
      = (1 - D.weight x) • D.atom x := by
    have h := corner_weightedComplement_eigen D hxy hxz hyz hxunit hxy0 hxz0
    rw [hcompl, Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton,
      ← add_assoc] at h
    exact h
  -- the pinned scaled dual vector
  have hMoInvUnit : IsUnit Mo.det := isUnit_iff_ne_zero.mpr
    (ne_of_gt hMo.det_pos)
  have hscaled : Mo⁻¹ *ᵥ ((1 - D.weight x) • D.atom x)
      = (Mo⁻¹ * (V * Matrix.diagonal
          ![D.weight d4, D.weight d5, D.weight d6] * Vᵀ)) *ᵥ D.atom x := by
    rw [hNVt, ← heig63, Matrix.mulVec_mulVec]
  have hMoInvN : Mo⁻¹ * (V * Matrix.diagonal
        ![D.weight d4, D.weight d5, D.weight d6] * Vᵀ)
      = (V⁻¹)ᵀ * (Matrix.diagonal
          ![D.weight d4, D.weight d5, D.weight d6] * Vᵀ) := by
    rw [← hVVt, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc ((V⁻¹)ᵀ) V⁻¹ V, hVinv, Matrix.mul_one]
  intro j
  have hread : D.atom (![d4, d5, d6] j) ⬝ᵥ
      (Mo⁻¹ *ᵥ ((1 - D.weight x) • D.atom x))
      = D.weight (![d4, d5, d6] j) * (D.atom (![d4, d5, d6] j) ⬝ᵥ D.atom x) := by
    rw [hscaled, hMoInvN, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_transpose, hetaOut j]
    have hdiagV : (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
        * Vᵀ) *ᵥ D.atom x
        = fun i => (![D.weight d4, D.weight d5, D.weight d6] : Fin 3 → ℝ) i
            * (D.atom (![d4, d5, d6] i) ⬝ᵥ D.atom x) := by
      funext i
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      congr 1
    rw [hdiagV]
    have hsingle : ∀ w : Fin 3 → ℝ, Pi.single j (1 : ℝ) ⬝ᵥ w = w j := by
      intro w
      simp [dotProduct, Pi.single_apply]
    rw [hsingle]
    fin_cases j <;> simp
  rw [Matrix.mulVec_smul] at hread
  rw [← hread, dotProduct_smul, smul_eq_mul]

/-- **THE ERASED DUAL QUOTA.**  The `Mo`-dual self-reading of the erased
atom is the squared-weighted cross energy with the outside atoms:

  `(1 − t_x)²·(g_xᵀMo⁻¹g_x) = Σ_d t_d²·(g_d·g_x)²` . -/
theorem corner_erasedDual_quota (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin 6))).PosDef)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    (1 - D.weight x) ^ 2
        * (D.atom x ⬝ᵥ
          ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ D.atom x))
      = D.weight d4 ^ 2 * (D.atom d4 ⬝ᵥ D.atom x) ^ 2
        + D.weight d5 ^ 2 * (D.atom d5 ⬝ᵥ D.atom x) ^ 2
        + D.weight d6 ^ 2 * (D.atom d6 ⬝ᵥ D.atom x) ^ 2 := by
  have hdual := corner_outsideDual_reading D hxy hxz hyz h45 h46 h56 hcompl
    hMo hxunit hxy0 hxz0
  have heig63 : (D.weight d4 • atomMatrix (D.atom d4)
      + D.weight d5 • atomMatrix (D.atom d5)
      + D.weight d6 • atomMatrix (D.atom d6)) *ᵥ D.atom x
      = (1 - D.weight x) • D.atom x := by
    have h := corner_weightedComplement_eigen D hxy hxz hyz hxunit hxy0 hxz0
    rw [hcompl, Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton,
      ← add_assoc] at h
    exact h
  have h4 := hdual 0
  have h5 := hdual 1
  have h6 := hdual 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h4 h5 h6
  -- expand the scaled self-reading through the eigen law
  have hexp : (1 - D.weight x) ^ 2
      * (D.atom x ⬝ᵥ
        ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ D.atom x))
      = ((1 - D.weight x) • D.atom x) ⬝ᵥ
          ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ
            ((1 - D.weight x) • D.atom x)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  rw [hexp, ← heig63]
  -- the left factor distributes into weighted plain readings
  have hleft : ((D.weight d4 • atomMatrix (D.atom d4)
      + D.weight d5 • atomMatrix (D.atom d5)
      + D.weight d6 • atomMatrix (D.atom d6)) *ᵥ D.atom x) ⬝ᵥ
        ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ
          ((D.weight d4 • atomMatrix (D.atom d4)
            + D.weight d5 • atomMatrix (D.atom d5)
            + D.weight d6 • atomMatrix (D.atom d6)) *ᵥ D.atom x))
      = D.weight d4 * (D.atom d4 ⬝ᵥ D.atom x)
          * (D.atom d4 ⬝ᵥ
            ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ
              ((D.weight d4 • atomMatrix (D.atom d4)
                + D.weight d5 • atomMatrix (D.atom d5)
                + D.weight d6 • atomMatrix (D.atom d6)) *ᵥ D.atom x)))
        + D.weight d5 * (D.atom d5 ⬝ᵥ D.atom x)
          * (D.atom d5 ⬝ᵥ
            ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ
              ((D.weight d4 • atomMatrix (D.atom d4)
                + D.weight d5 • atomMatrix (D.atom d5)
                + D.weight d6 • atomMatrix (D.atom d6)) *ᵥ D.atom x)))
        + D.weight d6 * (D.atom d6 ⬝ᵥ D.atom x)
          * (D.atom d6 ⬝ᵥ
            ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ
              ((D.weight d4 • atomMatrix (D.atom d4)
                + D.weight d5 • atomMatrix (D.atom d5)
                + D.weight d6 • atomMatrix (D.atom d6)) *ᵥ D.atom x))) := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec,
      show atomMatrix (D.atom d4) *ᵥ D.atom x
        = (D.atom d4 ⬝ᵥ D.atom x) • D.atom d4 from vecMulVec_mulVec_eq _ _ _,
      show atomMatrix (D.atom d5) *ᵥ D.atom x
        = (D.atom d5 ⬝ᵥ D.atom x) • D.atom d5 from vecMulVec_mulVec_eq _ _ _,
      show atomMatrix (D.atom d6) *ᵥ D.atom x
        = (D.atom d6 ⬝ᵥ D.atom x) • D.atom d6 from vecMulVec_mulVec_eq _ _ _]
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  rw [hleft, heig63]
  -- each dual reading collapses through the rigidity
  rw [Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [h4, h5, h6]
  ring

/-! ## 5. The free `z`-floor of the both-light cell -/

/-- **THE `z`-FLOOR IS FREE.**  At two positive definite four-set gaps the
`y`-floor and the `z`-floor are the SAME statement: each is equivalent to a
nonpositive outside gap determinant, because erasure of the inserted member
lands on the same outside triple.  The both-light clause system therefore
carries the `z`-floor at no cost. -/
theorem bothLight_y_floor_iff_z_floor {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m}
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef) :
    (1 ≤ D.atom y ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom y))
      ↔ (1 ≤ D.atom z ⬝ᵥ
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) := by
  classical
  have hynot : y ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  have hznot : z ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  rw [member_floor_iff_gapDet_erase_nonpos D hAy (Finset.mem_insert_self y _),
    member_floor_iff_gapDet_erase_nonpos D hAz (Finset.mem_insert_self z _),
    Finset.erase_insert hynot, Finset.erase_insert hznot]

/-! ## 6. The corner-facing forms -/

/-- The eigenvector law with orthogonality and unit norm supplied by the
corner equation. -/
theorem corner_oneAxisZero_weightedComplement_eigen (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    (∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d • atomMatrix (D.atom d)) *ᵥ D.atom x
      = (1 - D.weight x) • D.atom x := by
  obtain ⟨hxy0, hxz0⟩ :=
    corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam hunit hgap hax
  exact corner_weightedComplement_eigen D hxy hxz hyz
    (corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam hunit hgap
      (by simp) hax)
    hxy0 hxz0

/-- The dual rigidity with the corner inputs supplied by the corner
equation. -/
theorem corner_oneAxisZero_outsideDual_reading (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin 6))).PosDef)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    ∀ j : Fin 3,
      (1 - D.weight x)
          * (D.atom (![d4, d5, d6] j) ⬝ᵥ
            ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹ *ᵥ D.atom x))
        = D.weight (![d4, d5, d6] j)
            * (D.atom (![d4, d5, d6] j) ⬝ᵥ D.atom x) := by
  obtain ⟨hxy0, hxz0⟩ :=
    corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam hunit hgap hax
  exact corner_outsideDual_reading D hxy hxz hyz h45 h46 h56 hcompl hMo
    (corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam hunit hgap
      (by simp) hax)
    hxy0 hxz0

end Gtz
