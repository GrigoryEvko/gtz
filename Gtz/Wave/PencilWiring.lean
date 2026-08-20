import Gtz.Wave.TransverseFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The pencil wiring

The transverse floor and the frame bound are abstract pencil-frame laws.
The cell residuals are ambient.  This module lands the congruence that
carries the laws across: the chart that sends the three outside atoms to
the coordinate axes.

The chart is the column matrix `V` of the outside atoms.  Conjugation by
`V⁻¹` sends the weighted Parseval identity to the pencil master identity,
sends each four-set gap to its pencil form `1 − W + ηηᵀ`, sends the member
floors to the diagonal of one inverse, and sends the corner readings to
plain ambient dot products.  The seventh floor is the `y`-floor read
through the landed determinant downdate.

The headline (`Gtz.corner_bothLight_transverse_floor`) is the transverse
floor in fully ambient terms: on the both-light cell the seven floors
force the two dual-basis transverse energies at the rate of the two
smaller outside weights.  The companion (`Gtz.corner_scale_cap`) is the
ambient frame bound: the corner scale obeys `lam ≤ 1/t_y + 1/t_z − 2`, the
compactification of the corner arena.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The congruence kit -/

/-- Conjugation moves an atom through its vector: `M·ggᵀ·Mᵀ = (Mg)(Mg)ᵀ`. -/
theorem congr_atomMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) (g : Fin 3 → ℝ) :
    M * atomMatrix g * Mᵀ = atomMatrix (M *ᵥ g) := by
  ext i j
  simp only [atomMatrix, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The diagonal of a weight triple is the weighted sum of the coordinate
atoms. -/
theorem diagonal_eq_sum_single_atoms (t4 t5 t6 : ℝ) :
    Matrix.diagonal ![t4, t5, t6]
      = t4 • atomMatrix (Pi.single 0 1) + t5 • atomMatrix (Pi.single 1 1)
        + t6 • atomMatrix (Pi.single 2 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomMatrix, Matrix.vecMulVec_apply]

/-- A conjugated diagonal entry is a column reading. -/
theorem congr_entry (A M : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (Mᵀ * A * M) j j
      = (fun i => M i j) ⬝ᵥ (A *ᵥ fun i => M i j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

/-- A Gram-form reading is the squared length of the moved vector. -/
theorem quad_transpose_mul (M : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    a ⬝ᵥ ((Mᵀ * M) *ᵥ a) = (M *ᵥ a) ⬝ᵥ (M *ᵥ a) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

/-- Positive definiteness moves through an invertible congruence. -/
theorem posDef_congruence {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef)
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : IsUnit M.det) :
    (M * A * Mᵀ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      transpose_eq_of_isHermitian hA.1, ← Matrix.mul_assoc]
  · rw [star_trivial]
    have hform : x ⬝ᵥ ((M * A * Mᵀ) *ᵥ x)
        = (Mᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Mᵀ *ᵥ x)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
      ring
    have hwne : Mᵀ *ᵥ x ≠ 0 := by
      intro hcon
      apply hx
      have hinj : Function.Injective (Mᵀ).mulVec :=
        Matrix.mulVec_injective_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det _).mpr (by rwa [Matrix.det_transpose]))
      have hzero : Mᵀ *ᵥ x = Mᵀ *ᵥ 0 := by rw [Matrix.mulVec_zero]; exact hcon
      exact hinj hzero
    rw [hform]
    have h := hA.dotProduct_mulVec_pos hwne
    rwa [star_trivial] at h

/-- The inverse of an inverse-congruence is the transpose congruence of the
inverse. -/
theorem inv_congr_inv {A V : Matrix (Fin 3) (Fin 3) ℝ}
    (hV : IsUnit V.det) :
    (V⁻¹ * A * (V⁻¹)ᵀ)⁻¹ = Vᵀ * A⁻¹ * V := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hV, Matrix.nonsing_inv_nonsing_inv _
      (by rwa [Matrix.det_transpose]), Matrix.mul_assoc]

/-! ## 2. The ambient frame caps -/

/-- **THE PARSEVAL FRAME BOUND.**  A weighted atom never reads more than one:
`t_c·|g_c|² ≤ 1`. -/
theorem parseval_weight_leverage_le_one {m : ℕ} (D : WeightedDesign m 3)
    (c : Fin m) :
    D.weight c * (D.atom c ⬝ᵥ D.atom c) ≤ 1 := by
  classical
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun a => D.weight a • atomMatrix (D.atom a)) (Finset.mem_univ c)
  rw [D.isParseval] at hsplit
  have hpsd : (∑ a ∈ Finset.univ.erase c,
      D.weight a • atomMatrix (D.atom a)).PosSemidef :=
    Matrix.posSemidef_sum _ (fun a _ =>
      (posSemidef_atomMatrix (D.atom a)).smul (D.weight_pos a).le)
  have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (D.atom c)
  rw [star_trivial] at hread
  have hrest : (∑ a ∈ Finset.univ.erase c,
      D.weight a • atomMatrix (D.atom a))
      = 1 - D.weight c • atomMatrix (D.atom c) := by
    rw [← hsplit]; abel
  rw [hrest] at hread
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    quadForm_smul_atomMatrix] at hread
  have hlev : 0 ≤ D.atom c ⬝ᵥ D.atom c := by
    rw [dotProduct_self_eq_sum_sq]
    positivity
  nlinarith [hread, hlev, (D.weight_pos c), sq_nonneg (D.atom c ⬝ᵥ D.atom c)]

/-- **THE CORNER TRACE.**  The corner equation read at the trace: the three
inside leverages total `3 + lam`. -/
theorem corner_trace_identity {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    D.atom x ⬝ᵥ D.atom x + D.atom y ⬝ᵥ D.atom y + D.atom z ⬝ᵥ D.atom z
      = 3 + lam := by
  have htr := congrArg Matrix.trace hgap
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  rw [hsum, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add,
    trace_atomMatrix, trace_atomMatrix, trace_atomMatrix,
    Matrix.trace_smul, trace_atomMatrix, Matrix.trace_one] at htr
  have hcast : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  rw [hcast] at htr
  have hlevu : leverageOf u = 1 := by
    rw [show leverageOf u = u ⬝ᵥ u from (dotProduct_self_eq_sum_sq u).symm,
      hunit]
  rw [hlevu, smul_eq_mul, mul_one] at htr
  rw [show D.atom x ⬝ᵥ D.atom x = leverageOf (D.atom x) from
      dotProduct_self_eq_sum_sq _,
    show D.atom y ⬝ᵥ D.atom y = leverageOf (D.atom y) from
      dotProduct_self_eq_sum_sq _,
    show D.atom z ⬝ᵥ D.atom z = leverageOf (D.atom z) from
      dotProduct_self_eq_sum_sq _]
  linarith [htr]

/-- **THE CORNER SCALE CAP.**  On a corner with a unit erased atom the scale
obeys `lam ≤ 1/t_y + 1/t_z − 2`: the ambient frame bound compactifies the
corner arena. -/
theorem corner_scale_cap {m : ℕ} (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    lam ≤ 1 / D.weight y + 1 / D.weight z - 2 := by
  have htr := corner_trace_identity D hxy hxz hyz hunit hgap
  have hy := parseval_weight_leverage_le_one D y
  have hz := parseval_weight_leverage_le_one D z
  have hylev : D.atom y ⬝ᵥ D.atom y ≤ 1 / D.weight y := by
    rw [le_div_iff₀ (D.weight_pos y)]
    nlinarith [hy]
  have hzlev : D.atom z ⬝ᵥ D.atom z ≤ 1 / D.weight z := by
    rw [le_div_iff₀ (D.weight_pos z)]
    nlinarith [hz]
  nlinarith [htr, hylev, hzlev]

/-! ## 3. The ambient transverse floor -/

/-- **THE AMBIENT TRANSVERSE FLOOR.**  On the both-light cell — the two
four-set gaps positive definite — the `y`-floor, the six outside floors, a
unit erased atom, and independent outside atoms force the dual-basis
transverse energies at the rate of the two smaller outside weights:

  `σ·(σ − tcap) ≤ t_y·Σ_d T^y_d + t_z·Σ_d T^z_d` ,

with `σ` the outside weight total, `tcap` any bound of the three outside
weights, and `T^s_d` the transverse energy of the outside slot `d` at side
`s`: the `A_s`-energy of the dual-basis vector `Mo⁻¹g_d` minus the
reciprocal floor `1/r_d`.  Each energy is nonnegative on the cell, and the
left side is positive when two outside weights are. -/
theorem corner_bothLight_transverse_floor (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin 6))).PosDef)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hyfloor : 1 ≤ D.atom y ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom y))
    (hfY : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d))
    (hfZ : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d))
    {tcap : ℝ} (hc4 : D.weight d4 ≤ tcap) (hc5 : D.weight d5 ≤ tcap)
    (hc6 : D.weight d6 ≤ tcap) :
    (D.weight d4 + D.weight d5 + D.weight d6)
        * (D.weight d4 + D.weight d5 + D.weight d6 - tcap)
      ≤ D.weight y * (∑ j : Fin 3,
            (((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
              ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1) *ᵥ
                ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j)))
            - 1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j)))))
        + D.weight z * (∑ j : Fin 3,
            (((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
              ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1) *ᵥ
                ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j)))
            - 1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j))))) := by
  classical
  set Mo : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({d4, d5, d6} : Finset (Fin 6)) with hMoDef
  set Ay : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1 with hAyDef
  set Az : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1 with hAzDef
  set V : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun i j => D.atom (![d4, d5, d6] j) i with hVDef
  -- the outside sum is the column Gram
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
  -- the chart is invertible
  have hdetV : IsUnit V.det := by
    have hdet : Mo.det = V.det * V.det := by
      rw [← hVVt, Matrix.det_mul, Matrix.det_transpose]
    have hpos := hMo.det_pos
    rw [hdet] at hpos
    exact isUnit_iff_ne_zero.mpr fun hzero => by
      rw [hzero, mul_zero] at hpos
      exact lt_irrefl 0 hpos
  have hdetVt : IsUnit Vᵀ.det := by rwa [Matrix.det_transpose]
  have hVinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdetV
  have hVinv' : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hdetV
  have hdetVinv : IsUnit (V⁻¹).det := Matrix.isUnit_nonsing_inv_det V hdetV
  -- the columns and their pencil coordinates
  have hcol : ∀ j : Fin 3, V *ᵥ Pi.single j 1 = D.atom (![d4, d5, d6] j) := by
    intro j
    rw [Matrix.mulVec_single_one]
    ext i
    simp [hVDef]
  have hetaOut : ∀ j : Fin 3,
      V⁻¹ *ᵥ D.atom (![d4, d5, d6] j) = Pi.single j 1 := by
    intro j
    rw [← hcol j, Matrix.mulVec_mulVec, hVinv, Matrix.one_mulVec]
  set ηx : Fin 3 → ℝ := V⁻¹ *ᵥ D.atom x with hetaXDef
  set ηy : Fin 3 → ℝ := V⁻¹ *ᵥ D.atom y with hetaYDef
  set ηz : Fin 3 → ℝ := V⁻¹ *ᵥ D.atom z with hetaZDef
  have hVetaX : V *ᵥ ηx = D.atom x := by
    rw [hetaXDef, Matrix.mulVec_mulVec, hVinv', Matrix.one_mulVec]
  -- Parseval, split over the six names
  have hpars : (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = D.weight x • atomMatrix (D.atom x) + D.weight y • atomMatrix (D.atom y)
        + D.weight z • atomMatrix (D.atom z)
        + D.weight d4 • atomMatrix (D.atom d4)
        + D.weight d5 • atomMatrix (D.atom d5)
        + D.weight d6 • atomMatrix (D.atom d6) := by
    have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
      (fun c => D.weight c • atomMatrix (D.atom c))
    rw [D.isParseval, hcompl, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton,
      Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton] at hsplit
    rw [← hsplit]
    abel
  have hwsum : D.weight x + D.weight y + D.weight z
      + D.weight d4 + D.weight d5 + D.weight d6 = 1 := by
    have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
      D.weight
    rw [D.weight_sum_one, hcompl, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton,
      Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton] at hsplit
    linarith [hsplit]
  -- the master identity: Parseval in the pencil chart
  have hmaster : Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
      + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
      + D.weight z • atomMatrix ηz
      = V⁻¹ * (V⁻¹)ᵀ := by
    have hcong := congrArg (fun M => V⁻¹ * M * (V⁻¹)ᵀ) hpars
    simp only [Matrix.mul_one] at hcong
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul] at hcong
    rw [congr_atomMatrix, congr_atomMatrix, congr_atomMatrix,
      congr_atomMatrix, congr_atomMatrix, congr_atomMatrix] at hcong
    have h4 : V⁻¹ *ᵥ D.atom d4 = Pi.single 0 1 := by
      have := hetaOut 0
      simpa using this
    have h5 : V⁻¹ *ᵥ D.atom d5 = Pi.single 1 1 := by
      have := hetaOut 1
      simpa using this
    have h6 : V⁻¹ *ᵥ D.atom d6 = Pi.single 2 1 := by
      have := hetaOut 2
      simpa using this
    rw [h4, h5, h6, ← hetaXDef, ← hetaYDef, ← hetaZDef] at hcong
    rw [diagonal_eq_sum_single_atoms, hcong]
    abel
  -- the conjugated outside Gram is the identity
  have hVMoV : V⁻¹ * Mo * (V⁻¹)ᵀ = 1 := by
    rw [← hVVt, ← Matrix.mul_assoc, hVinv, Matrix.one_mul,
      ← Matrix.transpose_mul, hVinv, Matrix.transpose_one]
  -- the gap transports
  have hynotout : y ∉ ({d4, d5, d6} : Finset (Fin 6)) := by
    rw [← hcompl]
    simp
  have hznotout : z ∉ ({d4, d5, d6} : Finset (Fin 6)) := by
    rw [← hcompl]
    simp
  have hAysum : Ay = atomMatrix (D.atom y) + Mo - 1 := by
    rw [hAyDef, hMoDef, hcompl, subsetSum, subsetSum,
      Finset.sum_insert hynotout]
  have hAzsum : Az = atomMatrix (D.atom z) + Mo - 1 := by
    rw [hAzDef, hMoDef, hcompl, subsetSum, subsetSum,
      Finset.sum_insert hznotout]
  have hgapY : V⁻¹ * Ay * (V⁻¹)ᵀ
      = (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηy := by
    rw [hAysum]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_one]
    rw [congr_atomMatrix, hVMoV, ← hmaster, ← hetaYDef]
    abel
  have hgapZ : V⁻¹ * Az * (V⁻¹)ᵀ
      = (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηz := by
    rw [hAzsum]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_one]
    rw [congr_atomMatrix, hVMoV, ← hmaster, ← hetaZDef]
    abel
  -- the transported positive definiteness
  have hWpd : (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
      + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
      + D.weight z • atomMatrix ηz).PosDef := by
    rw [hmaster]
    have h := posDef_congruence
      (Matrix.PosDef.one : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosDef) hdetVinv
    rwa [Matrix.mul_one] at h
  have hAyBarPD : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
        + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
        + D.weight z • atomMatrix ηz)
      + atomMatrix ηy).PosDef := by
    rw [← hgapY]
    exact posDef_congruence hAy hdetVinv
  have hAzBarPD : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
        + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
        + D.weight z • atomMatrix ηz)
      + atomMatrix ηz).PosDef := by
    rw [← hgapZ]
    exact posDef_congruence hAz hdetVinv
  -- the floor and entry transports
  have hinvY : ∀ j : Fin 3,
      (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηy)⁻¹) j j
      = D.atom (![d4, d5, d6] j) ⬝ᵥ (Ay⁻¹ *ᵥ D.atom (![d4, d5, d6] j)) := by
    intro j
    rw [← hgapY, inv_congr_inv hdetV, congr_entry]
    rfl
  have hinvZ : ∀ j : Fin 3,
      (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηz)⁻¹) j j
      = D.atom (![d4, d5, d6] j) ⬝ᵥ (Az⁻¹ *ᵥ D.atom (![d4, d5, d6] j)) := by
    intro j
    rw [← hgapZ, inv_congr_inv hdetV, congr_entry]
    rfl
  have hfloorY : ∀ j : Fin 3,
      1 ≤ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηy)⁻¹) j j := by
    intro j
    rw [hinvY j]
    fin_cases j
    · simpa using hfY d4 (by rw [hcompl]; simp)
    · simpa using hfY d5 (by rw [hcompl]; simp)
    · simpa using hfY d6 (by rw [hcompl]; simp)
  have hfloorZ : ∀ j : Fin 3,
      1 ≤ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηz)⁻¹) j j := by
    intro j
    rw [hinvZ j]
    fin_cases j
    · simpa using hfZ d4 (by rw [hcompl]; simp)
    · simpa using hfZ d5 (by rw [hcompl]; simp)
    · simpa using hfZ d6 (by rw [hcompl]; simp)
  -- the seventh floor: the y-floor in determinant form
  have h7 : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
        + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
        + D.weight z • atomMatrix ηz)).det ≤ 0 := by
    have hMo1 : V⁻¹ * (Mo - 1) * (V⁻¹)ᵀ
        = (1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
            + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
            + D.weight z • atomMatrix ηz) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hVMoV, Matrix.mul_one, hmaster]
    have hyDet : (Mo - 1).det ≤ 0 := by
      have hmem : y ∈ insert y (({x, y, z} : Finset (Fin 6))ᶜ) :=
        Finset.mem_insert_self y _
      have hpd : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1).PosDef := by
        rw [← hAyDef]
        exact hAy
      have h := (member_floor_iff_gapDet_erase_nonpos D hpd hmem).mp (by
        rw [← hAyDef]
        exact hyfloor)
      have herase : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).erase y
          = ({d4, d5, d6} : Finset (Fin 6)) := by
        rw [Finset.erase_insert (by rw [hcompl]; exact hynotout), hcompl]
      rw [herase, ← hMoDef] at h
      exact h
    have hdet := congrArg Matrix.det hMo1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
    rw [← hdet]
    have hsq : 0 ≤ V⁻¹.det * V⁻¹.det := mul_self_nonneg _
    nlinarith [hyDet, hsq]
  -- the erased-atom link
  have hxlink : ηx ⬝ᵥ
      ((Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
        + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
        + D.weight z • atomMatrix ηz)⁻¹ *ᵥ ηx) = 1 := by
    rw [hmaster]
    have hWinv : (V⁻¹ * (V⁻¹)ᵀ)⁻¹ = Vᵀ * V := by
      rw [Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv,
        Matrix.nonsing_inv_nonsing_inv _ hdetVt,
        Matrix.nonsing_inv_nonsing_inv _ hdetV]
    rw [hWinv, quad_transpose_mul, hVetaX, hxunit]
  -- the abstract law fires
  have hmain := transverse_floor (D.weight_pos x).le (D.weight_pos y).le
    (D.weight_pos z).le (D.weight_pos d4).le (D.weight_pos d5).le
    (D.weight_pos d6).le (by linarith [hwsum]) hc4 hc5 hc6 hWpd hxlink
    hAyBarPD hAzBarPD hfloorY hfloorZ h7
  -- transport the conclusion into ambient readings
  have hMoInv : Mo⁻¹ = (V⁻¹)ᵀ * V⁻¹ := by
    rw [← hVVt, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]
  have hdual : ∀ j : Fin 3,
      Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j) = fun i => (V⁻¹)ᵀ i j := by
    intro j
    rw [hMoInv, ← Matrix.mulVec_mulVec, hetaOut j, Matrix.mulVec_single_one]
    rfl
  have hentryY : ∀ j : Fin 3,
      ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηy) j j
      = (Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
          (Ay *ᵥ (Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j))) := by
    intro j
    rw [← hgapY, hdual j]
    have h := congr_entry Ay ((V⁻¹)ᵀ) j
    rw [Matrix.transpose_transpose] at h
    exact h
  have hentryZ : ∀ j : Fin 3,
      ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηz) j j
      = (Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
          (Az *ᵥ (Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j))) := by
    intro j
    rw [← hgapZ, hdual j]
    have h := congr_entry Az ((V⁻¹)ᵀ) j
    rw [Matrix.transpose_transpose] at h
    exact h
  have hsumY : (∑ j : Fin 3,
      (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηy) j j
      - 1 / ((((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
            + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
            + D.weight z • atomMatrix ηz)
          + atomMatrix ηy)⁻¹) j j)))
      = ∑ j : Fin 3,
          ((Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
              (Ay *ᵥ (Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j)))
            - 1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                (Ay⁻¹ *ᵥ D.atom (![d4, d5, d6] j)))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hentryY j, hinvY j]
  have hsumZ : (∑ j : Fin 3,
      (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
          + D.weight z • atomMatrix ηz)
        + atomMatrix ηz) j j
      - 1 / ((((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - (Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
            + D.weight x • atomMatrix ηx + D.weight y • atomMatrix ηy
            + D.weight z • atomMatrix ηz)
          + atomMatrix ηz)⁻¹) j j)))
      = ∑ j : Fin 3,
          ((Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
              (Az *ᵥ (Mo⁻¹ *ᵥ D.atom (![d4, d5, d6] j)))
            - 1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                (Az⁻¹ *ᵥ D.atom (![d4, d5, d6] j)))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hentryZ j, hinvZ j]
  rw [hsumY, hsumZ] at hmain
  exact hmain

/-- **THE CORNER-FACING FORM.**  The ambient transverse floor with the unit
norm supplied by the corner equation. -/
theorem corner_bothLight_transverse_floor_of_corner (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hMo : (subsetSum D ({d4, d5, d6} : Finset (Fin 6))).PosDef)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hyfloor : 1 ≤ D.atom y ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom y))
    (hfY : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d))
    (hfZ : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d))
    {tcap : ℝ} (hc4 : D.weight d4 ≤ tcap) (hc5 : D.weight d5 ≤ tcap)
    (hc6 : D.weight d6 ≤ tcap) :
    (D.weight d4 + D.weight d5 + D.weight d6)
        * (D.weight d4 + D.weight d5 + D.weight d6 - tcap)
      ≤ D.weight y * (∑ j : Fin 3,
            (((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
              ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1) *ᵥ
                ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j)))
            - 1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j)))))
        + D.weight z * (∑ j : Fin 3,
            (((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                *ᵥ D.atom (![d4, d5, d6] j)) ⬝ᵥ
              ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1) *ᵥ
                ((subsetSum D ({d4, d5, d6} : Finset (Fin 6)))⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j)))
            - 1 / (D.atom (![d4, d5, d6] j) ⬝ᵥ
                ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                  *ᵥ D.atom (![d4, d5, d6] j))))) :=
  corner_bothLight_transverse_floor D hxy hxz hyz h45 h46 h56 hcompl hMo hAy
    hAz
    (corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam hunit hgap
      (by simp) hax)
    hyfloor hfY hfZ hc4 hc5 hc6

end Gtz
