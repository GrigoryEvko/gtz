/-
# The cross price of the two-zero stratum: a tie pays the parallelism gap

In the two-zero stratum (`K2`) the dominator `C = {x, y, z}` has a unit null
direction `w`, the atoms `y, z` read `w` at zero, and `x = ±w`.  The frame
matrix `M := (S_C − 1) + wwᵀ` is positive definite and fixes `w`.  This module
prices every avoiding triple through the silenced pair with ONE exact law:

  `det(S_{y,z,d} − 1) = ((g_d·w)² − 1)·det M − (g_d × w)ᵀ M (g_d × w)` .

The cross reading on the right is the `M`-metric cross energy of the PAIR
`(x, d)`, because `g_x = ±w`.  The refusal of `{y, z, d}` at a tie caps the
excess by that cross energy, for every outside atom.  The weighted total
against the landed excess identity gives THE CROSS PRICE OF THE STRATUM:

  `(t_y + t_z)·det M ≤ Σ_{d ∉ C} t_d·(g_d × w)ᵀ M (g_d × w)` .

The right side vanishes exactly when every outside atom is parallel to `w` —
parallel to the atom `x`.  A `K2` tie therefore buys its silenced weight with
the parallelism gap of the pairs `(x, d)`, and a stratum with an all-parallel
outside is not a tie at all.  The law holds at every size, and its two
degeneration channels [MEASURED, `scratchpad/corank1/f26probe3.jl`] are the
weight collapse `t_x, t_y, t_z → 0` and the parallel limit `g_d → ±w`.
-/
import Gtz.Wave.PairMinorBridge
import Gtz.Wave.KTwoEraseSystem
import Gtz.Wave.HeavyInsideCapGap
import Gtz.Wave.CrossLedgerRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Three pure matrix laws -/

/-- A rank-one update with a scale moves a determinant by the scaled adjugate
reading.  The second and third compounds of a rank-one update vanish. -/
theorem det_add_smul_atomMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ)
    (v : Fin 3 → ℝ) :
    (M + c • atomMatrix v).det = M.det + c * (v ⬝ᵥ (M.adjugate *ᵥ v)) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.add_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Fin.sum_univ_three, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  ring

/-- The two-update determinant law with a doubled subtracted atom.  The scaled
twin of `Gtz.det_add_atomMatrix_sub_atomMatrix_cross`. -/
theorem det_add_atomMatrix_sub_two_atomMatrix_cross
    (M : Matrix (Fin 3) (Fin 3) ℝ) (p w : Fin 3 → ℝ) :
    (M + atomMatrix p - (2 : ℝ) • atomMatrix w).det
        + (M + (2 : ℝ) • atomMatrix w).det
      = (M + atomMatrix p).det + M.det
        - 2 * (crossProduct p w ⬝ᵥ (M *ᵥ crossProduct p w)) := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, cross_apply,
    dotProduct, Matrix.mulVec, Fin.sum_univ_three, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- A matrix that fixes a vector gives its adjugate the determinant as the
eigenvalue on that vector.  No invertibility is necessary. -/
theorem adjugate_mulVec_fixed {M : Matrix (Fin 3) (Fin 3) ℝ}
    {w : Fin 3 → ℝ} (hMw : M *ᵥ w = w) :
    M.adjugate *ᵥ w = M.det • w := by
  calc M.adjugate *ᵥ w = M.adjugate *ᵥ (M *ᵥ w) := by rw [hMw]
    _ = (M.adjugate * M) *ᵥ w := Matrix.mulVec_mulVec _ _ _
    _ = (M.det • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ w := by
        rw [Matrix.adjugate_mul]
    _ = M.det • w := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]

/-! ## 2. The cross reading at a fixed unit vector -/

/-- **The cross reading against a fixed unit vector.**  For a symmetric matrix
with `M w = w`, `w` unit and `det M ≠ 0`, the `M`-energy of a cross with `w`
is the adjugate reading minus the squared `w`-component:

  `(p × w)ᵀ M (p × w) = pᵀ(adj M)p − (p·w)²·det M` .

The compound identity of the pair-minor bridge, read at the adjugate. -/
theorem cross_reading_at_fixed_unit {M : Matrix (Fin 3) (Fin 3) ℝ}
    {w : Fin 3 → ℝ} (hMw : M *ᵥ w = w) (hunit : w ⬝ᵥ w = 1)
    (hsymm : Mᵀ = M) (hdet : M.det ≠ 0) (p : Fin 3 → ℝ) :
    crossProduct p w ⬝ᵥ (M *ᵥ crossProduct p w)
      = p ⬝ᵥ (M.adjugate *ᵥ p) - (p ⬝ᵥ w) ^ 2 * M.det := by
  have hpg := det_pairGram_eq_cross_adjugate M.adjugate p w
  rw [adjugate_adjugate_fin_three, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul] at hpg
  have hadjw : M.adjugate *ᵥ w = M.det • w := adjugate_mulVec_fixed hMw
  have hww : w ⬝ᵥ (M.adjugate *ᵥ w) = M.det := by
    rw [hadjw, dotProduct_smul, smul_eq_mul, hunit, mul_one]
  have hpw : p ⬝ᵥ (M.adjugate *ᵥ w) = M.det * (p ⬝ᵥ w) := by
    rw [hadjw, dotProduct_smul, smul_eq_mul]
  have hadjsymm : M.adjugateᵀ = M.adjugate := by
    rw [Matrix.adjugate_transpose, hsymm]
  have hwp : w ⬝ᵥ (M.adjugate *ᵥ p) = M.det * (p ⬝ᵥ w) := by
    rw [dot_mulVec_comm hadjsymm w p, hpw]
  rw [hww, hpw, hwp] at hpg
  have hfac : M.det * (crossProduct p w ⬝ᵥ (M *ᵥ crossProduct p w))
      = M.det * (p ⬝ᵥ (M.adjugate *ᵥ p) - (p ⬝ᵥ w) ^ 2 * M.det) := by
    linear_combination -hpg
  exact mul_left_cancel₀ hdet hfac

/-- **The pair-erase swap determinant.**  For `M` that fixes the unit vector
`w`, symmetric with nonzero determinant:

  `det(M + ppᵀ − 2wwᵀ) = ((p·w)² − 1)·det M − (p × w)ᵀ M (p × w)` . -/
theorem det_add_atomMatrix_sub_two_fixed (M : Matrix (Fin 3) (Fin 3) ℝ)
    {w : Fin 3 → ℝ} (hMw : M *ᵥ w = w) (hunit : w ⬝ᵥ w = 1)
    (hsymm : Mᵀ = M) (hdet : M.det ≠ 0) (p : Fin 3 → ℝ) :
    (M + atomMatrix p - (2 : ℝ) • atomMatrix w).det
      = ((p ⬝ᵥ w) ^ 2 - 1) * M.det
        - crossProduct p w ⬝ᵥ (M *ᵥ crossProduct p w) := by
  have hcross := det_add_atomMatrix_sub_two_atomMatrix_cross M p w
  have hdouble : (M + (2 : ℝ) • atomMatrix w).det = 3 * M.det := by
    rw [det_add_smul_atomMatrix]
    have hww : w ⬝ᵥ (M.adjugate *ᵥ w) = M.det := by
      rw [adjugate_mulVec_fixed hMw, dotProduct_smul, smul_eq_mul, hunit,
        mul_one]
    rw [hww]
    ring
  have hplus : (M + atomMatrix p).det = M.det + p ⬝ᵥ (M.adjugate *ᵥ p) := by
    rw [show atomMatrix p = (1 : ℝ) • atomMatrix p from (one_smul _ _).symm,
      det_add_smul_atomMatrix, one_mul]
  have hread := cross_reading_at_fixed_unit hMw hunit hsymm hdet p
  linarith [hcross, hdouble, hplus, hread]

/-! ## 3. The frame matrix of the stratum -/

/-- The gap maps the null direction to zero. -/
theorem k2_gap_mulVec_nullDir_eq_zero (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    (subsetSum D C - 1) *ᵥ nullDir = 0 :=
  mulVec_eq_zero_of_form_eq_zero hdominates
    (transpose_subsetSum_sub_one D C) hnull

/-- The frame matrix `M = (S_C − 1) + wwᵀ` fixes the unit null direction. -/
theorem k2_frame_mulVec_fixed (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1) :
    (subsetSum D C - 1 + atomMatrix nullDir) *ᵥ nullDir = nullDir := by
  rw [Matrix.add_mulVec, k2_gap_mulVec_nullDir_eq_zero D hdominates hnull,
    atomMatrix, vecMulVec_mulVec_eq, hunit, one_smul, zero_add]

/-- The frame matrix is symmetric. -/
theorem k2_frame_transpose (D : WeightedDesign m 3) (C : Finset (Fin m))
    (nullDir : Fin 3 → ℝ) :
    (subsetSum D C - 1 + atomMatrix nullDir)ᵀ
      = subsetSum D C - 1 + atomMatrix nullDir := by
  rw [Matrix.transpose_add, transpose_subsetSum_sub_one,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix nullDir).1]

/-- **The frame matrix is positive definite.**  The null LINE hypothesis
enters exactly here: a vector that kills the gap form is a multiple of the
null direction, and the added atom then reads it. -/
theorem k2_frame_posDef (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) (hunit : nullDir ⬝ᵥ nullDir = 1) :
    (subsetSum D C - 1 + atomMatrix nullDir).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (k2_frame_transpose D C nullDir),
      fun v hv => ?_⟩
  rw [star_trivial, Matrix.add_mulVec, dotProduct_add, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm v nullDir]
  have hgap : 0 ≤ v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 v
    rwa [star_trivial] at h
  have hsq : 0 ≤ (nullDir ⬝ᵥ v) * (nullDir ⬝ᵥ v) := mul_self_nonneg _
  by_contra hcon
  push Not at hcon
  have hgap0 : v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) = 0 := by linarith
  have hread0 : nullDir ⬝ᵥ v = 0 := by nlinarith
  obtain ⟨scale, hscale⟩ := hline.2.2 v hgap0
  have hzero : scale = 0 := by
    have := hread0
    rw [hscale, dotProduct_smul, smul_eq_mul, hunit, mul_one] at this
    exact this
  exact hv (by rw [hscale, hzero, zero_smul])

/-- **The swap base is positive definite off the silent slice.**  The gap plus
an outside atom that reads the null direction is definite: the null line is
the only escape of the gap, and the atom closes it. -/
theorem k2_swapBase_posDef (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) (_hunit : nullDir ⬝ᵥ nullDir = 1)
    {d : Fin m} (hread : D.atom d ⬝ᵥ nullDir ≠ 0) :
    (subsetSum D C - 1 + atomMatrix (D.atom d)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (by
      rw [Matrix.transpose_add, transpose_subsetSum_sub_one,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom d)).1]),
      fun v hv => ?_⟩
  rw [star_trivial, Matrix.add_mulVec, dotProduct_add, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm v (D.atom d)]
  have hgap : 0 ≤ v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 v
    rwa [star_trivial] at h
  have hsq : 0 ≤ (D.atom d ⬝ᵥ v) * (D.atom d ⬝ᵥ v) := mul_self_nonneg _
  by_contra hcon
  push Not at hcon
  have hgap0 : v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) = 0 := by linarith
  have hread0 : D.atom d ⬝ᵥ v = 0 := by nlinarith
  obtain ⟨scale, hscale⟩ := hline.2.2 v hgap0
  have hzero : scale = 0 := by
    rw [hscale, dotProduct_smul, smul_eq_mul] at hread0
    rcases mul_eq_zero.mp hread0 with h | h
    · exact h
    · exact absurd h hread
  exact hv (by rw [hscale, hzero, zero_smul])

/-! ## 4. The forbidden-triple determinant law -/

/-- The avoiding triple through the silenced pair, in frame normal form. -/
theorem k2_avoiding_triple_normal_form (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    {d : Fin m} (_hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z) :
    subsetSum D ({y, z, d} : Finset (Fin m)) - 1
      = (subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir)
        + atomMatrix (D.atom d) - (2 : ℝ) • atomMatrix nullDir := by
  obtain ⟨-, hxw⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdominates hnull hunit hy hz
  have hax : atomMatrix (D.atom x) = atomMatrix nullDir := by
    rcases hxw with hxw | hxw
    · rw [hxw]
    · rw [hxw, atomMatrix_neg]
  have hsumC : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + (atomMatrix (D.atom y) + atomMatrix (D.atom z)) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
  have hsumT : subsetSum D ({y, z, d} : Finset (Fin m))
      = atomMatrix (D.atom y) + (atomMatrix (D.atom z) + atomMatrix (D.atom d)) := by
    rw [subsetSum, Finset.sum_insert (by simp [hyz, Ne.symm hdy]),
      Finset.sum_insert (by simp [Ne.symm hdz]), Finset.sum_singleton]
  rw [hsumT, hsumC, hax, two_smul]
  abel

/-- **THE FORBIDDEN-TRIPLE DETERMINANT LAW.**  In the two-zero stratum the
determinant of every avoiding triple through the silenced pair is the excess
against the pair cross energy:

  `det(S_{y,z,d} − 1) = ((g_d·w)² − 1)·det M − (g_d × w)ᵀ M (g_d × w)` ,

with `M = (S_C − 1) + wwᵀ ≻ 0` the frame matrix.  The cross is the pair
`(x, d)` cross up to sign, because `g_x = ±w`. -/
theorem k2_forbidden_det_eq (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    {d : Fin m} (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z) :
    (subsetSum D ({y, z, d} : Finset (Fin m)) - 1).det
      = ((D.atom d ⬝ᵥ nullDir) ^ 2 - 1)
          * (subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir).det
        - crossProduct (D.atom d) nullDir
            ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir)
              *ᵥ crossProduct (D.atom d) nullDir) := by
  have hMpd := k2_frame_posDef D hdominates hline hunit
  rw [k2_avoiding_triple_normal_form D hxy hxz hyz hdominates hline.2.1 hunit
    hy hz hdx hdy hdz]
  exact det_add_atomMatrix_sub_two_fixed _
    (k2_frame_mulVec_fixed D hdominates hline.2.1 hunit)
    hunit (k2_frame_transpose D _ nullDir) (ne_of_gt hMpd.det_pos) (D.atom d)

/-! ## 5. The tie caps every excess by its cross energy -/

/-- **The refusal caps the excess by the cross energy.**  At a tie every
avoiding triple through the silenced pair is refused, and the refusal reads:

  `((g_d·w)² − 1)·det M ≤ (g_d × w)ᵀ M (g_d × w)` .

If the cross energy were smaller, the triple determinant would be positive,
the swap base `S_C − 1 + g_dg_dᵀ` definite, and the rank-one downdate
criterion would make the triple a STRICT dominator. -/
theorem k2_isTie_excess_le_cross (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    {d : Fin m} (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z) :
    ((D.atom d ⬝ᵥ nullDir) ^ 2 - 1)
        * (subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir).det
      ≤ crossProduct (D.atom d) nullDir
          ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir)
            *ᵥ crossProduct (D.atom d) nullDir) := by
  classical
  set M : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir with hM
  have hMpd : M.PosDef := k2_frame_posDef D hdominates hline hunit
  by_contra hcon
  push Not at hcon
  have hcross0 : 0 ≤ crossProduct (D.atom d) nullDir
      ⬝ᵥ (M *ᵥ crossProduct (D.atom d) nullDir) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hMpd.posSemidef).2
      (crossProduct (D.atom d) nullDir)
    rwa [star_trivial] at h
  have hdetM : 0 < M.det := hMpd.det_pos
  have ha2 : 1 < (D.atom d ⬝ᵥ nullDir) ^ 2 := by nlinarith
  have haread : D.atom d ⬝ᵥ nullDir ≠ 0 := by
    intro h0
    rw [h0] at ha2
    norm_num at ha2
  have hdetT : 0 < (subsetSum D ({y, z, d} : Finset (Fin m)) - 1).det := by
    rw [k2_forbidden_det_eq D hxy hxz hyz hdominates hline hunit hy hz
      hdx hdy hdz, ← hM]
    linarith
  have hBpd : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1
      + atomMatrix (D.atom d)).PosDef :=
    k2_swapBase_posDef D hdominates hline hunit haread
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix (D.atom d) with hB
  have hsplit : subsetSum D ({y, z, d} : Finset (Fin m)) - 1
      = B - atomMatrix nullDir := by
    have hnf := k2_avoiding_triple_normal_form D hxy hxz hyz hdominates
      hline.2.1 hunit hy hz hdx hdy hdz
    rw [hnf, hB, two_smul]
    abel
  have hdetB : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hBpd.det_pos)
  have hdetdown : (B - atomMatrix nullDir).det
      = B.det * (1 - nullDir ⬝ᵥ (B⁻¹ *ᵥ nullDir)) := det_sub_atomMatrix hdetB _
  have hreadlt : nullDir ⬝ᵥ (B⁻¹ *ᵥ nullDir) < 1 := by
    rw [hsplit, hdetdown] at hdetT
    have hBdetpos := hBpd.det_pos
    nlinarith
  have hpd : (B - Matrix.vecMulVec nullDir nullDir).PosDef :=
    (posDef_sub_vecMulVec_iff B hBpd nullDir).mpr hreadlt
  have hcard : ({y, z, d} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hyz, hdy.symm]),
      Finset.card_insert_of_notMem (by simp [hdz.symm]), Finset.card_singleton]
  refine htie.2 ({y, z, d} : Finset (Fin m)) hcard ?_
  rw [hsplit]
  exact hpd

/-- **THE CROSS PRICE OF THE STRATUM.**  A `K2` tie pays the silenced weight
with the total weighted cross energy of the pairs `(x, d)`:

  `(t_y + t_z)·det M ≤ Σ_{d ∉ C} t_d·(g_d × w)ᵀ M (g_d × w)` .

The per-atom caps are weighted and summed against the landed outside excess
identity `Σ_{d ∉ C} t_d((g_d·w)² − 1) = t_y + t_z`. -/
theorem k2_isTie_crossPrice (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    (D.weight y + D.weight z)
        * (subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir).det
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d * (crossProduct (D.atom d) nullDir
            ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir)
              *ᵥ crossProduct (D.atom d) nullDir)) := by
  classical
  have hexcess := k2_outside_excess_total D hxy hxz hyz hdominates hline.2.1
    hunit hy hz
  calc (D.weight y + D.weight z)
      * (subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir).det
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.weight d * (((D.atom d ⬝ᵥ nullDir) ^ 2 - 1)
            * (subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir).det) := by
        rw [← hexcess, Finset.sum_mul]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun d hd => ?_
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hd
        exact mul_le_mul_of_nonneg_left
          (k2_isTie_excess_le_cross D htie hxy hxz hyz hdominates hline hunit
            hy hz hd.1 hd.2.1 hd.2.2)
          (D.weight_pos d).le

/-- **An all-parallel outside forbids the tie.**  If every outside atom is a
multiple of the null direction, every cross energy vanishes and the price law
demands `(t_y + t_z)·det M ≤ 0`, against positive weights and a definite
frame.  A `K2` tie therefore owns an outside atom that is NOT parallel to the
atom `x`. -/
theorem k2_not_isTie_of_outside_parallel_all (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    (hpar : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      crossProduct (D.atom d) nullDir = 0) :
    ¬ IsTie D := by
  classical
  intro htie
  have hprice := k2_isTie_crossPrice D htie hxy hxz hyz hdominates hline hunit hy hz
  have hzero : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (crossProduct (D.atom d) nullDir
        ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1 + atomMatrix nullDir)
          *ᵥ crossProduct (D.atom d) nullDir)) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [hpar d hd, Matrix.mulVec_zero, dotProduct_zero, mul_zero]
  rw [hzero] at hprice
  have hMpd := k2_frame_posDef D hdominates hline hunit
  have hty := D.weight_pos y
  have htz := D.weight_pos z
  nlinarith [hMpd.det_pos, hprice]

end Gtz
