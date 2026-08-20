import Gtz.Wave.ShellAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The transverse floor

The both-light collapse analysis rests on one quantitative law: the seven
floors FORCE transverse energy.  This module proves it, in the abstract
pencil-frame data, with no design and no spectral theory.

The data: weights `t_x..t_6` on the simplex, three vectors `η_x, η_y, η_z`,
the moment matrix

  `W = diag(t₄,t₅,t₆) + t_x·η_xη_xᵀ + t_y·η_yη_yᵀ + t_z·η_zη_zᵀ`

and the two shifted gaps `A_y = 1 − W + η_yη_yᵀ`, `A_z = 1 − W + η_zη_zᵀ`.
The transverse energy of a slot is the Schur excess
`T_d = A_dd − 1/(A⁻¹)_dd ≥ 0`.

**THE LAW** (`Gtz.transverse_floor`): under the six diagonal floors
`(A_y⁻¹)_dd ≥ 1`, `(A_z⁻¹)_dd ≥ 1`, the normalization
`η_xᵀW⁻¹η_x = 1`, and the seventh floor `det(1 − W) ≤ 0`:

  `t_y·ΣT^y_d + t_z·ΣT^z_d ≥ (t₄+t₅+t₆)·(t₄+t₅+t₆ − t_o)` ,

`tcap` any upper bound of the three outside weights.  The right side is
positive whenever two outside weights are: the floors force the arena away
from every collapse ray at a rate the two smaller outside weights set.

The proof is three moves.  Cauchy–Schwarz at the `W⁻¹`-unit `η_x` caps the
`x`-components by the diagonal of `W`; the floors and the Schur split cap
the `y`- and `z`-components the same way, at the price of one transverse
energy each; and the seventh floor makes the diagonal energies total at
least `1 − t_o`, because a matrix with nonpositive determinant is not
positive definite.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The bilinear Cauchy–Schwarz at a positive form -/

/-- **CS AT A POSITIVE FORM.**  For positive semidefinite `W` and any two
vectors, `(uᵀWv)² ≤ (uᵀWu)·(vᵀWv)`. -/
theorem posSemidef_bilinear_sq_le {W : Matrix (Fin 3) (Fin 3) ℝ}
    (hW : W.PosSemidef) (u v : Fin 3 → ℝ) :
    (u ⬝ᵥ (W *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (W *ᵥ u)) * (v ⬝ᵥ (W *ᵥ v)) := by
  have hq : ∀ x : Fin 3 → ℝ, 0 ≤ x ⬝ᵥ (W *ᵥ x) := by
    intro x
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hW).2 x
    rwa [star_trivial] at h
  have hsymm : v ⬝ᵥ (W *ᵥ u) = u ⬝ᵥ (W *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      transpose_eq_of_isHermitian hW.1, dotProduct_comm]
  set A : ℝ := u ⬝ᵥ (W *ᵥ u) with hA
  set B : ℝ := u ⬝ᵥ (W *ᵥ v) with hB
  set C : ℝ := v ⬝ᵥ (W *ᵥ v) with hC
  have hbil : ∀ c : ℝ, (c • u + v) ⬝ᵥ (W *ᵥ (c • u + v))
      = c ^ 2 * A + 2 * c * B + C := by
    intro c
    have hexp : (c • u + v) ⬝ᵥ (W *ᵥ (c • u + v))
        = c ^ 2 * (u ⬝ᵥ (W *ᵥ u)) + c * (u ⬝ᵥ (W *ᵥ v))
          + c * (v ⬝ᵥ (W *ᵥ u)) + v ⬝ᵥ (W *ᵥ v) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
        add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [hexp, hsymm, ← hA, ← hB, ← hC]
    ring
  have hApos : 0 ≤ A := hq u
  have hCpos : 0 ≤ C := hq v
  by_cases hA0 : A = 0
  · -- degenerate direction: the cross vanishes
    have hlin : ∀ c : ℝ, 0 ≤ 2 * c * B + C := by
      intro c
      have h := hq (c • u + v)
      rw [hbil c, hA0] at h
      linarith
    have hB0 : B = 0 := by
      by_contra hne
      have h := hlin (-(C + 1) / (2 * B))
      have hval : 2 * (-(C + 1) / (2 * B)) * B = -(C + 1) := by
        field_simp
      rw [hval] at h
      linarith
    rw [hB0, hA0]
    nlinarith
  · have hApos' : 0 < A := lt_of_le_of_ne hApos (Ne.symm hA0)
    have h := hq ((-B / A) • u + v)
    rw [hbil _] at h
    have hval : (-B / A) ^ 2 * A + 2 * (-B / A) * B + C = C - B ^ 2 / A := by
      field_simp
      ring
    rw [hval] at h
    have : B ^ 2 / A ≤ C := by linarith
    calc B ^ 2 = (B ^ 2 / A) * A := by field_simp
    _ ≤ C * A := mul_le_mul_of_nonneg_right this hApos'.le
    _ = A * C := by ring

/-- **THE DIAGONAL–INVERSE FLOOR.**  For positive definite `A`:
`1 ≤ A_dd·(A⁻¹)_dd`. -/
theorem posDef_diag_mul_inv_diag {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (d : Fin 3) :
    1 ≤ A d d * (A⁻¹) d d := by
  set e : Fin 3 → ℝ := Pi.single d 1 with he
  set u : Fin 3 → ℝ := A⁻¹ *ᵥ e with hu
  have hmove : ∀ x y : Fin 3 → ℝ, x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      transpose_eq_of_isHermitian hA.1]
  have hAAe : A *ᵥ u = e := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)), Matrix.one_mulVec]
  have hu_e : u ⬝ᵥ e = (A⁻¹) d d := by
    rw [hu, dotProduct_single_one, Matrix.mulVec_single_one]
    simp
  have h_uAu : u ⬝ᵥ (A *ᵥ u) = (A⁻¹) d d := by rw [hAAe, hu_e]
  have h_uAe : u ⬝ᵥ (A *ᵥ e) = 1 := by
    rw [hmove, hAAe, he, single_one_dotProduct]
    simp
  have h_eAe : e ⬝ᵥ (A *ᵥ e) = A d d := by
    rw [he, single_one_dotProduct, Matrix.mulVec_single_one]
    simp
  have hCS := posSemidef_bilinear_sq_le hA.posSemidef u e
  rw [h_uAe, h_uAu, h_eAe] at hCS
  nlinarith [hCS]

/-! ## 2. The seventh floor forces total diagonal energy -/

/-- **THE ENERGY FLOOR.**  If `det(1 − W) ≤ 0` for the moment matrix of the
data, the weighted vector energies total at least `1 − t_o`. -/
theorem seventh_floor_energy
    {tx ty tz t4 t5 t6 tcap : ℝ} {ηx ηy ηz : Fin 3 → ℝ}
    (htx : 0 ≤ tx) (hty : 0 ≤ ty) (htz : 0 ≤ tz)
    (h4o : t4 ≤ tcap) (h5o : t5 ≤ tcap) (h6o : t6 ≤ tcap)
    (h7 : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
          + ty • atomMatrix ηy + tz • atomMatrix ηz)).det ≤ 0) :
    1 ≤ tcap + (tx * (ηx ⬝ᵥ ηx) + ty * (ηy ⬝ᵥ ηy) + tz * (ηz ⬝ᵥ ηz)) := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
      + ty • atomMatrix ηy + tz • atomMatrix ηz with hWdef
  have hWsymm : Wᵀ = W := by
    rw [hWdef]
    simp only [Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.diagonal_transpose]
    congr 1 <;> [skip; exact congrArg _ (transpose_eq_of_isHermitian
      (posSemidef_atomMatrix ηz).1)]
    congr 1 <;> [skip; exact congrArg _ (transpose_eq_of_isHermitian
      (posSemidef_atomMatrix ηy).1)]
    congr 1
    exact congrArg _ (transpose_eq_of_isHermitian (posSemidef_atomMatrix ηx).1)
  -- a direction with nonpositive shifted form
  have hnotPD : ¬ ((1 : Matrix (Fin 3) (Fin 3) ℝ) - W).PosDef := by
    intro hPD
    exact absurd h7 (not_le.mpr hPD.det_pos)
  have hexists : ∃ φ : Fin 3 → ℝ, φ ≠ 0 ∧ φ ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ) - W) *ᵥ φ) ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hnotPD (Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun φ hφ => ?_⟩)
    · refine isHermitian_of_transpose_eq ?_
      rw [Matrix.transpose_sub, Matrix.transpose_one, hWsymm]
    · rw [star_trivial]
      exact hcon φ hφ
  obtain ⟨φ, hφne, hφform⟩ := hexists
  have hφφ : 0 < φ ⬝ᵥ φ := dotProduct_self_pos hφne
  -- the form expansion
  have hsub : φ ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ) - W) *ᵥ φ)
      = φ ⬝ᵥ φ - φ ⬝ᵥ (W *ᵥ φ) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
  have hWform : φ ⬝ᵥ (W *ᵥ φ)
      = (t4 * φ 0 ^ 2 + t5 * φ 1 ^ 2 + t6 * φ 2 ^ 2)
        + (tx * (φ ⬝ᵥ ηx) ^ 2 + ty * (φ ⬝ᵥ ηy) ^ 2 + tz * (φ ⬝ᵥ ηz) ^ 2) := by
    rw [hWdef]
    simp only [Matrix.add_mulVec, dotProduct_add, quadForm_smul_atomMatrix]
    have hdiag : φ ⬝ᵥ (Matrix.diagonal ![t4, t5, t6] *ᵥ φ)
        = t4 * φ 0 ^ 2 + t5 * φ 1 ^ 2 + t6 * φ 2 ^ 2 := by
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
        Fin.sum_univ_three]
      ring
    rw [hdiag]
    ring
  -- the bounds
  have hb1 : t4 * φ 0 ^ 2 + t5 * φ 1 ^ 2 + t6 * φ 2 ^ 2 ≤ tcap * (φ ⬝ᵥ φ) := by
    have hφφ' : φ ⬝ᵥ φ = φ 0 ^ 2 + φ 1 ^ 2 + φ 2 ^ 2 := by
      simp only [dotProduct, Fin.sum_univ_three]
      ring
    rw [hφφ']
    nlinarith [mul_nonneg (sub_nonneg.mpr h4o) (sq_nonneg (φ 0)),
      mul_nonneg (sub_nonneg.mpr h5o) (sq_nonneg (φ 1)),
      mul_nonneg (sub_nonneg.mpr h6o) (sq_nonneg (φ 2))]
  have hcs : ∀ η : Fin 3 → ℝ, (φ ⬝ᵥ η) ^ 2 ≤ (η ⬝ᵥ η) * (φ ⬝ᵥ φ) := by
    intro η
    have h := dotProduct_sq_le_mul φ η
    nlinarith [h]
  have hb2 : tx * (φ ⬝ᵥ ηx) ^ 2 ≤ tx * (ηx ⬝ᵥ ηx) * (φ ⬝ᵥ φ) := by
    have := hcs ηx
    nlinarith
  have hb3 : ty * (φ ⬝ᵥ ηy) ^ 2 ≤ ty * (ηy ⬝ᵥ ηy) * (φ ⬝ᵥ φ) := by
    have := hcs ηy
    nlinarith
  have hb4 : tz * (φ ⬝ᵥ ηz) ^ 2 ≤ tz * (ηz ⬝ᵥ ηz) * (φ ⬝ᵥ φ) := by
    have := hcs ηz
    nlinarith
  -- assemble: (φ⬝φ) ≤ [to + Σ t|η|²]·(φ⬝φ), divide
  have hchain : φ ⬝ᵥ φ
      ≤ (tcap + (tx * (ηx ⬝ᵥ ηx) + ty * (ηy ⬝ᵥ ηy) + tz * (ηz ⬝ᵥ ηz)))
        * (φ ⬝ᵥ φ) := by
    have h1 : φ ⬝ᵥ φ ≤ φ ⬝ᵥ (W *ᵥ φ) := by
      rw [hsub] at hφform
      linarith
    rw [hWform] at h1
    nlinarith [h1]
  nlinarith [hchain, hφφ]

/-- **THE SCHUR EXCESS IS NONNEGATIVE.**  For positive definite `A` the
diagonal dominates the inverse-diagonal reciprocal: `1/(A⁻¹)_dd ≤ A_dd`. -/
theorem posDef_schur_diag_nonneg {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A.PosDef) (d : Fin 3) :
    1 / (A⁻¹) d d ≤ A d d := by
  have hpos : 0 < (A⁻¹) d d := hA.inv.diag_pos
  have hkey := posDef_diag_mul_inv_diag hA d
  rw [div_le_iff₀ hpos]
  linarith

/-- **THE FRAME BOUND.**  A weighted atom inside a positive definite moment
matrix reads its inverse at most one over its weight: if `W − t·ηηᵀ ⪰ 0` and
`t > 0`, then `t·(ηᵀW⁻¹η) ≤ 1`.  This caps the corner scale of the pencil
arena: `λ = P + Q − 2 ≤ 1/t_y + 1/t_z − 2`. -/
theorem posDef_frame_reading_le {W : Matrix (Fin 3) (Fin 3) ℝ}
    (hW : W.PosDef) {t : ℝ} (ht : 0 < t) {η : Fin 3 → ℝ}
    (hpsd : (W - t • atomMatrix η).PosSemidef) :
    t * (η ⬝ᵥ (W⁻¹ *ᵥ η)) ≤ 1 := by
  set ψ : Fin 3 → ℝ := W⁻¹ *ᵥ η with hψ
  have hWψ : W *ᵥ ψ = η := by
    rw [hψ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (ne_of_gt hW.det_pos)), Matrix.one_mulVec]
  set P : ℝ := η ⬝ᵥ (W⁻¹ *ᵥ η) with hP
  have hψη : ψ ⬝ᵥ η = P := by
    rw [hψ, hP, dotProduct_comm]
  have hψWψ : ψ ⬝ᵥ (W *ᵥ ψ) = P := by rw [hWψ, hψη]
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ψ
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hψWψ] at hq
  have hquad : ψ ⬝ᵥ ((t • atomMatrix η) *ᵥ ψ) = t * (ψ ⬝ᵥ η) ^ 2 :=
    quadForm_smul_atomMatrix t η ψ
  rw [hquad, hψη] at hq
  have hPnn : 0 ≤ P := by
    rw [hP]
    exact inverseForm_nonneg hW η
  nlinarith [hq, hPnn]

/-! ## 3. The transverse floor -/

/-- **THE TRANSVERSE FLOOR.**  In the pencil data of the both-light cell —
moment matrix `W`, gaps `A_y = 1 − W + η_yη_yᵀ` and `A_z`, the normalization
`η_xᵀW⁻¹η_x = 1` — the six diagonal floors and the seventh floor
`det(1−W) ≤ 0` force transverse energy:

  `(t₄+t₅+t₆)·(t₄+t₅+t₆ − tcap)
     ≤ t_y·Σ_d(A_y,dd − 1/(A_y⁻¹)_dd) + t_z·Σ_d(A_z,dd − 1/(A_z⁻¹)_dd)` ,

`tcap` any upper bound of the three outside weights.  The right side is a
sum of nonnegative Schur excesses; the left side is positive whenever two
outside weights are.  The floors force the arena away from every collapse
ray at a rate set by the two smaller outside weights. -/
theorem transverse_floor
    {tx ty tz t4 t5 t6 tcap : ℝ} {ηx ηy ηz : Fin 3 → ℝ}
    (htx : 0 ≤ tx) (hty : 0 ≤ ty) (htz : 0 ≤ tz)
    (ht4 : 0 ≤ t4) (ht5 : 0 ≤ t5) (ht6 : 0 ≤ t6)
    (hsum : tx + ty + tz + t4 + t5 + t6 = 1)
    (h4o : t4 ≤ tcap) (h5o : t5 ≤ tcap) (h6o : t6 ≤ tcap)
    (hW : (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
        + ty • atomMatrix ηy + tz • atomMatrix ηz).PosDef)
    (hxlink : ηx ⬝ᵥ ((Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
        + ty • atomMatrix ηy + tz • atomMatrix ηz)⁻¹ *ᵥ ηx) = 1)
    (hAy : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
          + ty • atomMatrix ηy + tz • atomMatrix ηz)
        + atomMatrix ηy).PosDef)
    (hAz : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
          + ty • atomMatrix ηy + tz • atomMatrix ηz)
        + atomMatrix ηz).PosDef)
    (hfY : ∀ d, 1 ≤ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
          + ty • atomMatrix ηy + tz • atomMatrix ηz)
        + atomMatrix ηy)⁻¹) d d)
    (hfZ : ∀ d, 1 ≤ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
          + ty • atomMatrix ηy + tz • atomMatrix ηz)
        + atomMatrix ηz)⁻¹) d d)
    (h7 : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
          + ty • atomMatrix ηy + tz • atomMatrix ηz)).det ≤ 0) :
    (t4 + t5 + t6) * (t4 + t5 + t6 - tcap)
      ≤ ty * (∑ d, (((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
              + ty • atomMatrix ηy + tz • atomMatrix ηz)
            + atomMatrix ηy) d d
          - 1 / ((((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
              + ty • atomMatrix ηy + tz • atomMatrix ηz)
            + atomMatrix ηy)⁻¹) d d)))
        + tz * (∑ d, (((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
              + ty • atomMatrix ηy + tz • atomMatrix ηz)
            + atomMatrix ηz) d d
          - 1 / ((((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - (Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
              + ty • atomMatrix ηy + tz • atomMatrix ηz)
            + atomMatrix ηz)⁻¹) d d))) := by
  classical
  set W : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![t4, t5, t6] + tx • atomMatrix ηx
      + ty • atomMatrix ηy + tz • atomMatrix ηz with hWdef
  set Ay : Matrix (Fin 3) (Fin 3) ℝ := 1 - W + atomMatrix ηy with hAydef
  set Az : Matrix (Fin 3) (Fin 3) ℝ := 1 - W + atomMatrix ηz with hAzdef
  set S : Fin 3 → ℝ :=
    fun d => tx * ηx d ^ 2 + ty * ηy d ^ 2 + tz * ηz d ^ 2 with hSdef
  set TY : Fin 3 → ℝ := fun d => Ay d d - 1 / ((Ay⁻¹) d d) with hTYdef
  set TZ : Fin 3 → ℝ := fun d => Az d d - 1 / ((Az⁻¹) d d) with hTZdef
  -- entry computations
  have hWdd : ∀ d, W d d = (![t4, t5, t6] : Fin 3 → ℝ) d + S d := by
    intro d
    rw [hWdef, hSdef]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  have hAydd : ∀ d, Ay d d = 1 - W d d + ηy d ^ 2 := by
    intro d
    rw [hAydef]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq,
      atomMatrix, Matrix.vecMulVec_apply]
    ring
  have hAzdd : ∀ d, Az d d = 1 - W d d + ηz d ^ 2 := by
    intro d
    rw [hAzdef]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq,
      atomMatrix, Matrix.vecMulVec_apply]
    ring
  -- the gamma cap
  have hgam : ∀ d, ηx d ^ 2 ≤ W d d := by
    intro d
    set e : Fin 3 → ℝ := Pi.single d 1 with he
    set u : Fin 3 → ℝ := W⁻¹ *ᵥ ηx with hu
    have hmove : ∀ a b : Fin 3 → ℝ, a ⬝ᵥ (W *ᵥ b) = (W *ᵥ a) ⬝ᵥ b := by
      intro a b
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        transpose_eq_of_isHermitian hW.1]
    have hWu : W *ᵥ u = ηx := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        (isUnit_iff_ne_zero.mpr (ne_of_gt hW.det_pos)), Matrix.one_mulVec]
    have hCS := posSemidef_bilinear_sq_le hW.posSemidef u e
    have h1 : u ⬝ᵥ (W *ᵥ e) = ηx d := by
      rw [hmove, hWu, he, dotProduct_single_one]
    have h2 : u ⬝ᵥ (W *ᵥ u) = 1 := by
      rw [hWu, hu, dotProduct_comm, hxlink]
    have h3 : e ⬝ᵥ (W *ᵥ e) = W d d := by
      rw [he, single_one_dotProduct, Matrix.mulVec_single_one]
      simp
    rw [h1, h2, h3, one_mul] at hCS
    exact hCS
  -- the floor caps
  have hcapY : ∀ d, ηy d ^ 2 ≤ (![t4, t5, t6] : Fin 3 → ℝ) d + S d + TY d := by
    intro d
    have hr : 0 < (Ay⁻¹) d d := hAy.inv.diag_pos
    have h1r : 1 / ((Ay⁻¹) d d) ≤ 1 := by
      rw [div_le_one hr]
      exact hfY d
    have hey : ηy d ^ 2 = Ay d d - 1 + W d d := by
      rw [hAydd d]; ring
    have hAy2 : Ay d d = 1 / ((Ay⁻¹) d d) + TY d := by
      rw [hTYdef]; ring
    rw [hey, hAy2, hWdd d]
    linarith
  have hcapZ : ∀ d, ηz d ^ 2 ≤ (![t4, t5, t6] : Fin 3 → ℝ) d + S d + TZ d := by
    intro d
    have hr : 0 < (Az⁻¹) d d := hAz.inv.diag_pos
    have h1r : 1 / ((Az⁻¹) d d) ≤ 1 := by
      rw [div_le_one hr]
      exact hfZ d
    have hez : ηz d ^ 2 = Az d d - 1 + W d d := by
      rw [hAzdd d]; ring
    have hAz2 : Az d d = 1 / ((Az⁻¹) d d) + TZ d := by
      rw [hTZdef]; ring
    rw [hez, hAz2, hWdd d]
    linarith
  -- the slot inequality
  have hslot : ∀ d, S d * (1 - (tx + ty + tz))
      ≤ (tx + ty + tz) * (![t4, t5, t6] : Fin 3 → ℝ) d
        + ty * TY d + tz * TZ d := by
    intro d
    have hx := hgam d
    rw [hWdd d] at hx
    have h1 := mul_le_mul_of_nonneg_left hx htx
    have h2 := mul_le_mul_of_nonneg_left (hcapY d) hty
    have h3 := mul_le_mul_of_nonneg_left (hcapZ d) htz
    have hSd : S d = tx * ηx d ^ 2 + ty * ηy d ^ 2 + tz * ηz d ^ 2 := by
      rw [hSdef]
    nlinarith [h1, h2, h3]
  -- the seventh-floor energy
  have henergy : 1 ≤ tcap
      + (tx * (ηx ⬝ᵥ ηx) + ty * (ηy ⬝ᵥ ηy) + tz * (ηz ⬝ᵥ ηz)) := by
    exact seventh_floor_energy htx hty htz h4o h5o h6o h7
  have hStot : tx * (ηx ⬝ᵥ ηx) + ty * (ηy ⬝ᵥ ηy) + tz * (ηz ⬝ᵥ ηz)
      = S 0 + S 1 + S 2 := by
    simp only [hSdef, dotProduct, Fin.sum_univ_three]
    ring
  -- assemble
  have hs0 := hslot 0
  have hs1 := hslot 1
  have hs2 := hslot 2
  have htv : (![t4, t5, t6] : Fin 3 → ℝ) 0 = t4 ∧
      (![t4, t5, t6] : Fin 3 → ℝ) 1 = t5 ∧
      (![t4, t5, t6] : Fin 3 → ℝ) 2 = t6 := by
    refine ⟨rfl, rfl, rfl⟩
  obtain ⟨hv0, hv1, hv2⟩ := htv
  rw [hv0] at hs0; rw [hv1] at hs1; rw [hv2] at hs2
  have hsumTY : (∑ d, TY d) = TY 0 + TY 1 + TY 2 := Fin.sum_univ_three TY
  have hsumTZ : (∑ d, TZ d) = TZ 0 + TZ 1 + TZ 2 := Fin.sum_univ_three TZ
  rw [hsumTY, hsumTZ]
  have htau : tx + ty + tz ≤ 1 := by linarith
  have hSnn : 0 ≤ S 0 + S 1 + S 2 := by
    have : ∀ d, 0 ≤ S d := fun d => by
      rw [hSdef]
      have := sq_nonneg (ηx d); have := sq_nonneg (ηy d); have := sq_nonneg (ηz d)
      positivity
    linarith [this 0, this 1, this 2]
  rw [hStot] at henergy
  nlinarith [hs0, hs1, hs2, henergy, htau, hSnn,
    mul_le_mul_of_nonneg_left henergy (by linarith : (0:ℝ) ≤ 1 - (tx+ty+tz))]

end Gtz
