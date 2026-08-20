import Gtz.Wave.SeesawExchangeFloor
import Gtz.Wave.OutsideTriadDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# The weight-gap determinant law: where the `(1 − t_max)` factor comes from

The measured roof of the both-light cell is the `det K = 0` boundary under a
weight collapse onto ONE outside atom, and the measured deficit of the seven
floors is LINEAR in `1 − t_max` (ratio `0.10`–`0.43` over ten orders of
magnitude in the collapsing scale).  This module lands the exact algebra
behind that rate.

## The multilinear determinant expansion

Three rank-one atoms added to a `3×3` base expand into eight terms
(`Gtz.det_add_three_atomMatrix_fin_three`): the base determinant, three
adjugate readings, three cross readings, and one squared triple product.  A
polynomial identity — no hypotheses, no positivity.

## The weight-gap law

At a `Z1` corner Parseval reshapes the outside pencil at parameter one into
the outside gap plus the weighted inside atoms
(`Gtz.corner_oneAxisZero_weightGap_reshape`):

  `M_o − N_out = K + t_x G_x + t_y G_y + t_z G_z` ,  `K = S_{Cᶜ} − 1` ,

and the landed triad characteristic identity evaluates the same determinant
as `Π_d (1 − t_d) · det M_o`.  Combining with the expansion and the corner
pins — the cross pin `(g_y × g_z)(g_y × g_z)ᵀ = (1+lam)·g_xg_xᵀ` and the
erased orthogonality — gives the WEIGHT-GAP LAW
(`Gtz.corner_oneAxisZero_weightGap_det_law`):

  `Π_d (1 − t_d) · det M_o
     = det K + t_x·g_xᵀ(adj K)g_x + t_y·g_yᵀ(adj K)g_y + t_z·g_zᵀ(adj K)g_z
       + t_x t_y·(g_x×g_y)ᵀK(g_x×g_y) + t_x t_z·(g_x×g_z)ᵀK(g_x×g_z)
       + t_y t_z·(1+lam)·kxx + t_x t_y t_z·(1+lam)` ,

with `kxx = g_xᵀ K g_x` the erased energy.  Every term is explicit and the
left side carries the factor `1 − t_d` at EVERY outside atom: this is the
exact source of the measured linear rate.

## The tie floor

On the both-light cell a tie forces `det K ≤ 0` (the member determinant floor
at the inside pivot, landed).  The law then reads as a floor on the weighted
positive part (`Gtz.corner_oneAxisZero_bothLight_weightGap_floor`):

  `Π_d (1 − t_d) · det M_o ≤ (the seven weighted terms)` ,

the `(1 − t_max)`-carrying inequality the residual needs.  Because
`det M_o = (det Q)²  ≥ 0` for three outside atoms and the product of the
outside slacks is positive, the left side is a genuine positive floor
whenever the outside triple is nondegenerate.

## The Parseval reading rail

The weighted readings of ANY invertible gap total its inverse trace
(`Gtz.weighted_reading_total_eq_trace`): `Σ_c t_c·g_cᵀA⁻¹g_c = tr A⁻¹`.  With
the reading total of a four-set this pins the trace at a tie from below
(`Gtz.tie_fourSet_trace_ge_one`): `tr (S_F − 1)⁻¹ ≥ 1`.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The multilinear determinant expansion -/

/-- **THE THREE-ATOM DETERMINANT EXPANSION.**  Adding three weighted rank-one
atoms to a `3×3` base expands multilinearly into the base determinant, the
three adjugate readings, the three cross readings, and the squared triple
product:

  `det(M + t₁v₁v₁ᵀ + t₂v₂v₂ᵀ + t₃v₃v₃ᵀ)
     = det M + Σ tᵢ·vᵢᵀ(adj M)vᵢ + Σ_{i<j} tᵢtⱼ·(vᵢ×vⱼ)ᵀM(vᵢ×vⱼ)
       + t₁t₂t₃·((v₁×v₂)·v₃)²` .

A polynomial identity — no hypotheses. -/
theorem det_add_three_atomMatrix_fin_three (M : Matrix (Fin 3) (Fin 3) ℝ)
    (t₁ t₂ t₃ : ℝ) (v₁ v₂ v₃ : Fin 3 → ℝ) :
    (M + t₁ • atomMatrix v₁ + t₂ • atomMatrix v₂ + t₃ • atomMatrix v₃).det
      = M.det
        + (t₁ * (v₁ ⬝ᵥ (M.adjugate *ᵥ v₁))
          + t₂ * (v₂ ⬝ᵥ (M.adjugate *ᵥ v₂))
          + t₃ * (v₃ ⬝ᵥ (M.adjugate *ᵥ v₃)))
        + (t₁ * t₂ * (crossProduct v₁ v₂ ⬝ᵥ (M *ᵥ crossProduct v₁ v₂))
          + t₁ * t₃ * (crossProduct v₁ v₃ ⬝ᵥ (M *ᵥ crossProduct v₁ v₃))
          + t₂ * t₃ * (crossProduct v₂ v₃ ⬝ᵥ (M *ᵥ crossProduct v₂ v₃)))
        + t₁ * t₂ * t₃ * (crossProduct v₁ v₂ ⬝ᵥ v₃) ^ 2 := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    cross_apply]
  ring

/-! ## 2. The Parseval reading rail -/

/-- **THE WEIGHTED READING RAIL.**  The weighted readings of any invertible
gap total its inverse trace — Parseval read at the inverse.  An identity at
every design size and every base. -/
theorem weighted_reading_total_eq_trace (D : WeightedDesign m 3)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c)) = Matrix.trace A⁻¹ := by
  have htr : Matrix.trace (A⁻¹ * ∑ c, D.weight c • atomMatrix (D.atom c))
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ (A⁻¹ *ᵥ D.atom c)) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_smul_comm, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  rw [← htr, D.isParseval, Matrix.mul_one]

/-- **THE TIE PINS THE TRACE ABOVE ONE.**  At a tie the four member floors of
a strictly dominating four-set saturate the reading total, so the inverse gap
carries trace at least one. -/
theorem tie_fourSet_trace_ge_one (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) :
    1 ≤ Matrix.trace (subsetSum D F - 1)⁻¹ := by
  classical
  have hdet : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have htotal := subset_reading_total D F hdet
  have hones : ∑ _a ∈ F, (1 : ℝ) = 4 := by
    rw [Finset.sum_const, hF]
    norm_num
  have hfloors : (4 : ℝ)
      ≤ ∑ a ∈ F, D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a) := by
    rw [← hones]
    exact Finset.sum_le_sum fun a ha => fourSet_leverage_ge_one D htie F hF hPD ha
  linarith [htotal, hfloors]

/-! ## 3. The Parseval reshape of the outside pencil -/

/-- **THE WEIGHT-GAP RESHAPE.**  Parseval turns the outside pencil at
parameter one into the outside gap plus the weighted inside atoms:

  `S_{Cᶜ} − Σ_{d ∈ Cᶜ} t_d G_d = (S_{Cᶜ} − 1) + t_x G_x + t_y G_y + t_z G_z` . -/
theorem corner_oneAxisZero_weightGap_reshape (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
        - ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d • atomMatrix (D.atom d)
      = (subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1)
        + D.weight x • atomMatrix (D.atom x)
        + D.weight y • atomMatrix (D.atom y)
        + D.weight z • atomMatrix (D.atom z) := by
  classical
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun c => D.weight c • atomMatrix (D.atom c))
  rw [D.isParseval, sum_triple_eq hxy hxz hyz] at hsplit
  have hout : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d • atomMatrix (D.atom d)
      = 1 - (D.weight x • atomMatrix (D.atom x)
        + (D.weight y • atomMatrix (D.atom y)
          + D.weight z • atomMatrix (D.atom z))) := by
    rw [← hsplit]
    abel
  rw [hout]
  abel

/-! ## 4. The weight-gap determinant law -/

/-- **THE WEIGHT-GAP DETERMINANT LAW.**  At a `Z1` corner the product of the
outside weight slacks against the outside determinant equals the outside gap
determinant plus seven explicit weighted terms:

  `Π_d (1 − t_d) · det S_{Cᶜ}
     = det K + t_x·g_xᵀ(adj K)g_x + t_y·g_yᵀ(adj K)g_y + t_z·g_zᵀ(adj K)g_z
       + t_x t_y·(g_x×g_y)ᵀK(g_x×g_y) + t_x t_z·(g_x×g_z)ᵀK(g_x×g_z)
       + t_y t_z·(1+lam)·(g_xᵀKg_x) + t_x t_y t_z·(1+lam)` ,  `K = S_{Cᶜ} − 1` .

Tie-free.  The left side carries the slack `1 − t_d` of EVERY outside atom:
the exact algebraic source of the measured linear collapse rate of the
both-light roof. -/
theorem corner_oneAxisZero_weightGap_det_law (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    (∏ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (1 - D.weight d))
        * (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)).det
      = (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det
        + (D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom x))
          + D.weight y
            * (D.atom y ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom y))
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom z)))
        + (D.weight x * D.weight y
            * (crossProduct (D.atom x) (D.atom y) ⬝ᵥ
                ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ crossProduct (D.atom x) (D.atom y)))
          + D.weight x * D.weight z
            * (crossProduct (D.atom x) (D.atom z) ⬝ᵥ
                ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ crossProduct (D.atom x) (D.atom z)))
          + D.weight y * D.weight z
            * ((1 + lam)
              * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ D.atom x))))
        + D.weight x * D.weight y * D.weight z * (1 + lam) := by
  classical
  set K : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1 with hK
  -- the triad characteristic identity at parameter one
  have hCc : ((({x, y, z} : Finset (Fin 6))ᶜ) : Finset (Fin 6)).card = 3 :=
    card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)
  have hchar := outside_triad_char_identity D ({x, y, z} : Finset (Fin 6)) hCc 1
  simp only [one_smul, one_mul] at hchar
  -- the Parseval reshape
  have hreshape := corner_oneAxisZero_weightGap_reshape D hxy hxz hyz
  rw [hreshape, ← hK] at hchar
  -- the multilinear expansion
  have hexp := det_add_three_atomMatrix_fin_three K (D.weight x) (D.weight y)
    (D.weight z) (D.atom x) (D.atom y) (D.atom z)
  -- the cross pin turns the (y, z) cross reading into the erased energy
  have hpin := corner_oneAxisZero_cross_pin D hxy hxz hyz hlam hunit hgap hax haz
  have hcrossyz : crossProduct (D.atom y) (D.atom z) ⬝ᵥ
        (K *ᵥ crossProduct (D.atom y) (D.atom z))
      = (1 + lam) * (D.atom x ⬝ᵥ (K *ᵥ D.atom x)) := by
    calc crossProduct (D.atom y) (D.atom z) ⬝ᵥ
          (K *ᵥ crossProduct (D.atom y) (D.atom z))
        = Matrix.trace (K * atomMatrix (crossProduct (D.atom y) (D.atom z))) :=
          (trace_mul_atomMatrix K _).symm
      _ = Matrix.trace (K * ((1 + lam) • atomMatrix (D.atom x))) := by rw [hpin]
      _ = (1 + lam) * Matrix.trace (K * atomMatrix (D.atom x)) := by
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      _ = (1 + lam) * (D.atom x ⬝ᵥ (K *ᵥ D.atom x)) := by
          rw [trace_mul_atomMatrix]
  -- the squared triple product is the gap scale, by the same pin
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin 6))) hax
  have htriple : (crossProduct (D.atom x) (D.atom y) ⬝ᵥ D.atom z) ^ 2 = 1 + lam := by
    have hrot : crossProduct (D.atom x) (D.atom y) ⬝ᵥ D.atom z
        = crossProduct (D.atom y) (D.atom z) ⬝ᵥ D.atom x := by
      simp only [cross_apply, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring
    have hpinread := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) ℝ => D.atom x ⬝ᵥ (M *ᵥ D.atom x)) hpin
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hpinread
    rw [show atomMatrix (crossProduct (D.atom y) (D.atom z))
        = Matrix.vecMulVec (crossProduct (D.atom y) (D.atom z))
          (crossProduct (D.atom y) (D.atom z)) from rfl,
      quadForm_atomMatrix,
      show atomMatrix (D.atom x) = Matrix.vecMulVec (D.atom x) (D.atom x) from rfl,
      quadForm_atomMatrix, hlev] at hpinread
    rw [hrot]
    linarith [hpinread]
  rw [hexp, hcrossyz, htriple] at hchar
  rw [← hchar]

/-! ## 5. The tie floor of the both-light cell -/

/-- **THE WEIGHT-GAP FLOOR.**  At a both-light tie the member determinant
floor at the inside pivot forces `det K ≤ 0`, so the weight-gap law becomes a
floor on the weighted positive part:

  `Π_d (1 − t_d)·det S_{Cᶜ} ≤ (the seven weighted terms)` .

Every factor `1 − t_d` on the left is the slack of one outside weight: as the
outside mass collapses onto a single atom the left side vanishes LINEARLY in
`1 − t_max`, which is the measured rate of the both-light roof (ratio
`0.10`–`0.43` across ten orders of magnitude). -/
theorem corner_oneAxisZero_bothLight_weightGap_floor (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (∏ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (1 - D.weight d))
        * (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)).det
      ≤ (D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom x))
          + D.weight y
            * (D.atom y ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom y))
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom z)))
        + (D.weight x * D.weight y
            * (crossProduct (D.atom x) (D.atom y) ⬝ᵥ
                ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ crossProduct (D.atom x) (D.atom y)))
          + D.weight x * D.weight z
            * (crossProduct (D.atom x) (D.atom z) ⬝ᵥ
                ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ crossProduct (D.atom x) (D.atom z)))
          + D.weight y * D.weight z
            * ((1 + lam)
              * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ D.atom x))))
        + D.weight x * D.weight y * D.weight z * (1 + lam) := by
  have hlaw := corner_oneAxisZero_weightGap_det_law D hxy hxz hyz hlam hunit
    hgap hax haz
  have hdetK := (corner_oneAxisZero_bothLight_member_det_floor D htie hxy hxz
    hyz hAy hAz).2.2
  linarith [hlaw, hdetK]

/-- **The outside determinant is a square.**  Three outside atoms make the
outside sum a Gram matrix, so its determinant is the squared triple product —
nonnegative, and positive exactly off the degenerate outside triple. -/
theorem corner_outside_det_eq_triple_sq (D : WeightedDesign m 3)
    {d₁ d₂ d₃ : Fin m} (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃)
    {C : Finset (Fin m)} (hC : (Cᶜ : Finset (Fin m)) = {d₁, d₂, d₃}) :
    (subsetSum D (Cᶜ : Finset (Fin m))).det
      = (crossProduct (D.atom d₁) (D.atom d₂) ⬝ᵥ D.atom d₃) ^ 2 := by
  classical
  have hsum : subsetSum D (Cᶜ : Finset (Fin m))
      = atomMatrix (D.atom d₁) + atomMatrix (D.atom d₂)
        + atomMatrix (D.atom d₃) := by
    rw [subsetSum, hC, sum_triple_eq h12 h13 h23]
    abel
  rw [hsum]
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.add_apply, cross_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring


/-! ## 6. The outside slack product is a positive floor -/

/-- Three slacks in the unit interval beat the total slack: the
Weierstrass product bound at three factors. -/
theorem prod_three_one_sub_ge {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) :
    1 - (a + b + c) ≤ (1 - a) * (1 - b) * (1 - c) := by
  nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
    mul_nonneg (mul_nonneg ha hb) hc]

/-- **THE OUTSIDE SLACK FLOOR.**  The product of the outside weight slacks is
at least the inside weight total: as the outside mass collapses onto one atom
the product stays above `t_x + t_y + t_z`, and it vanishes only with the
inside weights. -/
theorem corner_oneAxisZero_outside_slack_floor (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    D.weight x + D.weight y + D.weight z
      ≤ ∏ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), (1 - D.weight d) := by
  classical
  have hCc : ((({x, y, z} : Finset (Fin 6))ᶜ) : Finset (Fin 6)).card = 3 :=
    card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)
  obtain ⟨d₁, d₂, d₃, h12, h13, h23, hset⟩ := Finset.card_eq_three.mp hCc
  have hsum := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6)) D.weight
  rw [D.weight_sum_one, sum_triple_eq hxy hxz hyz] at hsum
  have houts : D.weight d₁ + D.weight d₂ + D.weight d₃
      = 1 - (D.weight x + D.weight y + D.weight z) := by
    have hcompl : ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d
        = D.weight d₁ + (D.weight d₂ + D.weight d₃) := by
      rw [hset, sum_triple_eq h12 h13 h23]
    rw [hcompl] at hsum
    linarith
  have hlt : ∀ c : Fin 6, D.weight c ≤ 1 := fun c => by
    have hle := Finset.single_le_sum (f := D.weight)
      (fun e _ => (D.weight_pos e).le) (Finset.mem_univ c)
    rw [D.weight_sum_one] at hle
    exact hle
  rw [hset, Finset.prod_insert (by simp [h12, h13]),
    Finset.prod_insert (by simp [h23]), Finset.prod_singleton]
  have hbound := prod_three_one_sub_ge (D.weight_pos d₁).le (D.weight_pos d₂).le
    (D.weight_pos d₃).le (hlt d₁) (hlt d₂) (hlt d₃)
  have hstep : (1 - D.weight d₁) * ((1 - D.weight d₂) * (1 - D.weight d₃))
      = (1 - D.weight d₁) * (1 - D.weight d₂) * (1 - D.weight d₃) := by ring
  rw [hstep]
  linarith [hbound, houts]


/-- **THE POSITIVE WEIGHT-GAP FLOOR.**  Combining the weight-gap floor, the
outside slack floor and the square form of the outside determinant, a
both-light tie must pay the INSIDE weight total against the squared outside
triple product:

  `(t_x + t_y + t_z)·((q_1×q_2)·q_3)² ≤ (the seven weighted terms)` .

Both sides vanish only with the weights: the left side is a strictly positive
floor whenever the outside triple is nondegenerate, and it degenerates
exactly as the inside weights collapse — the `(5,3)` boundary limit.  This is
the tie-free `(1 − t_max)`-carrying constraint of the both-light cell in
closed determinant form. -/
theorem corner_oneAxisZero_bothLight_weightGap_positive_floor
    (D : WeightedDesign 6 3) (htie : IsTie D) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    {d₁ d₂ d₃ : Fin 6} (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃)
    (hset : ((({x, y, z} : Finset (Fin 6))ᶜ) : Finset (Fin 6)) = {d₁, d₂, d₃}) :
    (D.weight x + D.weight y + D.weight z)
        * (crossProduct (D.atom d₁) (D.atom d₂) ⬝ᵥ D.atom d₃) ^ 2
      ≤ (D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom x))
          + D.weight y
            * (D.atom y ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom y))
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ)
                - 1).adjugate *ᵥ D.atom z)))
        + (D.weight x * D.weight y
            * (crossProduct (D.atom x) (D.atom y) ⬝ᵥ
                ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ crossProduct (D.atom x) (D.atom y)))
          + D.weight x * D.weight z
            * (crossProduct (D.atom x) (D.atom z) ⬝ᵥ
                ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ crossProduct (D.atom x) (D.atom z)))
          + D.weight y * D.weight z
            * ((1 + lam)
              * (D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
                  *ᵥ D.atom x))))
        + D.weight x * D.weight y * D.weight z * (1 + lam) := by
  have hfloor := corner_oneAxisZero_bothLight_weightGap_floor D htie hxy hxz hyz
    hlam hunit hgap hax haz hAy hAz
  have hslack := corner_oneAxisZero_outside_slack_floor D hxy hxz hyz
  have hdet := corner_outside_det_eq_triple_sq D h12 h13 h23 hset
  have hsq : (0 : ℝ) ≤ (crossProduct (D.atom d₁) (D.atom d₂) ⬝ᵥ D.atom d₃) ^ 2 :=
    sq_nonneg _
  rw [hdet] at hfloor
  nlinarith [hfloor, hslack, hsq]

/-! ## 8. Calibration at the witness -/

/-- The outside determinant of the witness is `64`: the outside triple of the
`Z1` witness is nondegenerate, so its weight-gap floor is a strictly positive
constraint. -/
theorem oneAxisZeroWitness_outside_det :
    (subsetSum oneAxisZeroWitness (({0, 1, 2} : Finset (Fin 6))ᶜ)).det = 64 := by
  have hcompl : ((({0, 1, 2} : Finset (Fin 6))ᶜ) : Finset (Fin 6)) = {3, 4, 5} := by
    decide
  have hsum : subsetSum oneAxisZeroWitness (({0, 1, 2} : Finset (Fin 6))ᶜ)
      = !![4, 0, 0; 0, 4, 0; 0, 0, 4] := by
    rw [hcompl, subsetSum]
    ext rowIndex colIndex
    rw [show ({3, 4, 5} : Finset (Fin 6))
        = insert 3 (insert 4 ({5} : Finset (Fin 6))) from rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [atomMatrix, Matrix.vecMulVec_apply, oneAxisZeroWitness_atom,
        oneAxisZeroWitnessAtom, Matrix.add_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
  rw [hsum, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

end Gtz
