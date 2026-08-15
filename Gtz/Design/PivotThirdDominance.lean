/-
# The pivot-third dominance law

A selection of a direction chart is strictly dominating as soon as the three
labels it omits each carry a full pivot below one third.  No weight cap, no
determinant, no frame and no rank condition enter the hypothesis.

The law is the H-matrix reading of the complement matrix.  Plain diagonal
dominance compares the diagonal entry of an omitted label with its own
off-diagonal row, and that comparison is BOOST-SENSITIVE: the row of `a` carries
the boosts of the labels it points at, so one heavy partner defeats the criterion
however small the pivots are.  The scaled kill removes the sensitivity at exactly
one scale.  Weighting the label `c` by the reciprocal square root of its boost
turns every off-diagonal entry into a pivot pairing, and what is left is a
statement about pivots alone.

The threshold one third is sharp for this route.  At omitted count three the
criterion reads `sqrt (pi a) * (sqrt (pi b) + sqrt (pi c)) < 1 - pi a`, and at a
common value `p` that is `2 * p < 1 - p`.
-/
import Gtz.Design.ComplementDiagonalDominance
import Gtz.Design.PivotOnlyDominance

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## 1. The resolvent is a symmetric positive semidefinite form -/

/-- The full-selection gap of a chart is symmetric, so its inverse is too. -/
theorem transpose_univGap_inv (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) :
    ((directionChartGap direction mass weight Finset.univ)⁻¹)ᵀ
      = (directionChartGap direction mass weight Finset.univ)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, directionChartGap_transpose]

/-- The resolvent pairing of two probes is symmetric. -/
theorem resolvent_pairing_comm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (u v : Fin 3 → ℝ) :
    u ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ v)
      = v ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ u) :=
  dotProduct_mulVec_comm_of_transpose (transpose_univGap_inv direction mass weight) u v

/-- The resolvent form is nonnegative at every probe. -/
theorem resolvent_quadForm_nonneg (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (u : Fin 3 → ℝ) :
    0 ≤ u ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ u) := by
  simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.mp huniv.inv.posSemidef).2 u

/-- **Cauchy--Schwarz through the resolvent.**  The squared inverse form of two
labels is at most the product of their own inverse forms.

The corpus carries `pivot_prices_overlap`, which pairs the resolvent against the
gap itself.  This is the pairing INSIDE the resolvent, which that lemma does not
supply. -/
theorem sq_fullInverseForm_le_mul (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (a b : Fin size) :
    (fullInverseForm direction mass weight a b) ^ 2
      ≤ fullInverseForm direction mass weight a a
        * fullInverseForm direction mass weight b b := by
  classical
  set faa := fullInverseForm direction mass weight a a with hfaa
  set fbb := fullInverseForm direction mass weight b b with hfbb
  set fab := fullInverseForm direction mass weight a b with hfab
  have hcross := resolvent_pairing_comm direction mass weight (direction b) (direction a)
  have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * faa + 2 * t * fab + fbb := by
    intro t
    have hnn := resolvent_quadForm_nonneg direction mass weight huniv
      (t • direction a + direction b)
    have hexpand :
        (t • direction a + direction b) ⬝ᵥ
            ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ
              (t • direction a + direction b))
          = t ^ 2 * faa + 2 * t * fab + fbb := by
      simp only [hfaa, hfbb, hfab, fullInverseForm, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hcross]
      ring
    rw [hexpand] at hnn
    exact hnn
  have hfaaNonneg : 0 ≤ faa := by
    have hself := resolvent_quadForm_nonneg direction mass weight huniv (direction a)
    simpa [hfaa, fullInverseForm] using hself
  rcases hfaaNonneg.lt_or_eq with hpos | hzero
  · have hmin := hquad (-(fab / faa))
    have hne : faa ≠ 0 := ne_of_gt hpos
    have hexp : (-(fab / faa)) ^ 2 * faa + 2 * (-(fab / faa)) * fab + fbb
        = fbb - fab ^ 2 / faa := by
      field_simp
      ring
    rw [hexp] at hmin
    have hmul : 0 ≤ (fbb - fab ^ 2 / faa) * faa := mul_nonneg hmin hpos.le
    have hclear : (fbb - fab ^ 2 / faa) * faa = fbb * faa - fab ^ 2 := by
      field_simp
    rw [hclear] at hmul
    nlinarith [hmul]
  · have hzero' : faa = 0 := hzero.symm
    have hlin : ∀ t : ℝ, 0 ≤ 2 * t * fab + fbb := by
      intro t
      have hq := hquad t
      rw [hzero'] at hq
      linarith [hq]
    have habZero : fab = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hposab
      · have hbig := hlin ((fbb + 1) / (-2 * fab))
        have hrw : 2 * ((fbb + 1) / (-2 * fab)) * fab = -(fbb + 1) := by
          field_simp
        rw [hrw] at hbig
        linarith [hbig]
      · have hbig := hlin (-(fbb + 1) / (2 * fab))
        have hrw : 2 * (-(fbb + 1) / (2 * fab)) * fab = -(fbb + 1) := by
          field_simp
        rw [hrw] at hbig
        linarith [hbig]
    rw [habZero, hzero']
    simp

/-! ## 2. The pivot pairing bound -/

/-- The pivot of a label is nonnegative when its boost is. -/
theorem fullPivot_nonneg_of_boost (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (a : Fin size) (hboost : 0 ≤ mass a / weight a) :
    0 ≤ fullPivot direction mass weight a :=
  mul_nonneg hboost (fullInverseForm_self_nonneg direction mass weight huniv a)

/-- The absolute inverse form is at most the geometric mean of the diagonals. -/
theorem abs_fullInverseForm_le_sqrt (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (a b : Fin size) :
    |fullInverseForm direction mass weight a b|
      ≤ Real.sqrt (fullInverseForm direction mass weight a a)
        * Real.sqrt (fullInverseForm direction mass weight b b) := by
  have hcs := sq_fullInverseForm_le_mul direction mass weight huniv a b
  have hsqrt : Real.sqrt ((fullInverseForm direction mass weight a b) ^ 2)
      ≤ Real.sqrt (fullInverseForm direction mass weight a a
        * fullInverseForm direction mass weight b b) := Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_sq_eq_abs] at hsqrt
  rwa [Real.sqrt_mul (fullInverseForm_self_nonneg direction mass weight huniv a)] at hsqrt

/-- **The pivot pairing bound.**  With the reciprocal square-root scale the
off-diagonal complement entry of `a b` is bounded by the boost square root of `a`
times the geometric mean of the two pivots. -/
theorem scaledEntry_le_sqrt_pivot_mul (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    {a b : Fin size} (hne : b ≠ a)
    (hra : 0 < mass a / weight a) (hrb : 0 < mass b / weight b) :
    (Real.sqrt (mass b / weight b))⁻¹ * |complementMatrixEntry direction mass weight a b|
      ≤ Real.sqrt (mass a / weight a)
        * (Real.sqrt (fullPivot direction mass weight a)
          * Real.sqrt (fullPivot direction mass weight b)) := by
  have hab : a ≠ b := fun h => hne h.symm
  have hentry : |complementMatrixEntry direction mass weight a b|
      = (mass a / weight a) * (mass b / weight b)
        * |fullInverseForm direction mass weight a b| := by
    rw [complementMatrixEntry_off direction mass weight hab, abs_neg, abs_mul, abs_mul,
      abs_of_pos hra, abs_of_pos hrb]
  have hsa : Real.sqrt (mass a / weight a) * Real.sqrt (mass a / weight a)
      = mass a / weight a := Real.mul_self_sqrt hra.le
  have hsb : Real.sqrt (mass b / weight b) * Real.sqrt (mass b / weight b)
      = mass b / weight b := Real.mul_self_sqrt hrb.le
  have hsbPos : 0 < Real.sqrt (mass b / weight b) := Real.sqrt_pos.mpr hrb
  have hpa : Real.sqrt (fullPivot direction mass weight a)
      = Real.sqrt (mass a / weight a)
        * Real.sqrt (fullInverseForm direction mass weight a a) := by
    rw [fullPivot, Real.sqrt_mul hra.le]
  have hpb : Real.sqrt (fullPivot direction mass weight b)
      = Real.sqrt (mass b / weight b)
        * Real.sqrt (fullInverseForm direction mass weight b b) := by
    rw [fullPivot, Real.sqrt_mul hrb.le]
  have hcs := abs_fullInverseForm_le_sqrt direction mass weight huniv a b
  rw [hentry, hpa, hpb, inv_mul_le_iff₀ hsbPos]
  have hright : Real.sqrt (mass b / weight b)
      * (Real.sqrt (mass a / weight a)
        * (Real.sqrt (mass a / weight a)
            * Real.sqrt (fullInverseForm direction mass weight a a)
          * (Real.sqrt (mass b / weight b)
            * Real.sqrt (fullInverseForm direction mass weight b b))))
      = (Real.sqrt (mass a / weight a) * Real.sqrt (mass a / weight a))
        * (Real.sqrt (mass b / weight b) * Real.sqrt (mass b / weight b))
        * (Real.sqrt (fullInverseForm direction mass weight a a)
          * Real.sqrt (fullInverseForm direction mass weight b b)) := by
    ring
  rw [hright, hsa, hsb]
  exact mul_le_mul_of_nonneg_left hcs (mul_nonneg hra.le hrb.le)

/-! ## 3. The law -/

/-- **THE PIVOT-THIRD DOMINANCE LAW.**  A selection whose three omitted labels
all carry a full pivot below one third is strictly dominating.

Compare `posDef_subsetSum_of_quarterPivotQuarter`, which needs BOTH a weight cap
of one quarter AND a pivot cap of one quarter, and is stated at the design level.
This law drops the weight cap entirely, raises the pivot threshold from one
quarter to one third, and lives on the chart, where no design need exist. -/
theorem posDef_directionChartGap_of_pivotThird (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size))
    (hboost : ∀ label, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hcard : selectedᶜ.card = 3)
    (hpivot : ∀ a ∈ selectedᶜ, fullPivot direction mass weight a < 1 / 3) :
    (directionChartGap direction mass weight selected).PosDef := by
  classical
  set scale : Fin size → ℝ := fun c => (Real.sqrt (mass c / weight c))⁻¹ with hscaleDef
  have hsqrtThird : Real.sqrt (1 / 3) * Real.sqrt (1 / 3) = 1 / 3 :=
    Real.mul_self_sqrt (by norm_num)
  have hpivotSqrtLe : ∀ a ∈ selectedᶜ,
      Real.sqrt (fullPivot direction mass weight a) ≤ Real.sqrt (1 / 3) := fun a ha =>
    Real.sqrt_le_sqrt (hpivot a ha).le
  refine posDef_directionChartGap_of_scaledRowSlack_pos direction mass weight selected scale
    (fun a _ => inv_pos.mpr (Real.sqrt_pos.mpr (hboost a)))
    (fun label _ => hboost label) huniv ?_
  intro a ha
  have hraPos : 0 < mass a / weight a := hboost a
  have hsaPos : 0 < Real.sqrt (mass a / weight a) := Real.sqrt_pos.mpr hraPos
  have hsa : Real.sqrt (mass a / weight a) * Real.sqrt (mass a / weight a)
      = mass a / weight a := Real.mul_self_sqrt hraPos.le
  have hcard2 : (selectedᶜ.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  -- The scaled row, termwise, is at most a constant pivot pairing.
  have hrow : complementScaledRowOff direction mass weight selectedᶜ scale a
      ≤ ∑ _b ∈ selectedᶜ.erase a, Real.sqrt (mass a / weight a) * (1 / 3) := by
    rw [complementScaledRowOff, sum_ite_eq_sum_erase]
    refine Finset.sum_le_sum fun b hb => ?_
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbmem : b ∈ selectedᶜ := Finset.mem_of_mem_erase hb
    refine le_trans (scaledEntry_le_sqrt_pivot_mul direction mass weight huniv hba
      hraPos (hboost b)) ?_
    have hprod : Real.sqrt (fullPivot direction mass weight a)
        * Real.sqrt (fullPivot direction mass weight b) ≤ 1 / 3 := by
      calc Real.sqrt (fullPivot direction mass weight a)
            * Real.sqrt (fullPivot direction mass weight b)
          ≤ Real.sqrt (1 / 3) * Real.sqrt (1 / 3) :=
            mul_le_mul (hpivotSqrtLe a ha) (hpivotSqrtLe b hbmem)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = 1 / 3 := hsqrtThird
    exact mul_le_mul_of_nonneg_left hprod hsaPos.le
  -- The constant sum is two thirds of the boost square root.
  have hconst : ∑ _b ∈ selectedᶜ.erase a, Real.sqrt (mass a / weight a) * (1 / 3)
      = Real.sqrt (mass a / weight a) * (2 / 3) := by
    rw [Finset.sum_const, hcard2, nsmul_eq_mul]
    push_cast
    ring
  -- The right side is the boost square root against the pivot defect.
  have hrhs : scale a * complementMatrixEntry direction mass weight a a
      = Real.sqrt (mass a / weight a) * (1 - fullPivot direction mass weight a) := by
    rw [complementMatrixEntry_diag direction mass weight a, hscaleDef]
    have hcancel : (Real.sqrt (mass a / weight a))⁻¹ * (mass a / weight a)
        = Real.sqrt (mass a / weight a) := by
      rw [inv_mul_eq_div, Real.div_sqrt]
    calc (Real.sqrt (mass a / weight a))⁻¹
          * ((mass a / weight a) * (1 - fullPivot direction mass weight a))
        = ((Real.sqrt (mass a / weight a))⁻¹ * (mass a / weight a))
          * (1 - fullPivot direction mass weight a) := by ring
      _ = Real.sqrt (mass a / weight a) * (1 - fullPivot direction mass weight a) := by
          rw [hcancel]
  rw [hrhs]
  refine lt_of_le_of_lt (le_trans hrow (le_of_eq hconst)) ?_
  have hgap : (2 : ℝ) / 3 < 1 - fullPivot direction mass weight a := by
    have := hpivot a ha
    linarith
  exact mul_lt_mul_of_pos_left hgap hsaPos

end Gtz
