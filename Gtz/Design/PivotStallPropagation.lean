import Gtz.Design.PivotBalanceLaw
import Gtz.Design.CapSlack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Propagation from a stalled four-set

The pivot balance law detects a label outside every positive-definite stalled
four-set.  Adjoining such a label cannot itself finish the descent: its pivot at
the enlarged five-set is always below one, so it can be erased back immediately.
The useful information is what happens to the four old pivots.

This module proves the exact dichotomy.

* If an old pivot drops below one, erasing that old label produces a genuinely
  exchanged positive-definite four-set.
* If all four old pivots remain at least one, the unique missing label at the
  five-set has pivot strictly larger than `1 + 1 / (2 * weight)`.

The strict half-price is forced by the exact self-pivot update
`p_inserted = p_old / (1 + p_old)`: the inserted label contributes more than
`-1/2` to the centered five-set balance, while every old contribution is
nonnegative.
-/

namespace Gtz

open Matrix

/-! ## Scaled chart atoms and determinant ratios -/

/-- The rank-one vector whose atom is the boosted chart atom. -/
noncomputable def chartLadderVector {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (label : Fin size) : Fin 3 → ℝ :=
  Real.sqrt (mass label / weight label) • direction label

/-- The scaled ladder vector realizes the chart's boosted atom exactly. -/
theorem atomMatrix_chartLadderVector {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (label : Fin size) :
    atomMatrix (chartLadderVector direction mass weight label)
      = (mass label / weight label) • atomMatrix (direction label) := by
  rw [chartLadderVector, atomMatrix_smul,
    Real.sq_sqrt (div_nonneg (hmass label).le (hweight label).le)]

/-- The inverse quadratic form of the scaled vector is the chart pivot. -/
theorem chartLadderVector_inv_quad {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) (label : Fin size) :
    chartLadderVector direction mass weight label ⬝ᵥ
        ((directionChartGap direction mass weight base)⁻¹ *ᵥ
          chartLadderVector direction mass weight label)
      = chartLadderPivot direction mass weight base label := by
  have hroot : Real.sqrt (mass label / weight label)
      * Real.sqrt (mass label / weight label) = mass label / weight label :=
    Real.mul_self_sqrt (div_nonneg (hmass label).le (hweight label).le)
  unfold chartLadderVector chartLadderPivot
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, hroot]

/-- Chart pivots are nonnegative at a positive-definite base. -/
theorem chartLadderPivot_nonneg_of_posDef {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (label : Fin size) :
    0 ≤ chartLadderPivot direction mass weight base label := by
  unfold chartLadderPivot
  exact mul_nonneg (div_pos (hmass label) (hweight label)).le
    (hpd.inv.posSemidef.dotProduct_mulVec_nonneg (direction label))

/-! ## The two-vector rank-one update -/

/-- **THE EXACT CROSS UPDATE.**  Adding the rank-one atom of `source` lowers
the inverse form of `target` by exactly the squared inverse cross term, divided
by `1 +` the source inverse form.  The division-free identity is the useful
form: it retains the equality case and needs no choice of square root.

This is the two-vector Sherman--Morrison law proved by solving one linear
system.  `inverseForm_add_atomMatrix` is its diagonal specialization. -/
theorem inverseForm_add_atomMatrix_cross_update {rank : ℕ}
    {baseMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hposDef : baseMat.PosDef) (source target : Fin rank → ℝ) :
    (1 + source ⬝ᵥ (baseMat⁻¹ *ᵥ source))
        * (target ⬝ᵥ (baseMat⁻¹ *ᵥ target)
          - target ⬝ᵥ ((baseMat + atomMatrix source)⁻¹ *ᵥ target))
      = (target ⬝ᵥ (baseMat⁻¹ *ᵥ source)) ^ 2 := by
  have hunit : IsUnit baseMat.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hbigPosDef : (baseMat + atomMatrix source).PosDef :=
    hposDef.add_posSemidef (posSemidef_atomMatrix source)
  have hbigUnit : IsUnit (baseMat + atomMatrix source).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hbigPosDef.det_pos)
  set sourceDual : Fin rank → ℝ := baseMat⁻¹ *ᵥ source with hsourceDual
  set targetDual : Fin rank → ℝ := baseMat⁻¹ *ᵥ target with htargetDual
  set sourceEnergy : ℝ := source ⬝ᵥ sourceDual with hsourceEnergy
  set cross : ℝ := target ⬝ᵥ sourceDual with hcross
  have hsourceMul : baseMat *ᵥ sourceDual = source := by
    rw [hsourceDual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv baseMat hunit,
      Matrix.one_mulVec]
  have htargetMul : baseMat *ᵥ targetDual = target := by
    rw [htargetDual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv baseMat hunit,
      Matrix.one_mulVec]
  have hcrossComm : source ⬝ᵥ targetDual = cross := by
    have hinvSymm : (baseMat⁻¹)ᵀ = baseMat⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, PosDef.transpose_eq hposDef]
    have hentry : ∀ row col : Fin rank, baseMat⁻¹ col row = baseMat⁻¹ row col := by
      intro row col
      have hcongr := congrFun (congrFun hinvSymm row) col
      simpa using hcongr
    rw [htargetDual, hcross, hsourceDual]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun row _ => Finset.sum_congr rfl fun col _ => ?_
    rw [hentry row col]
    ring
  have hatomSource : atomMatrix source *ᵥ sourceDual = sourceEnergy • source := by
    rw [atomMatrix, vecMulVec_mulVec_eq, hsourceEnergy]
  have hatomTarget : atomMatrix source *ᵥ targetDual = cross • source := by
    rw [atomMatrix, vecMulVec_mulVec_eq, hcrossComm]
  set candidate : Fin rank → ℝ :=
    (1 + sourceEnergy) • targetDual - cross • sourceDual with hcandidate
  have hbaseCandidate : baseMat *ᵥ candidate =
      (1 + sourceEnergy) • target - cross • source := by
    rw [hcandidate, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      htargetMul, hsourceMul]
  have hatomCandidate : atomMatrix source *ᵥ candidate = cross • source := by
    rw [hcandidate, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hatomTarget, hatomSource]
    ext index
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hbigMul : (baseMat + atomMatrix source) *ᵥ candidate =
      (1 + sourceEnergy) • target := by
    rw [Matrix.add_mulVec, hbaseCandidate, hatomCandidate]
    ext index
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsolve : (1 + sourceEnergy) •
      ((baseMat + atomMatrix source)⁻¹ *ᵥ target) = candidate := by
    have hstep : (baseMat + atomMatrix source)⁻¹ *ᵥ
        ((baseMat + atomMatrix source) *ᵥ candidate) = candidate := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hbigUnit,
        Matrix.one_mulVec]
    rw [hbigMul, Matrix.mulVec_smul] at hstep
    exact hstep
  have hpaired := congrArg (fun vector : Fin rank → ℝ => target ⬝ᵥ vector) hsolve
  rw [dotProduct_smul, hcandidate, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hpaired
  have htargetSource : target ⬝ᵥ (baseMat⁻¹ *ᵥ source) = cross := by
    rw [← hsourceDual]
  rw [htargetSource] at hpaired
  nlinarith

/-- The inverse cross term between two scaled chart atoms at one base. -/
noncomputable def chartLadderCross {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (base : Finset (Fin size)) (target source : Fin size) : ℝ :=
  chartLadderVector direction mass weight target ⬝ᵥ
    ((directionChartGap direction mass weight base)⁻¹ *ᵥ
      chartLadderVector direction mass weight source)

/-- **THE EXACT CHART CROSS UPDATE.**  Inserting `added` lowers the pivot of
every `target` by the square of their inverse cross term. -/
theorem chartLadderPivot_insert_cross_update {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (target : Fin size) :
    (1 + chartLadderPivot direction mass weight base added)
        * (chartLadderPivot direction mass weight base target
          - chartLadderPivot direction mass weight (insert added base) target)
      = chartLadderCross direction mass weight base target added ^ 2 := by
  have hstep := inverseForm_add_atomMatrix_cross_update hpd
    (chartLadderVector direction mass weight added)
    (chartLadderVector direction mass weight target)
  have hgap : directionChartGap direction mass weight base
        + atomMatrix (chartLadderVector direction mass weight added)
      = directionChartGap direction mass weight (insert added base) := by
    rw [atomMatrix_chartLadderVector direction mass weight hmass hweight added,
      ← directionChartGap_insert direction mass weight base hadded]
  rw [hgap] at hstep
  rw [chartLadderVector_inv_quad direction mass weight hmass hweight base added,
    chartLadderVector_inv_quad direction mass weight hmass hweight base target,
    chartLadderVector_inv_quad direction mass weight hmass hweight
      (insert added base) target] at hstep
  simpa [chartLadderCross] using hstep

/-- Insertion can only decrease every chart pivot. -/
theorem chartLadderPivot_insert_le {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (target : Fin size) :
    chartLadderPivot direction mass weight (insert added base) target
      ≤ chartLadderPivot direction mass weight base target := by
  have hupdate := chartLadderPivot_insert_cross_update direction mass weight
    hmass hweight base hadded hpd target
  have hsource := chartLadderPivot_nonneg_of_posDef direction mass weight
    hmass hweight base hpd added
  nlinarith [sq_nonneg (chartLadderCross direction mass weight base target added)]

/-- A pivot drops strictly exactly when its inverse cross term with the inserted
label is nonzero. -/
theorem chartLadderPivot_insert_lt_iff_cross_ne_zero {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (target : Fin size) :
    chartLadderPivot direction mass weight (insert added base) target
        < chartLadderPivot direction mass weight base target
      ↔ chartLadderCross direction mass weight base target added ≠ 0 := by
  have hupdate := chartLadderPivot_insert_cross_update direction mass weight
    hmass hweight base hadded hpd target
  have hsource := chartLadderPivot_nonneg_of_posDef direction mass weight
    hmass hweight base hpd added
  constructor
  · intro hlt hzero
    have hsquare : chartLadderCross direction mass weight base target added ^ 2 = 0 := by
      rw [hzero]
      norm_num
    rw [hsquare] at hupdate
    nlinarith [hupdate]
  · intro hne
    have hsquare : 0 < chartLadderCross direction mass weight base target added ^ 2 :=
      sq_pos_of_ne_zero hne
    nlinarith

/-- A pivot is unchanged exactly at inverse-form orthogonality. -/
theorem chartLadderPivot_insert_eq_iff_cross_eq_zero {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (target : Fin size) :
    chartLadderPivot direction mass weight (insert added base) target
        = chartLadderPivot direction mass weight base target
      ↔ chartLadderCross direction mass weight base target added = 0 := by
  constructor
  · intro heq
    by_contra hne
    exact (not_lt_of_ge heq.ge)
      ((chartLadderPivot_insert_lt_iff_cross_ne_zero direction mass weight
        hmass hweight base hadded hpd target).mpr hne)
  · intro hzero
    exact le_antisymm
      (chartLadderPivot_insert_le direction mass weight hmass hweight base
        hadded hpd target)
      (not_lt.mp fun hlt =>
        (chartLadderPivot_insert_lt_iff_cross_ne_zero direction mass weight
          hmass hweight base hadded hpd target).mp hlt hzero)

/-- Inserting one chart label multiplies the gap determinant by `1 + pivot`. -/
theorem det_directionChartGap_insert_eq_det_mul_one_add_pivot {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef) :
    (directionChartGap direction mass weight (insert added base)).det
      = (directionChartGap direction mass weight base).det
          * (1 + chartLadderPivot direction mass weight base added) := by
  have hunit : IsUnit (directionChartGap direction mass weight base).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  rw [directionChartGap_insert direction mass weight base hadded,
    ← atomMatrix_chartLadderVector direction mass weight hmass hweight added,
    det_add_atomMatrix hunit,
    chartLadderVector_inv_quad direction mass weight hmass hweight base added]

/-- Erasing one chart label multiplies the gap determinant by `1 - pivot`. -/
theorem det_directionChartGap_erase_eq_det_mul_one_sub_pivot {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {erased : Fin size} (herased : erased ∈ base)
    (hpd : (directionChartGap direction mass weight base).PosDef) :
    (directionChartGap direction mass weight (base.erase erased)).det
      = (directionChartGap direction mass weight base).det
          * (1 - chartLadderPivot direction mass weight base erased) := by
  have hunit : IsUnit (directionChartGap direction mass weight base).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  rw [directionChartGap_erase direction mass weight base herased,
    ← atomMatrix_chartLadderVector direction mass weight hmass hweight erased,
    det_sub_atomMatrix hunit,
    chartLadderVector_inv_quad direction mass weight hmass hweight base erased]

/-- If erasing one label from a positive-definite base lands exactly on the PSD
boundary, that label's pivot is one.  This is the equality refinement of the
usual implication `not PosDef → pivot ≥ 1`. -/
theorem chartLadderPivot_eq_one_of_erase_posSemidef_not_posDef {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {erased : Fin size} (herased : erased ∈ base)
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (hboundary : (directionChartGap direction mass weight
      (base.erase erased)).PosSemidef)
    (hnotPosDef : ¬ (directionChartGap direction mass weight
      (base.erase erased)).PosDef) :
    chartLadderPivot direction mass weight base erased = 1 := by
  have hdetZero :
      (directionChartGap direction mass weight (base.erase erased)).det = 0 := by
    by_contra hdetNe
    exact hnotPosDef (hboundary.posDef_iff_det_ne_zero.mpr hdetNe)
  have hdetRatio := det_directionChartGap_erase_eq_det_mul_one_sub_pivot
    direction mass weight hmass hweight base herased hpd
  rw [hdetZero] at hdetRatio
  nlinarith [hpd.det_pos]

/-! ## The exact self-pivot update -/

/-- Insertion and erasure are inverse determinant updates. -/
theorem chartLadderPivot_insert_self_product {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef) :
    (1 + chartLadderPivot direction mass weight base added)
        * (1 - chartLadderPivot direction mass weight (insert added base) added)
      = 1 := by
  have hpdInsert :
      (directionChartGap direction mass weight (insert added base)).PosDef :=
    posDef_directionChartGap_of_subset direction mass weight hmass hweight
      (Finset.subset_insert added base) hpd
  have hinsert := det_directionChartGap_insert_eq_det_mul_one_add_pivot
    direction mass weight hmass hweight base hadded hpd
  have herase := det_directionChartGap_erase_eq_det_mul_one_sub_pivot
    direction mass weight hmass hweight (insert added base)
      (Finset.mem_insert_self added base) hpdInsert
  simp only [Finset.erase_insert hadded] at herase
  have hdetNe : (directionChartGap direction mass weight base).det ≠ 0 :=
    ne_of_gt hpd.det_pos
  have hproduct :
      (directionChartGap direction mass weight base).det
          * ((1 + chartLadderPivot direction mass weight base added)
            * (1 - chartLadderPivot direction mass weight
                (insert added base) added))
        = (directionChartGap direction mass weight base).det * 1 := by
    calc
      _ = ((directionChartGap direction mass weight base).det
            * (1 + chartLadderPivot direction mass weight base added))
          * (1 - chartLadderPivot direction mass weight
              (insert added base) added) := by ring
      _ = (directionChartGap direction mass weight (insert added base)).det
          * (1 - chartLadderPivot direction mass weight
              (insert added base) added) := by rw [← hinsert]
      _ = (directionChartGap direction mass weight base).det := herase.symm
      _ = (directionChartGap direction mass weight base).det * 1 := by ring
  exact mul_left_cancel₀ hdetNe hproduct

/-- **THE SELF-PIVOT UPDATE.**  After a label is inserted, its pivot becomes
`p / (1 + p)`, where `p` was its pivot at the old base. -/
theorem chartLadderPivot_insert_self {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef) :
    chartLadderPivot direction mass weight (insert added base) added
      = chartLadderPivot direction mass weight base added
          / (1 + chartLadderPivot direction mass weight base added) := by
  have hnonneg := chartLadderPivot_nonneg_of_posDef direction mass weight
    hmass hweight base hpd added
  have hden : 0 < 1 + chartLadderPivot direction mass weight base added := by
    linarith
  rw [eq_div_iff hden.ne']
  have hproduct := chartLadderPivot_insert_self_product direction mass weight
    hmass hweight base hadded hpd
  nlinarith

/-- An outside pivot at least one becomes an inside pivot in `[1/2, 1)`. -/
theorem chartLadderPivot_insert_self_mem_Ico {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) {added : Fin size} (hadded : added ∉ base)
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (hlarge : 1 ≤ chartLadderPivot direction mass weight base added) :
    1 / 2 ≤ chartLadderPivot direction mass weight (insert added base) added
      ∧ chartLadderPivot direction mass weight (insert added base) added < 1 := by
  have hnonneg := chartLadderPivot_nonneg_of_posDef direction mass weight
    hmass hweight base hpd added
  have hden : 0 < 1 + chartLadderPivot direction mass weight base added := by
    linarith
  rw [chartLadderPivot_insert_self direction mass weight hmass hweight
    base hadded hpd]
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · rw [div_lt_one hden]
    linarith

/-! ## Centering the balance law -/

/-- **THE CENTERED PIVOT BALANCE.**  At size six the constant is `4 - |S|`.
Cardinality four has no constant term; cardinality five contributes `-1`. -/
theorem pivot_centered_balance (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hpd : (directionChartGap direction point.mass point.weight selected).PosDef) :
    ∑ label ∈ selected, (1 - point.weight label)
        * (chartLadderPivot direction point.mass point.weight selected label - 1)
      = (4 : ℝ) - selected.card
        + ∑ label ∈ selectedᶜ, point.weight label
            * (chartLadderPivot direction point.mass point.weight selected label - 1) := by
  have hbalance := pivot_balance direction point selected hpd
  have hsplit : ∑ label ∈ selected, point.weight label
      + ∑ label ∈ selectedᶜ, point.weight label = 1 := by
    rw [Finset.sum_add_sum_compl, point.weight_sum_one]
  have hinsWeight : ∑ label ∈ selected, (1 - point.weight label)
      = selected.card - 1 + ∑ label ∈ selectedᶜ, point.weight label := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [nsmul_eq_mul, mul_one]
    linarith
  have hinCenter :
      ∑ label ∈ selected, (1 - point.weight label)
          * (chartLadderPivot direction point.mass point.weight selected label - 1)
        = (∑ label ∈ selected, (1 - point.weight label)
            * chartLadderPivot direction point.mass point.weight selected label)
          - ∑ label ∈ selected, (1 - point.weight label) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  have houtCenter :
      ∑ label ∈ selectedᶜ, point.weight label
          * (chartLadderPivot direction point.mass point.weight selected label - 1)
        = (∑ label ∈ selectedᶜ, point.weight label
            * chartLadderPivot direction point.mass point.weight selected label)
          - ∑ label ∈ selectedᶜ, point.weight label := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hinCenter, houtCenter, hbalance, hinsWeight]
  ring

/-! ## Four-set propagation -/

-- AUDIT-UNUSED-GENERIC (2026-08-17): this theorem and its successor at :484 take
-- `direction` as an argument, so they hold at EVERY six-label chart.  Measured
-- call sites instantiate `kFourDirection` only (:724).  Neither is ever applied
-- to `Gtz.threeLinesDirection`, although the three-lines lane carries the exact
-- residual they address: `Gtz.threeLines_cardThree_or_cardFour_stall`
-- (Gtz/Design/ThreeLinesDescentPort.lean:372) reduces the whole A2 obligation to
-- ruling out a stalled positive definite card-four selection, and
-- `Gtz.ThreeLinesFundamentalStallEscape`
-- (Gtz/Wave/ThreeLinesStallEscapeWiring.lean:143) is `Iff`-equal to the target.
-- Applying these two laws at `threeLinesDirection slide` costs one line each.
/-- A stalled positive-definite four-set has an outside pivot at least one. -/
theorem card_four_stall_exists_outside_pivot_ge_one
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hcard : selected.card = 4)
    (hpd : (directionChartGap direction point.mass point.weight selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction point.mass point.weight selected label) :
    ∃ added ∉ selected,
      1 ≤ chartLadderPivot direction point.mass point.weight selected added := by
  by_contra hnone
  push Not at hnone
  have hcenter := pivot_centered_balance direction point selected hpd
  rw [hcard] at hcenter
  norm_num at hcenter
  have hinNonneg : 0 ≤ ∑ label ∈ selected, (1 - point.weight label)
      * (chartLadderPivot direction point.mass point.weight selected label - 1) := by
    exact Finset.sum_nonneg fun label hmem =>
      mul_nonneg (by linarith [directionChartPoint_weight_lt_one point label])
        (by linarith [hstall label hmem])
  have hcompCard : selectedᶜ.card = 2 := by
    rw [Finset.card_compl, hcard]
    norm_num
  have hcompNonempty : selectedᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hcompCard
    norm_num at hcompCard
  have houtNeg : ∑ label ∈ selectedᶜ, point.weight label
      * (chartLadderPivot direction point.mass point.weight selected label - 1) < 0 := by
    have hlt : (∑ label ∈ selectedᶜ, point.weight label
        * (chartLadderPivot direction point.mass point.weight selected label - 1))
        < ∑ _label ∈ selectedᶜ, (0 : ℝ) := by
      refine Finset.sum_lt_sum_of_nonempty hcompNonempty fun label hmem => ?_
      have hpivot := hnone label (Finset.mem_compl.mp hmem)
      have hweight := point.weight_pos label
      nlinarith
    simpa using hlt
  linarith

/-- **THE FOUR-SET PROPAGATION DICHOTOMY.**  A positive-definite stalled
four-set admits an outside insertion whose self-pivot lies in `[1/2,1)`.  Either
an old label becomes erasable, producing an exchanged positive-definite
four-set, or all four old labels stay stalled and every (necessarily unique)
missing label at the five-set has pivot strictly above `1 + 1/(2w)`. -/
theorem card_four_stall_exchange_or_priced_endpoint
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hcard : selected.card = 4)
    (hpd : (directionChartGap direction point.mass point.weight selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction point.mass point.weight selected label) :
    ∃ added : Fin 6, added ∉ selected ∧
      (directionChartGap direction point.mass point.weight
        (insert added selected)).PosDef ∧
      1 / 2 ≤ chartLadderPivot direction point.mass point.weight
        (insert added selected) added ∧
      chartLadderPivot direction point.mass point.weight
        (insert added selected) added < 1 ∧
      ((∃ dropped ∈ selected,
          chartLadderPivot direction point.mass point.weight
              (insert added selected) dropped < 1 ∧
          (directionChartGap direction point.mass point.weight
            ((insert added selected).erase dropped)).PosDef)
        ∨ ((∀ dropped ∈ selected,
              1 ≤ chartLadderPivot direction point.mass point.weight
                (insert added selected) dropped) ∧
            ∀ missing ∉ insert added selected,
              1 + 1 / (2 * point.weight missing)
                < chartLadderPivot direction point.mass point.weight
                    (insert added selected) missing)) := by
  obtain ⟨added, hadded, hlarge⟩ :=
    card_four_stall_exists_outside_pivot_ge_one direction point hcard hpd hstall
  have hpdInsert : (directionChartGap direction point.mass point.weight
      (insert added selected)).PosDef :=
    posDef_directionChartGap_of_subset direction point.mass point.weight
      point.mass_pos point.weight_pos (Finset.subset_insert added selected) hpd
  obtain ⟨hselfHalf, hselfLt⟩ :=
    chartLadderPivot_insert_self_mem_Ico direction point.mass point.weight
      point.mass_pos point.weight_pos selected hadded hpd hlarge
  refine ⟨added, hadded, hpdInsert, hselfHalf, hselfLt, ?_⟩
  by_cases hexchange : ∃ dropped ∈ selected,
      chartLadderPivot direction point.mass point.weight
        (insert added selected) dropped < 1
  · left
    obtain ⟨dropped, hdropped, hpivot⟩ := hexchange
    exact ⟨dropped, hdropped, hpivot,
      (posDef_directionChartGap_erase_iff direction point.mass point.weight
        point.mass_pos point.weight_pos (insert added selected)
        (Finset.mem_insert_of_mem hdropped) hpdInsert).mpr hpivot⟩
  · right
    push Not at hexchange
    have hremain : ∀ dropped ∈ selected,
        1 ≤ chartLadderPivot direction point.mass point.weight
          (insert added selected) dropped := by
      intro dropped hdropped
      exact hexchange dropped hdropped
    refine ⟨hremain, ?_⟩
    intro missing hmissing
    have hcardInsert : (insert added selected).card = 5 := by
      rw [Finset.card_insert_of_notMem hadded, hcard]
    have hcompCard : (insert added selected)ᶜ.card = 1 := by
      rw [Finset.card_compl, hcardInsert]
      norm_num
    obtain ⟨only, honly⟩ := Finset.card_eq_one.mp hcompCard
    have hmissingMem : missing ∈ (insert added selected)ᶜ :=
      Finset.mem_compl.mpr hmissing
    rw [honly] at hmissingMem
    have hmissingEq : missing = only := by simpa using hmissingMem
    subst only
    have hcenter := pivot_centered_balance direction point
      (insert added selected) hpdInsert
    rw [hcardInsert, honly, Finset.sum_singleton] at hcenter
    norm_num at hcenter
    have holdNonneg : 0 ≤ ∑ label ∈ selected,
        (1 - point.weight label)
          * (chartLadderPivot direction point.mass point.weight
              (insert added selected) label - 1) := by
      exact Finset.sum_nonneg fun label hlabel =>
        mul_nonneg (by linarith [directionChartPoint_weight_lt_one point label])
          (by linarith [hremain label hlabel])
    have haddTerm : -1 / 2 < (1 - point.weight added)
        * (chartLadderPivot direction point.mass point.weight
            (insert added selected) added - 1) := by
      have hfactor : 0 ≤ (1 - point.weight added)
          * (chartLadderPivot direction point.mass point.weight
              (insert added selected) added - 1 / 2) :=
        mul_nonneg (by linarith [directionChartPoint_weight_lt_one point added])
          (by linarith [hselfHalf])
      nlinarith [hfactor, point.weight_pos added]
    have hinLower : -1 / 2 < ∑ label ∈ insert added selected,
        (1 - point.weight label)
          * (chartLadderPivot direction point.mass point.weight
              (insert added selected) label - 1) := by
      rw [Finset.sum_insert hadded]
      linarith
    have hpricedMul : 1 / 2 < point.weight missing
        * (chartLadderPivot direction point.mass point.weight
            (insert added selected) missing - 1) := by
      linarith
    have hweight := point.weight_pos missing
    have hrewrite : 1 + 1 / (2 * point.weight missing)
        = (point.weight missing + 1 / 2) / point.weight missing := by
      field_simp
    rw [hrewrite, div_lt_iff₀ hweight]
    nlinarith

/-! ## The K4 pivot wall -/

/-- The four-pivot K4 wall inherits the generic exchange-or-priced-endpoint
dichotomy at its pointer window. -/
theorem kFourPivotWall_exchange_or_priced_endpoint
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (hwall : KFourTreeWindowAllPivotWallData point tree) :
    ∃ pointer : Fin 6, pointer ∉ tree ∧
      chartLadderPivot kFourDirection point.mass point.weight
          (insert pointer tree) pointer = 1 ∧
      ∃ added : Fin 6, added ∉ insert pointer tree ∧
        (directionChartGap kFourDirection point.mass point.weight
          (insert added (insert pointer tree))).PosDef ∧
        1 / 2 ≤ chartLadderPivot kFourDirection point.mass point.weight
          (insert added (insert pointer tree)) added ∧
        chartLadderPivot kFourDirection point.mass point.weight
          (insert added (insert pointer tree)) added < 1 ∧
        ((∃ dropped ∈ insert pointer tree,
            chartLadderPivot kFourDirection point.mass point.weight
                (insert added (insert pointer tree)) dropped < 1 ∧
            (directionChartGap kFourDirection point.mass point.weight
              ((insert added (insert pointer tree)).erase dropped)).PosDef)
          ∨ ((∀ dropped ∈ insert pointer tree,
                1 ≤ chartLadderPivot kFourDirection point.mass point.weight
                  (insert added (insert pointer tree)) dropped) ∧
              ∀ missing ∉ insert added (insert pointer tree),
                1 + 1 / (2 * point.weight missing)
                  < chartLadderPivot kFourDirection point.mass point.weight
                      (insert added (insert pointer tree)) missing)) := by
  obtain ⟨pointer, hpointer, hpd, hstall⟩ := hwall
  have hcard : (insert pointer tree).card = 4 := by
    rw [Finset.card_insert_of_notMem hpointer, kFourSpanningTree_card tree htree]
  have herase : (insert pointer tree).erase pointer = tree :=
    Finset.erase_insert hpointer
  have hboundary : (directionChartGap kFourDirection point.mass point.weight
      ((insert pointer tree).erase pointer)).PosSemidef := by
    rw [herase]
    exact hgap
  have hnotPosDef : ¬ (directionChartGap kFourDirection point.mass point.weight
      ((insert pointer tree).erase pointer)).PosDef := by
    rw [herase]
    exact not_posDef_of_kFourTreeWindowData point hwindow
  have hpointerEq := chartLadderPivot_eq_one_of_erase_posSemidef_not_posDef
    kFourDirection point.mass point.weight point.mass_pos point.weight_pos
      (insert pointer tree) (Finset.mem_insert_self pointer tree) hpd
      hboundary hnotPosDef
  obtain ⟨added, hadded, hpdInsert, hhalf, hlt, hcases⟩ :=
    card_four_stall_exchange_or_priced_endpoint kFourDirection point
      hcard hpd hstall
  exact ⟨pointer, hpointer, hpointerEq, added, hadded, hpdInsert, hhalf, hlt,
    hcases⟩

/-! ## The boundary pointer under the first insertion -/

/-- The exact first-insertion data at a K4 pivot wall.  The original boundary
pointer starts at pivot one.  Its pivot can only decrease after the outside
label is inserted, and it decreases strictly exactly when the inverse cross
term is nonzero.  In that case erasing the pointer gives the explicit exchanged
four-set `insert added tree` with positive-definite gap.

Thus a boundary pointer survives the insertion only through one exact equation:
inverse-form orthogonality to the added chart atom. -/
structure KFourPivotWallPointerCrossData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) where
  pointer : Fin 6
  pointer_notMem : pointer ∉ tree
  window_posDef :
    (directionChartGap kFourDirection point.mass point.weight
      (insert pointer tree)).PosDef
  pointer_pivot_eq_one :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert pointer tree) pointer = 1
  added : Fin 6
  added_notMem : added ∉ insert pointer tree
  added_pivot_ge_one_before :
    1 ≤ chartLadderPivot kFourDirection point.mass point.weight
      (insert pointer tree) added
  five_posDef :
    (directionChartGap kFourDirection point.mass point.weight
      (insert added (insert pointer tree))).PosDef
  added_pivot_ge_half_after :
    1 / 2 ≤ chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) added
  added_pivot_lt_one_after :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) added < 1
  pointer_pivot_le_one_after :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) pointer ≤ 1
  pointer_pivot_lt_one_iff_cross_ne_zero :
    chartLadderPivot kFourDirection point.mass point.weight
        (insert added (insert pointer tree)) pointer < 1
      ↔ chartLadderCross kFourDirection point.mass point.weight
          (insert pointer tree) pointer added ≠ 0
  pointer_pivot_eq_one_iff_cross_eq_zero :
    chartLadderPivot kFourDirection point.mass point.weight
        (insert added (insert pointer tree)) pointer = 1
      ↔ chartLadderCross kFourDirection point.mass point.weight
          (insert pointer tree) pointer added = 0
  direct_exchange_posDef :
    chartLadderCross kFourDirection point.mass point.weight
        (insert pointer tree) pointer added ≠ 0 →
      (directionChartGap kFourDirection point.mass point.weight
        (insert added tree)).PosDef

/-- **THE POINTER-CROSS PROPAGATION LAW.**  Every K4 pivot wall carries the
exact data above.  This strengthens the broad exchange arm by naming the first
possible deletion: unless one inverse cross term vanishes exactly, the original
boundary pointer itself is erasable. -/
theorem kFourPivotWall_pointerCrossData
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (hwall : KFourTreeWindowAllPivotWallData point tree) :
    Nonempty (KFourPivotWallPointerCrossData point tree) := by
  obtain ⟨pointer, hpointer, hpdWindow, hstall⟩ := hwall
  have hcard : (insert pointer tree).card = 4 := by
    rw [Finset.card_insert_of_notMem hpointer, kFourSpanningTree_card tree htree]
  have herase : (insert pointer tree).erase pointer = tree :=
    Finset.erase_insert hpointer
  have hboundary : (directionChartGap kFourDirection point.mass point.weight
      ((insert pointer tree).erase pointer)).PosSemidef := by
    rw [herase]
    exact hgap
  have hnotPosDef : ¬ (directionChartGap kFourDirection point.mass point.weight
      ((insert pointer tree).erase pointer)).PosDef := by
    rw [herase]
    exact not_posDef_of_kFourTreeWindowData point hwindow
  have hpointerEq := chartLadderPivot_eq_one_of_erase_posSemidef_not_posDef
    kFourDirection point.mass point.weight point.mass_pos point.weight_pos
      (insert pointer tree) (Finset.mem_insert_self pointer tree) hpdWindow
      hboundary hnotPosDef
  obtain ⟨added, hadded, hlarge⟩ :=
    card_four_stall_exists_outside_pivot_ge_one kFourDirection point hcard
      hpdWindow hstall
  have hpdFive : (directionChartGap kFourDirection point.mass point.weight
      (insert added (insert pointer tree))).PosDef :=
    posDef_directionChartGap_of_subset kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos (Finset.subset_insert added _) hpdWindow
  obtain ⟨hhalf, hselfLt⟩ :=
    chartLadderPivot_insert_self_mem_Ico kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos (insert pointer tree) hadded hpdWindow hlarge
  have hpointerLeRaw := chartLadderPivot_insert_le kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos (insert pointer tree) hadded
      hpdWindow pointer
  have hpointerLe : chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) pointer ≤ 1 := by
    rw [← hpointerEq]
    exact hpointerLeRaw
  have hpointerLtIff := chartLadderPivot_insert_lt_iff_cross_ne_zero
    kFourDirection point.mass point.weight point.mass_pos point.weight_pos
      (insert pointer tree) hadded hpdWindow pointer
  rw [hpointerEq] at hpointerLtIff
  have hpointerEqIff := chartLadderPivot_insert_eq_iff_cross_eq_zero
    kFourDirection point.mass point.weight point.mass_pos point.weight_pos
      (insert pointer tree) hadded hpdWindow pointer
  rw [hpointerEq] at hpointerEqIff
  have haddNePointer : added ≠ pointer := by
    intro heq
    subst added
    exact hadded (Finset.mem_insert_self pointer tree)
  have hset : (insert added (insert pointer tree)).erase pointer =
      insert added tree := by
    ext label
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hne, rfl | rfl | hmem⟩
      · exact Or.inl rfl
      · exact absurd rfl hne
      · exact Or.inr hmem
    · rintro (rfl | hmem)
      · exact ⟨haddNePointer, Or.inl rfl⟩
      · exact ⟨fun heq => hpointer (heq ▸ hmem), Or.inr (Or.inr hmem)⟩
  refine ⟨⟨pointer, hpointer, hpdWindow, hpointerEq, added, hadded, hlarge,
    hpdFive, hhalf, hselfLt, hpointerLe, hpointerLtIff, hpointerEqIff, ?_⟩⟩
  intro hcrossNe
  have hpointerLt := hpointerLtIff.mpr hcrossNe
  have hpdErase : (directionChartGap kFourDirection point.mass point.weight
      ((insert added (insert pointer tree)).erase pointer)).PosDef :=
    (posDef_directionChartGap_erase_iff kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos (insert added (insert pointer tree))
      (Finset.mem_insert_of_mem (Finset.mem_insert_self pointer tree))
      hpdFive).mpr hpointerLt
  rw [hset] at hpdErase
  exact hpdErase

/-! ## Package and spend the two propagation arms -/

/-- The concrete exchange arm produced from a K4 pivot wall.  The exchanged
four-set is retained explicitly: later arguments can either delete once more
to a spanning tree or analyze the genuinely recurrent stall. -/
structure KFourPivotWallExchangeData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) where
  pointer : Fin 6
  pointer_notMem : pointer ∉ tree
  pointer_pivot_eq_one :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert pointer tree) pointer = 1
  added : Fin 6
  added_notMem : added ∉ insert pointer tree
  five_posDef :
    (directionChartGap kFourDirection point.mass point.weight
      (insert added (insert pointer tree))).PosDef
  added_pivot_ge_half :
    1 / 2 ≤ chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) added
  added_pivot_lt_one :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) added < 1
  dropped : Fin 6
  dropped_mem : dropped ∈ insert pointer tree
  dropped_pivot_lt_one :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) dropped < 1
  exchange_posDef :
    (directionChartGap kFourDirection point.mass point.weight
      ((insert added (insert pointer tree)).erase dropped)).PosDef
  exchange_card : ((insert added (insert pointer tree)).erase dropped).card = 4

/-- The alternative five-set endpoint.  All four old labels remain stalled,
while the unique missing label is priced strictly above
`1 + 1 / (2 * weight)`. -/
structure KFourPivotWallPricedEndpointData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) where
  pointer : Fin 6
  pointer_notMem : pointer ∉ tree
  pointer_pivot_eq_one :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert pointer tree) pointer = 1
  added : Fin 6
  added_notMem : added ∉ insert pointer tree
  five_posDef :
    (directionChartGap kFourDirection point.mass point.weight
      (insert added (insert pointer tree))).PosDef
  added_pivot_ge_half :
    1 / 2 ≤ chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) added
  added_pivot_lt_one :
    chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) added < 1
  old_pivots_ge_one : ∀ dropped ∈ insert pointer tree,
    1 ≤ chartLadderPivot kFourDirection point.mass point.weight
      (insert added (insert pointer tree)) dropped
  missing_price : ∀ missing ∉ insert added (insert pointer tree),
    1 + 1 / (2 * point.weight missing)
      < chartLadderPivot kFourDirection point.mass point.weight
          (insert added (insert pointer tree)) missing

/-- Package the raw nested existential from the propagation theorem into the
two exact K4 wall arms. -/
theorem kFourPivotWall_exchangeData_or_pricedEndpointData
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (hwall : KFourTreeWindowAllPivotWallData point tree) :
    Nonempty (KFourPivotWallExchangeData point tree) ∨
      Nonempty (KFourPivotWallPricedEndpointData point tree) := by
  obtain ⟨pointer, hpointer, hpointerEq, added, hadded, hpdFive, hhalf, hlt,
    hexchange | hendpoint⟩ :=
    kFourPivotWall_exchange_or_priced_endpoint point htree hgap hwindow hwall
  · obtain ⟨dropped, hdropped, hdropLt, hpdExchange⟩ := hexchange
    left
    refine ⟨⟨pointer, hpointer, hpointerEq, added, hadded, hpdFive, hhalf, hlt,
      dropped, hdropped, hdropLt, hpdExchange, ?_⟩⟩
    have hwindowCard : (insert pointer tree).card = 4 := by
      rw [Finset.card_insert_of_notMem hpointer, kFourSpanningTree_card tree htree]
    have hfiveCard : (insert added (insert pointer tree)).card = 5 := by
      rw [Finset.card_insert_of_notMem hadded, hwindowCard]
    rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem hdropped), hfiveCard]
  · right
    exact ⟨⟨pointer, hpointer, hpointerEq, added, hadded, hpdFive, hhalf, hlt,
      hendpoint.1, hendpoint.2⟩⟩

/-- A positive-definite four-set either deletes once more to a strict K4
spanning tree or is a genuine four-pivot stall. -/
theorem exists_strictTree_or_cardFour_stall_of_posDef
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hcard : selected.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef) ∨
      ∀ label ∈ selected,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          selected label := by
  by_cases hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected label
  · exact Or.inr hstall
  · left
    push Not at hstall
    obtain ⟨dropped, hdropped, hdropLt⟩ := hstall
    have hpdTree : (directionChartGap kFourDirection point.mass point.weight
        (selected.erase dropped)).PosDef :=
      (posDef_directionChartGap_erase_iff kFourDirection point.mass point.weight
        point.mass_pos point.weight_pos selected hdropped hpd).mpr hdropLt
    have hcardTree : (selected.erase dropped).card = 3 := by
      rw [Finset.card_erase_of_mem hdropped, hcard]
    refine ⟨selected.erase dropped,
      mem_kFourSpanningTreeList_of_card_three _ hcardTree ?_, hpdTree⟩
    intro htriangle
    exact kFourTriangle_gap_not_posDef point _ htriangle hpdTree

/-- The only exchange branch not already closed by one further deletion: an
exchanged positive-definite four-set whose four deletion pivots all remain at
least one. -/
def KFourPivotWallRecurrentStallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ data : KFourPivotWallExchangeData point tree,
    ∀ label ∈
        (insert data.added (insert data.pointer tree)).erase data.dropped,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        ((insert data.added (insert data.pointer tree)).erase data.dropped)
          label

/-- **THE PIVOT-WALL PROPAGATION CAPSTONE.**  Every actual pivot wall either
already yields a strict spanning tree, reaches a recurrent stalled four-set,
or reaches the strict half-priced five-set endpoint.  Thus the broad pivot-wall
atlas target has been reduced to two exact residual arms. -/
theorem kFourPivotWall_strictTree_or_recurrentStall_or_pricedEndpoint
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hwindow : KFourTreeWindowData point tree)
    (hwall : KFourTreeWindowAllPivotWallData point tree) :
    (∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef) ∨
      KFourPivotWallRecurrentStallData point tree ∨
        Nonempty (KFourPivotWallPricedEndpointData point tree) := by
  rcases kFourPivotWall_exchangeData_or_pricedEndpointData point htree hgap
      hwindow hwall with hexchangeData | hendpoint
  · obtain ⟨hexchange⟩ := hexchangeData
    rcases exists_strictTree_or_cardFour_stall_of_posDef point
      hexchange.exchange_card hexchange.exchange_posDef with hstrict | hstall
    · exact Or.inl hstrict
    · exact Or.inr (Or.inl ⟨hexchange, hstall⟩)
  · exact Or.inr (Or.inr hendpoint)

end Gtz
