import Gtz.Wave.FourRowCoefficientProjection
import Gtz.Wave.FourActivePositiveMultipliers
import Gtz.Wave.FourActiveRankSplit
import Gtz.Wave.ActiveBlockKernelPromotion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

def orbitFourLabel : Fin 4 → Finset (Fin 6) :=
  ![orbitFourBlockZeroOneTwo, orbitFourBlockZeroOneThree,
    orbitFourBlockZeroTwoThree, orbitFourBlockOneFourFive]

theorem orbitFourLabel_range :
    Finset.univ.image orbitFourLabel = orbitFourFamily := by
  decide

theorem orbitFourLabel_injective : Function.Injective orbitFourLabel := by
  decide

/-- Columns are the multiplier-weighted ambient tight directions. -/
noncomputable def orbitFourWeightedTightColumns
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ) :
    Matrix (Fin 6) (Fin 4) ℝ :=
  fun atomIndex label =>
    Real.sqrt (multiplier (orbitFourLabel label))
      * tightDir (orbitFourLabel label) atomIndex

/-- The stationary assembly on the canonical four-block family is the Gram
matrix of its four multiplier-weighted tight columns. -/
theorem orbitFourWeightedTightColumns_mul_transpose
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ)
    (hnonneg : ∀ selected ∈ orbitFourFamily, 0 ≤ multiplier selected) :
    orbitFourWeightedTightColumns multiplier tightDir
        * (orbitFourWeightedTightColumns multiplier tightDir).transpose
      = chartMultiplierAssembly orbitFourFamily multiplier tightDir := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, chartMultiplierAssembly_apply, Fin.sum_univ_four]
  have hzero := Real.sq_sqrt
    (hnonneg orbitFourBlockZeroOneTwo (by simp [orbitFourFamily]))
  have hone := Real.sq_sqrt
    (hnonneg orbitFourBlockZeroOneThree (by simp [orbitFourFamily]))
  have htwo := Real.sq_sqrt
    (hnonneg orbitFourBlockZeroTwoThree (by simp [orbitFourFamily]))
  have hthree := Real.sq_sqrt
    (hnonneg orbitFourBlockOneFourFive (by simp [orbitFourFamily]))
  simp only [orbitFourWeightedTightColumns, orbitFourLabel,
    Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [show Real.sqrt (multiplier orbitFourBlockZeroOneTwo)
          * tightDir orbitFourBlockZeroOneTwo rowIndex
          * (Real.sqrt (multiplier orbitFourBlockZeroOneTwo)
            * tightDir orbitFourBlockZeroOneTwo colIndex)
        = multiplier orbitFourBlockZeroOneTwo
          * (tightDir orbitFourBlockZeroOneTwo rowIndex
            * tightDir orbitFourBlockZeroOneTwo colIndex) by
      calc
        _ = (Real.sqrt (multiplier orbitFourBlockZeroOneTwo)) ^ 2
              * (tightDir orbitFourBlockZeroOneTwo rowIndex
                * tightDir orbitFourBlockZeroOneTwo colIndex) := by ring
        _ = _ := by rw [hzero],
    show Real.sqrt (multiplier orbitFourBlockZeroOneThree)
          * tightDir orbitFourBlockZeroOneThree rowIndex
          * (Real.sqrt (multiplier orbitFourBlockZeroOneThree)
            * tightDir orbitFourBlockZeroOneThree colIndex)
        = multiplier orbitFourBlockZeroOneThree
          * (tightDir orbitFourBlockZeroOneThree rowIndex
            * tightDir orbitFourBlockZeroOneThree colIndex) by
      calc
        _ = (Real.sqrt (multiplier orbitFourBlockZeroOneThree)) ^ 2
              * (tightDir orbitFourBlockZeroOneThree rowIndex
                * tightDir orbitFourBlockZeroOneThree colIndex) := by ring
        _ = _ := by rw [hone],
    show Real.sqrt (multiplier orbitFourBlockZeroTwoThree)
          * tightDir orbitFourBlockZeroTwoThree rowIndex
          * (Real.sqrt (multiplier orbitFourBlockZeroTwoThree)
            * tightDir orbitFourBlockZeroTwoThree colIndex)
        = multiplier orbitFourBlockZeroTwoThree
          * (tightDir orbitFourBlockZeroTwoThree rowIndex
            * tightDir orbitFourBlockZeroTwoThree colIndex) by
      calc
        _ = (Real.sqrt (multiplier orbitFourBlockZeroTwoThree)) ^ 2
              * (tightDir orbitFourBlockZeroTwoThree rowIndex
                * tightDir orbitFourBlockZeroTwoThree colIndex) := by ring
        _ = _ := by rw [htwo],
    show Real.sqrt (multiplier orbitFourBlockOneFourFive)
          * tightDir orbitFourBlockOneFourFive rowIndex
          * (Real.sqrt (multiplier orbitFourBlockOneFourFive)
            * tightDir orbitFourBlockOneFourFive colIndex)
        = multiplier orbitFourBlockOneFourFive
          * (tightDir orbitFourBlockOneFourFive rowIndex
            * tightDir orbitFourBlockOneFourFive colIndex) by
      calc
        _ = (Real.sqrt (multiplier orbitFourBlockOneFourFive)) ^ 2
              * (tightDir orbitFourBlockOneFourFive rowIndex
                * tightDir orbitFourBlockOneFourFive colIndex) := by ring
        _ = _ := by rw [hthree]]
  have hzeroNot : orbitFourBlockZeroOneTwo ∉
      ({orbitFourBlockZeroOneThree, orbitFourBlockZeroTwoThree,
        orbitFourBlockOneFourFive} : Finset (Finset (Fin 6))) := by decide
  have honeNot : orbitFourBlockZeroOneThree ∉
      ({orbitFourBlockZeroTwoThree, orbitFourBlockOneFourFive} :
        Finset (Finset (Fin 6))) := by decide
  have htwoNot : orbitFourBlockZeroTwoThree ∉
      ({orbitFourBlockOneFourFive} : Finset (Finset (Fin 6))) := by decide
  rw [orbitFourFamily, Finset.sum_insert hzeroNot,
    Finset.sum_insert honeNot, Finset.sum_insert htwoNot, Finset.sum_singleton]
  ring

/-- Positive multiplier rescaling does not change the span of the four tight
directions. -/
theorem orbitFourWeightedTightColumns_span_eq
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ)
    (hpositive : ∀ selected ∈ orbitFourFamily, 0 < multiplier selected) :
    Submodule.span ℝ
        (Set.range (orbitFourWeightedTightColumns multiplier tightDir).col)
      = Submodule.span ℝ
        (↑(orbitFourFamily.image tightDir) : Set (Fin 6 → ℝ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro vector hvector
    rcases hvector with ⟨label, rfl⟩
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Finset.mem_coe, Finset.mem_image]
    refine ⟨orbitFourLabel label, ?_, rfl⟩
    rw [← orbitFourLabel_range]
    exact Finset.mem_image.mpr ⟨label, Finset.mem_univ _, rfl⟩
  · rw [Submodule.span_le]
    intro vector hvector
    simp only [Finset.mem_coe, Finset.mem_image] at hvector
    rcases hvector with ⟨selected, hselected, rfl⟩
    have hselectedRange : selected ∈ Finset.univ.image orbitFourLabel := by
      rw [orbitFourLabel_range]
      exact hselected
    rcases Finset.mem_image.mp hselectedRange with ⟨label, _, hlabel⟩
    have hroot : Real.sqrt (multiplier selected) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hpositive selected hselected))
    have hrecover :
        tightDir selected =
          (Real.sqrt (multiplier selected))⁻¹ •
            (orbitFourWeightedTightColumns multiplier tightDir).col label := by
      funext atomIndex
      simp [orbitFourWeightedTightColumns, hlabel, hroot]
    rw [hrecover]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨label, rfl⟩

/-- Four-dimensional tight-row span is exactly full column rank for the
weighted Gram factor. -/
theorem orbitFourWeightedTightColumns_finrank_range
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ)
    (hpositive : ∀ selected ∈ orbitFourFamily, 0 < multiplier selected)
    (hspan : Module.finrank ℝ
      (Submodule.span ℝ
        (↑(orbitFourFamily.image tightDir) : Set (Fin 6 → ℝ))) = 4) :
    Module.finrank ℝ (LinearMap.range
      (Matrix.toLin' (orbitFourWeightedTightColumns multiplier tightDir))) = 4 := by
  rw [Matrix.range_toLin', orbitFourWeightedTightColumns_span_eq
    multiplier tightDir hpositive, hspan]

/-- Local tightness survives multiplier square-root rescaling of a column. -/
theorem projection_mul_orbitFourWeightedColumn_apply
    {projection : Matrix (Fin 6) (Fin 6) ℝ}
    {weight : Fin 6 → ℝ} {value : ℝ}
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value
      orbitFourFamily (id : Finset (Fin 6) → Finset (Fin 6))
      multiplier tightDir)
    (label : Fin 4) (atomIndex : Fin 6)
    (hmem : atomIndex ∈ orbitFourLabel label) :
    (projection * orbitFourWeightedTightColumns multiplier tightDir)
        atomIndex label
      = (value + weight atomIndex)
          * orbitFourWeightedTightColumns multiplier tightDir atomIndex label := by
  have hactive : orbitFourLabel label ∈ orbitFourFamily := by
    rw [← orbitFourLabel_range]
    exact Finset.mem_image.mpr ⟨label, Finset.mem_univ _, rfl⟩
  have htight := projection_mulVec_tightDir_of_mem hdata hactive hmem
  change (projection *ᵥ
      (orbitFourWeightedTightColumns multiplier tightDir).col label) atomIndex
    = _
  change (projection *ᵥ
      (Real.sqrt (multiplier (orbitFourLabel label)) •
        tightDir (orbitFourLabel label))) atomIndex = _
  rw [Matrix.mulVec_smul, Pi.smul_apply, htight]
  simp only [orbitFourWeightedTightColumns, smul_eq_mul]
  ring

/-- **THE ORBIT-FOUR COEFFICIENT PROJECTION.**  Any stationary datum on the
canonical four-block family produces a symmetric idempotent rank-two operator
on the four multiplier-weighted tight directions.  This is the common source
of the aligned and reflected trace contradictions. -/
theorem SixThreeCrux.exists_orbitFour_coefficientProjection
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = orbitFourFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir) :
    let B := orbitFourWeightedTightColumns multiplier tightDir
    let P := (chartPointOfDesign crux.design).chart
    ∃ (L : Matrix (Fin 4) (Fin 6) ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ),
      L * B = 1 ∧ P * B = B * M ∧ M.transpose = M
        ∧ M * M = M ∧ Matrix.trace M = 2 := by
  classical
  let B := orbitFourWeightedTightColumns multiplier tightDir
  let P := (chartPointOfDesign crux.design).chart
  have hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]
    decide
  have hpositive : ∀ selected ∈
      chartArgmaxFamily (chartPointOfDesign crux.design),
      0 < multiplier selected :=
    crux.activeWeight_pos_of_identity_family_card_four hdata hfamilyCard
  have hpositiveOrbit : ∀ selected ∈ orbitFourFamily,
      0 < multiplier selected := by
    intro selected hselected
    apply hpositive selected
    rw [hfamily]
    exact hselected
  obtain ⟨hspan, hcaptured, _⟩ :=
    crux.fourRowSpan_and_capturedRanks hdata hfamilyCard hpositive
  rw [hfamily] at hspan hcaptured
  have hspanOrbit : Module.finrank ℝ
      (Submodule.span ℝ
        (↑(orbitFourFamily.image tightDir) : Set (Fin 6 → ℝ))) = 4 := by
    exact hspan
  have hBRange : Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' B)) = 4 := by
    simpa only [B] using orbitFourWeightedTightColumns_finrank_range
      multiplier tightDir hpositiveOrbit hspanOrbit
  obtain ⟨L, hleft⟩ :=
    exists_matrix_leftInverse_of_finrank_range_eq_four B hBRange
  have hgram : B * B.transpose =
      chartMultiplierAssembly orbitFourFamily multiplier tightDir := by
    simpa only [B] using orbitFourWeightedTightColumns_mul_transpose
      multiplier tightDir (fun selected hselected =>
        le_of_lt (hpositiveOrbit selected hselected))
  have hcommutes : P * (B * B.transpose) = (B * B.transpose) * P := by
    rw [hgram]
    simpa only [P, hfamily] using hdata.assembly_commutes
  have hcapturedGram : Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (P * (B * B.transpose)))) = 2 := by
    rw [hgram]
    simpa only [P] using hcaptured
  have hrank : (P * (B * B.transpose)).rank = 2 := by
    change Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (P * (B * B.transpose)))) = 2
    exact hcapturedGram
  obtain ⟨M, hrepresentation, hsymm, hidem, htrace⟩ :=
    exists_coefficient_projection_trace_eq_two_of_commutingGram
      P B L hleft (by simpa only [P] using hdata.isSymmetric)
      (by simpa only [P] using hdata.isIdempotent) hcommutes hrank
  exact ⟨L, M, hleft, hrepresentation, hsymm, hidem, htrace⟩

/-- **REFLECTED TYPE-NINE LEAF CLOSED.**  In the canonical support pattern,
the two middle weighted tight rows are the only rows visible at atoms `0` and
`3`, while the last row is private at atom `4`.  If the endpoint restriction
is nonsingular, local tightness fixes three diagonal trace contributions.  The
rank-two coefficient trace then contradicts the negative-chart shifted-weight
budget. -/
theorem SixThreeCrux.false_of_orbitFour_reflectedRows
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = orbitFourFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    {a r c f k : ℝ}
    (hrowZero :
      (orbitFourWeightedTightColumns multiplier tightDir) 0
        = (![0, a, r, 0] : Fin 4 → ℝ))
    (hrowThree :
      (orbitFourWeightedTightColumns multiplier tightDir) 3
        = (![0, c, f, 0] : Fin 4 → ℝ))
    (hrowFour :
      (orbitFourWeightedTightColumns multiplier tightDir) 4
        = (![0, 0, 0, k] : Fin 4 → ℝ))
    (hendpoint : a * f - r * c ≠ 0)
    (hk : k ≠ 0) : False := by
  classical
  let point := chartPointOfDesign crux.design
  let P := point.chart
  let B := orbitFourWeightedTightColumns multiplier tightDir
  let value := chartObjective point
  change B 0 = (![0, a, r, 0] : Fin 4 → ℝ) at hrowZero
  change B 3 = (![0, c, f, 0] : Fin 4 → ℝ) at hrowThree
  change B 4 = (![0, 0, 0, k] : Fin 4 → ℝ) at hrowFour
  have hdataOrbit : IsChartStationaryData 3 P point.weight value
      orbitFourFamily (id : Finset (Fin 6) → Finset (Fin 6))
      multiplier tightDir := by
    simpa only [P, point, value, hfamily] using hdata
  obtain ⟨L, M, hleft, hrepresentation, hsymm, hidem, htrace⟩ :=
    crux.exists_orbitFour_coefficientProjection hfamily hdata
  have hzeroLeft := congrFun (congrFun hrepresentation (0 : Fin 6)) (1 : Fin 4)
  have hzeroRight := congrFun (congrFun hrepresentation (0 : Fin 6)) (2 : Fin 4)
  have hthreeLeft := congrFun (congrFun hrepresentation (3 : Fin 6)) (1 : Fin 4)
  have hthreeRight := congrFun (congrFun hrepresentation (3 : Fin 6)) (2 : Fin 4)
  have hprivate := congrFun (congrFun hrepresentation (4 : Fin 6)) (3 : Fin 4)
  have himageZeroLeft := projection_mul_orbitFourWeightedColumn_apply
    hdataOrbit (1 : Fin 4) (0 : Fin 6) (by
      simp [orbitFourLabel, orbitFourBlockZeroOneThree])
  have himageZeroRight := projection_mul_orbitFourWeightedColumn_apply
    hdataOrbit (2 : Fin 4) (0 : Fin 6) (by
      simp [orbitFourLabel, orbitFourBlockZeroTwoThree])
  have himageThreeLeft := projection_mul_orbitFourWeightedColumn_apply
    hdataOrbit (1 : Fin 4) (3 : Fin 6) (by
      simp [orbitFourLabel, orbitFourBlockZeroOneThree])
  have himageThreeRight := projection_mul_orbitFourWeightedColumn_apply
    hdataOrbit (2 : Fin 4) (3 : Fin 6) (by
      simp [orbitFourLabel, orbitFourBlockZeroTwoThree])
  have himagePrivate := projection_mul_orbitFourWeightedColumn_apply
    hdataOrbit (3 : Fin 4) (4 : Fin 6) (by
      simp [orbitFourLabel, orbitFourBlockOneFourFive])
  change (P * B) 0 1 = (B * M) 0 1 at hzeroLeft
  change (P * B) 0 2 = (B * M) 0 2 at hzeroRight
  change (P * B) 3 1 = (B * M) 3 1 at hthreeLeft
  change (P * B) 3 2 = (B * M) 3 2 at hthreeRight
  change (P * B) 4 3 = (B * M) 4 3 at hprivate
  change (P * B) 0 1 = (value + point.weight 0) * B 0 1 at himageZeroLeft
  change (P * B) 0 2 = (value + point.weight 0) * B 0 2 at himageZeroRight
  change (P * B) 3 1 = (value + point.weight 3) * B 3 1 at himageThreeLeft
  change (P * B) 3 2 = (value + point.weight 3) * B 3 2 at himageThreeRight
  change (P * B) 4 3 = (value + point.weight 4) * B 4 3 at himagePrivate
  rw [himageZeroLeft, Matrix.mul_apply, hrowZero, Fin.sum_univ_four] at hzeroLeft
  rw [himageZeroRight, Matrix.mul_apply, hrowZero, Fin.sum_univ_four] at hzeroRight
  rw [himageThreeLeft, Matrix.mul_apply, hrowThree, Fin.sum_univ_four] at hthreeLeft
  rw [himageThreeRight, Matrix.mul_apply, hrowThree, Fin.sum_univ_four] at hthreeRight
  rw [himagePrivate, Matrix.mul_apply, hrowFour, Fin.sum_univ_four] at hprivate
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hzeroLeft
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hzeroRight
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hthreeLeft
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hthreeRight
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hprivate
  have htraceEntries : M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four] using htrace
  have hshiftedNonneg (atomIndex : Fin 6) :
      0 ≤ value + point.weight atomIndex := by
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
    change -value ≤ point.weight atomIndex at hfloor
    linarith
  have hshiftedSum :
      (value + point.weight 0) + (value + point.weight 1)
        + (value + point.weight 2) + (value + point.weight 3)
        + (value + point.weight 4) + (value + point.weight 5) < 1 := by
    have hsum := hdata.weight_sum_one
    rw [Fin.sum_univ_six] at hsum
    have hnegative : value < 0 := by
      simpa only [value, point] using crux.hasNegativeChartValue
    linarith
  exact false_of_typeNine_reflected_general_coordinates hsymm hidem
    hendpoint hk (hshiftedNonneg 1) (hshiftedNonneg 2) (hshiftedNonneg 5)
    hzeroLeft.symm hzeroRight.symm hthreeLeft.symm hthreeRight.symm hprivate.symm htraceEntries
    hshiftedSum

/-- Consequently the endpoint rows of every surviving canonical type-nine
configuration are aligned. -/
theorem SixThreeCrux.orbitFour_endpoint_det_eq_zero
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = orbitFourFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    {a r c f k : ℝ}
    (hrowZero :
      (orbitFourWeightedTightColumns multiplier tightDir) 0
        = (![0, a, r, 0] : Fin 4 → ℝ))
    (hrowThree :
      (orbitFourWeightedTightColumns multiplier tightDir) 3
        = (![0, c, f, 0] : Fin 4 → ℝ))
    (hrowFour :
      (orbitFourWeightedTightColumns multiplier tightDir) 4
        = (![0, 0, 0, k] : Fin 4 → ℝ))
    (hk : k ≠ 0) :
    a * f - r * c = 0 := by
  by_contra hdet
  exact crux.false_of_orbitFour_reflectedRows hfamily hdata hrowZero
    hrowThree hrowFour hdet hk

/-- Division-free conversion of endpoint determinant zero into an aligned
row relation. -/
theorem exists_nonzero_alignment_of_endpoint_det_eq_zero
    {a r c f : ℝ}
    (ha : a ≠ 0) (hr : r ≠ 0)
    (hdet : a * f - r * c = 0) :
    ∃ scale : ℝ, scale ≠ 0 ∧ r = scale * a ∧ f = scale * c := by
  refine ⟨r / a, div_ne_zero hr ha, ?_, ?_⟩
  · field_simp
  · apply (mul_left_cancel₀ ha)
    field_simp [ha] at hdet ⊢
    linarith


end Gtz
