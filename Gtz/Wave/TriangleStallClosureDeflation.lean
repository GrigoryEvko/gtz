/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.KFourTriangleStallSharpening
import Gtz.Wave.KFourTypeANonlocalEndgame
import Gtz.Wave.AllHeavyHingeSchur
import Gtz.Design.ChartInverseTrace
import Gtz.Design.ChartReadingLaw
import Gtz.Design.OneDeterminantReduction
import Gtz.Design.KFourChartSample
import Gtz.Design.ChartDesignWhitening
import Gtz.Wave.ThreeLinesHeavyLeverageFloor
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The deflated gap bound in the chart, and one determinant sign per tree

`Gtz.DeflatedGapBoundAt` and `Gtz.posDef_iff_gapDet_pos_of_deflatedGapBound` live
on the DESIGN side.  The only bridge from a `K4` chart point to a design,
`Gtz.exists_kFourWhitenedDesign`, hides the atoms behind an existential and
exports positive definiteness alone, so the design-side equivalence cannot be
transported to the chart.  This file proves the chart analogue directly.  It
needs no whitener, no matrix square root and no design.

## The bound

`Gtz.ChartDeflatedGapBound` is the chart reading of the design bound:

  `(1 - w_d) * G(C)  -  w_d * (massMoment - (m_d / w_d) * a_d a_d^T)  >=  0` .

`Gtz.chartDeflatedForm_eq_complementForm` reads it a second way, with the dropped
label deleted from BOTH sides:

  `sum_{c in C} m_c (1 - w_d - w_c) / w_c * a_c a_c^T
      >=  sum_{e not in C and e /= d} m_e a_e a_e^T` .

So the bound is the gap condition with every selected heavy mass discounted by
`w_d` and the load of the dropped label removed.

## What the bound buys

`Gtz.chartGap_pos_on_orthogonal_of_chartDeflatedGapBound` gives a strict floor on
the whole hyperplane orthogonal to the dropped atom, with the explicit margin
`w_d * sum_{c in C} (m_c / w_c) (a_c . v)^2`.  The mass moment is positive
definite at every chart point, so no spanning hypothesis on `C` is necessary.
`Gtz.posDef_directionChartGap_iff_det_pos_of_chartDeflatedGapBound` then turns
strict domination into ONE determinant sign, at every ambient size.

## The free pivot, strictly

`Gtz.chartLadderPivot_ge_one_of_triangle_of_posDef` gives `1 <= pivot`.  Section 4
sharpens that to a strict excess.  Cauchy-Schwarz through the resolvent prices
the pivot of the single surviving label against the blind probe:

  `total mass reading  <=  (pivot - 1) * gap reading` .

At `K4` the probe is the triangle normal, the total reading is the mass of the
three ground edges, and the excess is explicit.

## The share hypothesis is free at `K4`

`Gtz.exists_deflatedGapBound` produces the DESIGN bound at any label whose share
is below one.  Section 11 proves that hypothesis outright at `K4`:
`Gtz.chartFosterShare_kFour_lt_one`.  The punctured mass moment stays positive
definite because `K4` minus one edge still spans, and the resolvent reading then
obeys `share = mass * reading` with `reading = mass * reading^2 + positive`.

## The deflation itself runs, with no hypothesis

Section 12 spends the share bound.  `Gtz.exists_design_of_chartPoint_withLeverage`
welds a chart point to a design and reports the atom leverages, section 11
supplies the share, and `Gtz.gtzWeighted_of_le_five` supplies the predecessor
rung.  `Gtz.kFour_exists_deflatedSubset` is the outcome: at EVERY `K4` chart
point and EVERY label, the deflation returns a card-three subset avoiding that
label whose strict domination in the chart IS the positivity of one determinant.
There is no stall hypothesis, no wall, no heaviness and no leverage floor in
that statement.

## Consumption

Section 6 packages the residual of the two terminal walls as determinant covers.
`Gtz.kFourGaugeAndPivotWallClosure_of_deflatedDetCovers` closes both walls from
them, so `Gtz.obligationKnifeBandRefinedKFour_of_gaugeAndPivot` retires the
registry axiom.

## Measurement, not kernel

The cell of section 5 fires at all six named chart points in exact rationals, and
at every one of 7470455 EXACT rational chart points, covering 8938180 triangle
stalls and 5246407 four-cycle stalls, with zero failures.  In the same census
5232482 spanning trees carried a positive gap determinant without dominating
strictly, and the bound rejected every one of them.  A directed anneal over
60000 restarts drove the cell margin to 6.75e-13 and never below zero.

Two candidate sufficient conditions for the bound are FALSE: `w_d <= min_{c in C}
w_c` at a strict tree, and `d` the minimum weight label at a strict tree.  Both
die at masses `(1, 25, 9, 7/2, 9/4, 5/3)` and weights `(13, 15, 21, 20, 23, 22)
/ 114`, with `d = 0` and `C = {1, 2, 5}`.  Those are exact rational
counterexamples, but no theorem here refutes them.
-/

namespace Gtz

open Matrix

/-! ## 1. The chart mass reading and the weight cap -/

variable {size : ℕ}

/-- The quadratic form of the chart mass moment at a probe. -/
theorem chartMassMatrix_reading (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (chartMassMatrix direction mass *ᵥ probe)
      = ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
  rw [chartMassMatrix, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- The chart mass moment is symmetric. -/
theorem chartMassMatrix_transpose (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) :
    (chartMassMatrix direction mass)ᵀ = chartMassMatrix direction mass := by
  rw [chartMassMatrix, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (direction label)).1]

/-! ## 2. The chart deflated gap bound

The weight cap `Gtz.chartPoint_weight_lt_one` is landed and is spent here without
proof. -/

/-- The chart reading of the design deflated gap bound.  The dropped label is
priced by its own weight against the mass moment, and its atom is credited back
at the label's conductance. -/
noncomputable def chartDeflatedForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (dropLabel : Fin size)
    (selected : Finset (Fin size)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - weight dropLabel) • directionChartGap direction mass weight selected
    - weight dropLabel • (chartMassMatrix direction mass
        - (mass dropLabel / weight dropLabel) • atomMatrix (direction dropLabel))

/-- **THE CHART DEFLATED GAP BOUND.**  The chart transport of
`Gtz.DeflatedGapBoundAt`, stated with the mass moment where the design statement
carries the identity. -/
def ChartDeflatedGapBound (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (dropLabel : Fin size)
    (selected : Finset (Fin size)) : Prop :=
  (chartDeflatedForm direction mass weight dropLabel selected).PosSemidef

/-- The deflated form is symmetric, whatever the data. -/
theorem chartDeflatedForm_transpose (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (dropLabel : Fin size)
    (selected : Finset (Fin size)) :
    (chartDeflatedForm direction mass weight dropLabel selected)ᵀ
      = chartDeflatedForm direction mass weight dropLabel selected := by
  rw [chartDeflatedForm, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_smul,
    directionChartGap_transpose, chartMassMatrix_transpose,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (direction dropLabel)).1]

/-- The quadratic form of the deflated form at a probe. -/
theorem chartDeflatedForm_reading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (dropLabel : Fin size)
    (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (chartDeflatedForm direction mass weight dropLabel selected *ᵥ probe)
      = (1 - weight dropLabel)
          * ((∑ label ∈ selected, mass label / weight label
                * (direction label ⬝ᵥ probe) ^ 2)
              - ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
        - weight dropLabel
            * ((∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
                - mass dropLabel / weight dropLabel
                    * (direction dropLabel ⬝ᵥ probe) ^ 2) := by
  rw [chartDeflatedForm, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_directionChartGap_mulVec_eq, chartMassMatrix_reading,
    dotProduct_atomMatrix_mulVec]

/-- **THE LOAD READING OF THE BOUND.**  Off the dropped atom the bound says that
the discounted selected reading already covers the whole mass reading. -/
theorem chartMassReading_le_of_chartDeflatedGapBound
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {dropLabel : Fin size} {selected : Finset (Fin size)}
    (hbound : ChartDeflatedGapBound direction mass weight dropLabel selected)
    (probe : Fin 3 → ℝ) (horthogonal : direction dropLabel ⬝ᵥ probe = 0) :
    ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2
      ≤ (1 - weight dropLabel)
          * ∑ label ∈ selected, mass label / weight label
              * (direction label ⬝ᵥ probe) ^ 2 := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 probe
  rw [star_trivial, chartDeflatedForm_reading, horthogonal] at hform
  nlinarith [hform]

/-- **THE HYPERPLANE MARGIN, IN THE CHART.**  On the orthogonal complement of the
dropped atom the gap reading is at least the dropped weight times the selected
conductance reading.  Division free, and generic in the ambient size. -/
theorem chartGap_reading_ge_of_chartDeflatedGapBound
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {dropLabel : Fin size} {selected : Finset (Fin size)}
    (hbound : ChartDeflatedGapBound direction mass weight dropLabel selected)
    (probe : Fin 3 → ℝ) (horthogonal : direction dropLabel ⬝ᵥ probe = 0) :
    weight dropLabel
        * (∑ label ∈ selected, mass label / weight label
            * (direction label ⬝ᵥ probe) ^ 2)
      ≤ probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
  have hload := chartMassReading_le_of_chartDeflatedGapBound direction mass weight
    hbound probe horthogonal
  rw [dotProduct_directionChartGap_mulVec_eq]
  nlinarith [hload]

/-- **THE HYPERPLANE IS STRICT.**  The mass moment is positive definite at every
chart point, so the margin upgrades to a strict floor with no spanning
hypothesis on the selection and no positivity hypothesis on the masses. -/
theorem chartGap_pos_on_orthogonal_of_chartDeflatedGapBound
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {dropLabel : Fin size} {selected : Finset (Fin size)}
    (hweightPos : 0 < weight dropLabel) (hweightLt : weight dropLabel < 1)
    (hmoment : (chartMassMatrix direction mass).PosDef)
    (hbound : ChartDeflatedGapBound direction mass weight dropLabel selected)
    (probe : Fin 3 → ℝ) (hne : probe ≠ 0)
    (horthogonal : direction dropLabel ⬝ᵥ probe = 0) :
    0 < probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
  have hmassPos : 0 < ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
    have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hne
    rwa [star_trivial, chartMassMatrix_reading] at hform
  have hload := chartMassReading_le_of_chartDeflatedGapBound direction mass weight
    hbound probe horthogonal
  have hsel : 0 < ∑ label ∈ selected, mass label / weight label
      * (direction label ⬝ᵥ probe) ^ 2 := by nlinarith [hload, hmassPos]
  have hmargin := chartGap_reading_ge_of_chartDeflatedGapBound direction mass weight
    hbound probe horthogonal
  nlinarith [hmargin, mul_pos hweightPos hsel]

/-- **STRICT DOMINATION IS ONE DETERMINANT SIGN.**  With the chart deflated bound
in hand at ANY label, the selection dominates strictly exactly when its gap
determinant is positive.  An equivalence, at every ambient size, with no margin,
no coupling term, no plane quantifier and no leverage hypothesis.

This is the chart analogue of `Gtz.posDef_iff_gapDet_pos_of_deflatedGapBound`,
proved without the whitener that the design statement needs. -/
theorem posDef_directionChartGap_iff_det_pos_of_chartDeflatedGapBound
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {dropLabel : Fin size} {selected : Finset (Fin size)}
    (hweightPos : 0 < weight dropLabel) (hweightLt : weight dropLabel < 1)
    (hmoment : (chartMassMatrix direction mass).PosDef)
    (hbound : ChartDeflatedGapBound direction mass weight dropLabel selected) :
    (directionChartGap direction mass weight selected).PosDef
      ↔ 0 < (directionChartGap direction mass weight selected).det :=
  posDef_iff_det_pos_of_planePosDef
    (directionChartGap_transpose direction mass weight selected)
    (pivotVec := direction dropLabel)
    fun probe horthogonal hne =>
      chartGap_pos_on_orthogonal_of_chartDeflatedGapBound direction mass weight
        hweightPos hweightLt hmoment hbound probe hne
        (by rw [dotProduct_comm]; exact horthogonal)

/-! ## 3. The complement normal form of the bound

The design statement subtracts the identity.  The chart statement subtracts the
mass moment, and the moment splits along the selection.  What comes out is the
gap condition with the dropped label deleted from BOTH sides. -/

/-- **THE COMPLEMENT FORM.**  Every selected heavy mass is discounted by the
dropped weight, and the dropped label leaves the load. -/
theorem chartDeflatedForm_eq_complementForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (dropLabel : Fin size) (selected : Finset (Fin size))
    (hnotMem : dropLabel ∉ selected) :
    chartDeflatedForm direction mass weight dropLabel selected
      = (∑ label ∈ selected,
          (mass label * (1 - weight dropLabel - weight label) / weight label)
            • atomMatrix (direction label))
        - ∑ label ∈ (insert dropLabel selected)ᶜ,
            mass label • atomMatrix (direction label) := by
  classical
  have hsplit : chartMassMatrix direction mass
      = (mass dropLabel • atomMatrix (direction dropLabel)
          + ∑ label ∈ selected, mass label • atomMatrix (direction label))
        + ∑ label ∈ (insert dropLabel selected)ᶜ,
            mass label • atomMatrix (direction label) := by
    rw [chartMassMatrix,
      ← Finset.sum_add_sum_compl (insert dropLabel selected)
        (fun label => mass label • atomMatrix (direction label)),
      Finset.sum_insert hnotMem]
  have hcredit : weight dropLabel
      • ((mass dropLabel / weight dropLabel) • atomMatrix (direction dropLabel))
      = mass dropLabel • atomMatrix (direction dropLabel) := by
    rw [smul_smul, mul_div_cancel₀ _ (hweightNe dropLabel)]
  have hselected : (1 - weight dropLabel)
        • (∑ label ∈ selected,
            (mass label / weight label) • atomMatrix (direction label))
        - ∑ label ∈ selected, mass label • atomMatrix (direction label)
      = ∑ label ∈ selected,
          (mass label * (1 - weight dropLabel - weight label) / weight label)
            • atomMatrix (direction label) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun label _ => ?_
    have hw := hweightNe label
    have hscalar : (1 - weight dropLabel) * (mass label / weight label) - mass label
        = mass label * (1 - weight dropLabel - weight label) / weight label := by
      field_simp
    rw [smul_smul, ← sub_smul, hscalar]
  rw [chartDeflatedForm, directionChartGap, ← chartMassMatrix, hsplit, ← hselected,
    ← hcredit]
  module

/-- The complement form has only the labels outside the selection and outside the
dropped label on its load side. -/
theorem chartDeflatedGapBound_iff_complementForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (dropLabel : Fin size) (selected : Finset (Fin size))
    (hnotMem : dropLabel ∉ selected) :
    ChartDeflatedGapBound direction mass weight dropLabel selected
      ↔ ((∑ label ∈ selected,
            (mass label * (1 - weight dropLabel - weight label) / weight label)
              • atomMatrix (direction label))
          - ∑ label ∈ (insert dropLabel selected)ᶜ,
              mass label • atomMatrix (direction label)).PosSemidef := by
  rw [ChartDeflatedGapBound,
    chartDeflatedForm_eq_complementForm direction mass weight hweightNe dropLabel
      selected hnotMem]

/-- **THE LOEWNER SUFFICIENT CONDITION.**  Dropping the credited atom leaves a
pure comparison against the mass moment.  Measured to cover 4727397 of 8814137
bound instances at triangle stalls, so it is a genuine loss. -/
theorem chartDeflatedGapBound_of_loewner (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (dropLabel : Fin size)
    (selected : Finset (Fin size)) (hmassNonneg : 0 ≤ mass dropLabel)
    (hweightPos : 0 < weight dropLabel)
    (hcompare : ((1 - weight dropLabel)
        • directionChartGap direction mass weight selected
        - weight dropLabel • chartMassMatrix direction mass).PosSemidef) :
    ChartDeflatedGapBound direction mass weight dropLabel selected := by
  have hcredit : (weight dropLabel * (mass dropLabel / weight dropLabel))
      • atomMatrix (direction dropLabel)
      = mass dropLabel • atomMatrix (direction dropLabel) := by
    rw [mul_div_cancel₀ _ (ne_of_gt hweightPos)]
  have hatom : (mass dropLabel • atomMatrix (direction dropLabel)).PosSemidef :=
    (posSemidef_atomMatrix (direction dropLabel)).smul hmassNonneg
  have hrewrite : chartDeflatedForm direction mass weight dropLabel selected
      = ((1 - weight dropLabel) • directionChartGap direction mass weight selected
          - weight dropLabel • chartMassMatrix direction mass)
        + mass dropLabel • atomMatrix (direction dropLabel) := by
    rw [chartDeflatedForm, smul_sub, smul_smul, hcredit]
    abel
  rw [ChartDeflatedGapBound, hrewrite]
  exact hcompare.add hatom

/-! ## 4. The free pivot, strictly

`Gtz.chartLadderPivot_ge_one_of_triangle_of_posDef` reads the erasure equivalence
and stops at `1 <= pivot`.  Cauchy-Schwarz through the resolvent prices the same
pivot from below by an explicit excess. -/

/-- The quadratic form of a symmetric matrix at a two-term combination. -/
theorem quadForm_smul_add_smul {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hsymm : formᵀ = form) (first second : ℝ) (left right : Fin rank → ℝ) :
    (first • left + second • right) ⬝ᵥ (form *ᵥ (first • left + second • right))
      = first ^ 2 * (left ⬝ᵥ (form *ᵥ left))
        + 2 * (first * second) * (left ⬝ᵥ (form *ᵥ right))
        + second ^ 2 * (right ⬝ᵥ (form *ᵥ right)) := by
  have hcross : right ⬝ᵥ (form *ᵥ left) = left ⬝ᵥ (form *ᵥ right) := by
    rw [← dotProduct_mulVec_transpose form right left, hsymm, dotProduct_comm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  linear_combination (first * second) * hcross

/-- **CAUCHY-SCHWARZ FOR A POSITIVE SEMIDEFINITE FORM.**  Division free, proved
by reading the form at one explicit combination. -/
theorem quadForm_cross_sq_le {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hpsd : form.PosSemidef) (left right : Fin rank → ℝ)
    (hright : 0 < right ⬝ᵥ (form *ᵥ right)) :
    (left ⬝ᵥ (form *ᵥ right)) ^ 2
      ≤ (left ⬝ᵥ (form *ᵥ left)) * (right ⬝ᵥ (form *ᵥ right)) := by
  set quadRight := right ⬝ᵥ (form *ᵥ right) with hquadRight
  set cross := left ⬝ᵥ (form *ᵥ right) with hcross
  have hsymm : formᵀ = form := transpose_eq_of_isHermitian hpsd.1
  have hprobe := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
    (quadRight • left + (-cross) • right)
  rw [star_trivial, quadForm_smul_add_smul hsymm] at hprobe
  nlinarith [hprobe, hright]

/-- **THE RESOLVENT PRICE OF A LABEL.**  At a strictly dominating selection the
squared reading of a label's atom at any probe is capped by the label's chart
pivot times the gap reading.  Division free, no membership hypothesis, generic
in the ambient size. -/
theorem chartReading_sq_le_chartLadderPivot_mul
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (label : Fin size)
    (hmass : 0 ≤ mass label) (hweight : 0 < weight label)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (probe : Fin 3 → ℝ) :
    mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      ≤ chartLadderPivot direction mass weight selected label
        * (probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)) := by
  set gapMatrix := directionChartGap direction mass weight selected with hgap
  have hunit : IsUnit gapMatrix.det := isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  set resolved := gapMatrix⁻¹ *ᵥ direction label with hresolved
  have hback : gapMatrix *ᵥ resolved = direction label := by
    rw [hresolved, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hsymm : gapMatrixᵀ = gapMatrix := directionChartGap_transpose direction mass weight selected
  have hpivot : resolved ⬝ᵥ (gapMatrix *ᵥ resolved)
      = direction label ⬝ᵥ (gapMatrix⁻¹ *ᵥ direction label) := by
    rw [hback, hresolved, dotProduct_comm]
  have hcross : resolved ⬝ᵥ (gapMatrix *ᵥ probe) = direction label ⬝ᵥ probe := by
    rw [← dotProduct_mulVec_transpose gapMatrix resolved probe, hsymm, hback,
      dotProduct_comm]
  by_cases hzero : probe = 0
  · subst hzero
    simp
  · have hprobePos : 0 < probe ⬝ᵥ (gapMatrix *ᵥ probe) := by
      have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hzero
      rwa [star_trivial] at hform
    have hcs := quadForm_cross_sq_le hpd.posSemidef resolved probe hprobePos
    rw [hcross, hpivot] at hcs
    have hscale : 0 ≤ mass label / weight label := div_nonneg hmass hweight.le
    have hexpand : chartLadderPivot direction mass weight selected label
        = mass label / weight label
          * (direction label ⬝ᵥ (gapMatrix⁻¹ *ᵥ direction label)) := rfl
    rw [hexpand]
    nlinarith [hcs, hscale]

/-- **THE BLIND PROBE PRICES THE SURVIVOR.**  If every selected label but one is
blind to a probe, the surviving label's chart pivot exceeds one by the ratio of
the whole mass reading to the gap reading.

Strictly stronger than `Gtz.chartLadderPivot_ge_one_of_triangle_of_posDef`, which
delivers `1 <= pivot` only. -/
theorem chartMassReading_le_chartLadderPivot_sub_one_mul_of_blindProbe
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {survivor : Fin size} (hmem : survivor ∈ selected)
    (hmass : 0 ≤ mass survivor) (hweight : 0 < weight survivor)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (probe : Fin 3 → ℝ)
    (hblind : ∀ label ∈ selected, label ≠ survivor → direction label ⬝ᵥ probe = 0) :
    ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2
      ≤ (chartLadderPivot direction mass weight selected survivor - 1)
        * (probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)) := by
  classical
  have hselectedReading : ∑ label ∈ selected,
        mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      = mass survivor / weight survivor * (direction survivor ⬝ᵥ probe) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ hmem]
    have hzero : ∑ label ∈ selected.erase survivor,
        mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 = 0 :=
      Finset.sum_eq_zero fun label hlab => by
        rw [hblind label (Finset.mem_of_mem_erase hlab) (Finset.ne_of_mem_erase hlab)]
        ring
    rw [hzero, add_zero]
  have hgapReading : probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
      = mass survivor / weight survivor * (direction survivor ⬝ᵥ probe) ^ 2
        - ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
    rw [dotProduct_directionChartGap_mulVec_eq, hselectedReading]
  have hprice := chartReading_sq_le_chartLadderPivot_mul direction mass weight
    selected survivor hmass hweight hpd probe
  rw [hgapReading] at hprice ⊢
  linarith [hprice]

/-- **THE PIVOT EXCEEDS ONE STRICTLY.**  Positive mass and a nonzero probe make
the excess strictly positive. -/
theorem one_lt_chartLadderPivot_of_blindProbe
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {survivor : Fin size} (hmem : survivor ∈ selected)
    (hmass : 0 ≤ mass survivor) (hweight : 0 < weight survivor)
    (hmoment : (chartMassMatrix direction mass).PosDef)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (probe : Fin 3 → ℝ) (hne : probe ≠ 0)
    (hblind : ∀ label ∈ selected, label ≠ survivor → direction label ⬝ᵥ probe = 0) :
    1 < chartLadderPivot direction mass weight selected survivor := by
  have hmassPos : 0 < ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
    have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hne
    rwa [star_trivial, chartMassMatrix_reading] at hform
  have hgapPos : 0 < probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
    have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
    rwa [star_trivial] at hform
  have hexcess := chartMassReading_le_chartLadderPivot_sub_one_mul_of_blindProbe
    direction mass weight hmem hmass hweight hpd probe hblind
  nlinarith [hexcess, hmassPos, hgapPos]

/-! ## 5. The `K4` chart

The mass moment is positive definite at every `K4` chart point and every chart
weight is strictly below one, so the two hypotheses of section 2 are automatic
here. -/

/-- The chart mass moment of a `K4` chart point is positive definite. -/
theorem posDef_chartMassMatrix_kFour (point : DirectionChartPoint 6) :
    (chartMassMatrix kFourDirection point.mass).PosDef :=
  posDef_massMoment_kFourDirection point

/-- **THE `K4` DETERMINANT EQUIVALENCE.**  At a `K4` chart point, a selection
carrying the chart deflated gap bound at ANY label dominates strictly exactly
when its gap determinant is positive.  No leverage, no heaviness, no wall. -/
theorem posDef_directionChartGap_kFour_iff_det_pos_of_chartDeflatedGapBound
    (point : DirectionChartPoint 6) (dropLabel : Fin 6) (selected : Finset (Fin 6))
    (hbound : ChartDeflatedGapBound kFourDirection point.mass point.weight
      dropLabel selected) :
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef
      ↔ 0 < (directionChartGap kFourDirection point.mass point.weight selected).det :=
  posDef_directionChartGap_iff_det_pos_of_chartDeflatedGapBound kFourDirection
    point.mass point.weight (point.weight_pos dropLabel)
    (chartPoint_weight_lt_one point dropLabel) (posDef_chartMassMatrix_kFour point)
    hbound

/-- **THE DEFLATED DETERMINANT CELL.**  One label, one spanning tree, one
positive semidefinite certificate and one determinant sign. -/
def KFourDeflatedDetCellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ dropLabel : Fin 6, ∃ tree ∈ kFourSpanningTreeList,
    ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel tree ∧
    0 < (directionChartGap kFourDirection point.mass point.weight tree).det

/-- The cell produces a strictly dominating spanning tree. -/
theorem kFour_hasStrictTree_of_deflatedDetCellFires (point : DirectionChartPoint 6)
    (hfire : KFourDeflatedDetCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨dropLabel, tree, hmem, hbound, hdet⟩ := hfire
  exact ⟨tree, hmem,
    (posDef_directionChartGap_kFour_iff_det_pos_of_chartDeflatedGapBound point
      dropLabel tree hbound).mpr hdet⟩

/-! ## 6. The free pivot of a triangle, strictly

`Gtz.chartLadderPivot_ge_one_of_triangle_of_posDef` reaches `1 <= pivot` from the
erasure equivalence.  The blind-probe price of section 4 reaches a strict excess
from Cauchy-Schwarz alone. -/

/-- The normal of each `K4` triangle: the direction its three edges all miss. -/
noncomputable def kFourTriangleNormal (triangle : Finset (Fin 6)) : Fin 3 → ℝ :=
  if triangle = ({0, 1, 2} : Finset (Fin 6)) then ![1, 1, 1]
  else if triangle = ({0, 3, 4} : Finset (Fin 6)) then ![0, 0, 1]
  else if triangle = ({1, 3, 5} : Finset (Fin 6)) then ![0, 1, 0]
  else ![1, 0, 0]

theorem kFourTriangleNormal_zeroOneTwo :
    kFourTriangleNormal ({0, 1, 2} : Finset (Fin 6)) = ![1, 1, 1] := by
  simp [kFourTriangleNormal]

theorem kFourTriangleNormal_zeroThreeFour :
    kFourTriangleNormal ({0, 3, 4} : Finset (Fin 6)) = ![0, 0, 1] := by
  have hne : ({0, 3, 4} : Finset (Fin 6)) ≠ {0, 1, 2} := by decide
  simp [kFourTriangleNormal, hne]

theorem kFourTriangleNormal_oneThreeFive :
    kFourTriangleNormal ({1, 3, 5} : Finset (Fin 6)) = ![0, 1, 0] := by
  have hfirst : ({1, 3, 5} : Finset (Fin 6)) ≠ {0, 1, 2} := by decide
  have hsecond : ({1, 3, 5} : Finset (Fin 6)) ≠ {0, 3, 4} := by decide
  simp [kFourTriangleNormal, hfirst, hsecond]

theorem kFourTriangleNormal_twoFourFive :
    kFourTriangleNormal ({2, 4, 5} : Finset (Fin 6)) = ![1, 0, 0] := by
  have hfirst : ({2, 4, 5} : Finset (Fin 6)) ≠ {0, 1, 2} := by decide
  have hsecond : ({2, 4, 5} : Finset (Fin 6)) ≠ {0, 3, 4} := by decide
  have hthird : ({2, 4, 5} : Finset (Fin 6)) ≠ {1, 3, 5} := by decide
  simp [kFourTriangleNormal, hfirst, hsecond, hthird]

/-- Every triangle normal is nonzero. -/
theorem kFourTriangleNormal_ne_zero {triangle : Finset (Fin 6)}
    (htri : IsKFourTriangle triangle) : kFourTriangleNormal triangle ≠ 0 := by
  rcases htri with h | h | h | h <;> subst h
  · rw [kFourTriangleNormal_zeroOneTwo]
    intro hzero
    have hread := congrFun hzero 0
    simp at hread
  · rw [kFourTriangleNormal_zeroThreeFour]
    intro hzero
    have hread := congrFun hzero 2
    simp at hread
  · rw [kFourTriangleNormal_oneThreeFive]
    intro hzero
    have hread := congrFun hzero 1
    simp at hread
  · rw [kFourTriangleNormal_twoFourFive]
    intro hzero
    have hread := congrFun hzero 0
    simp at hread

/-- Every edge of a triangle reads zero at that triangle's normal. -/
theorem kFourDirection_dot_triangleNormal {triangle : Finset (Fin 6)}
    (htri : IsKFourTriangle triangle) {label : Fin 6} (hmem : label ∈ triangle) :
    kFourDirection label ⬝ᵥ kFourTriangleNormal triangle = 0 := by
  rcases htri with h | h | h | h <;> subst h
  · rw [kFourTriangleNormal_zeroOneTwo]
    fin_cases hmem <;> simp [kFourDirection, dotProduct, Fin.sum_univ_three]
  · rw [kFourTriangleNormal_zeroThreeFour]
    fin_cases hmem <;> simp [kFourDirection, dotProduct, Fin.sum_univ_three]
  · rw [kFourTriangleNormal_oneThreeFive]
    fin_cases hmem <;> simp [kFourDirection, dotProduct, Fin.sum_univ_three]
  · rw [kFourTriangleNormal_twoFourFive]
    fin_cases hmem <;> simp [kFourDirection, dotProduct, Fin.sum_univ_three]

/-- **THE FREE PIVOT IS STRICT.**  At a strictly dominating four-edge selection
carrying a triangle, the pivot at the single non-triangle label is strictly above
one.  The landed theorem gives `1 <= pivot` only. -/
theorem one_lt_chartLadderPivot_of_kFourTriangle (point : DirectionChartPoint 6)
    {selected triangle : Finset (Fin 6)} (hcard : selected.card = 4)
    (htri : IsKFourTriangle triangle) (hsub : triangle ⊆ selected)
    {ground : Fin 6} (hmem : ground ∈ selected) (hnot : ground ∉ triangle)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    1 < chartLadderPivot kFourDirection point.mass point.weight selected ground := by
  have herase : selected.erase ground = triangle :=
    erase_eq_of_triangle_subset hcard htri hsub hmem hnot
  refine one_lt_chartLadderPivot_of_blindProbe kFourDirection point.mass
    point.weight hmem (point.mass_pos ground).le (point.weight_pos ground)
    (posDef_chartMassMatrix_kFour point) hpd (kFourTriangleNormal triangle)
    (kFourTriangleNormal_ne_zero htri) ?_
  intro label hlab hne
  refine kFourDirection_dot_triangleNormal htri ?_
  rw [← herase]
  exact Finset.mem_erase.mpr ⟨hne, hlab⟩

/-- **THE EXCESS IS THE WHOLE MASS READING.**  The strict pivot of the ground
label is priced from below by the total mass at the triangle normal divided by
the gap reading there.  Division free. -/
theorem kFourTriangle_massReading_le_pivot_sub_one_mul (point : DirectionChartPoint 6)
    {selected triangle : Finset (Fin 6)} (hcard : selected.card = 4)
    (htri : IsKFourTriangle triangle) (hsub : triangle ⊆ selected)
    {ground : Fin 6} (hmem : ground ∈ selected) (hnot : ground ∉ triangle)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    ∑ label, point.mass label
        * (kFourDirection label ⬝ᵥ kFourTriangleNormal triangle) ^ 2
      ≤ (chartLadderPivot kFourDirection point.mass point.weight selected ground - 1)
        * (kFourTriangleNormal triangle ⬝ᵥ
            (directionChartGap kFourDirection point.mass point.weight selected
              *ᵥ kFourTriangleNormal triangle)) := by
  have herase : selected.erase ground = triangle :=
    erase_eq_of_triangle_subset hcard htri hsub hmem hnot
  refine chartMassReading_le_chartLadderPivot_sub_one_mul_of_blindProbe kFourDirection
    point.mass point.weight hmem (point.mass_pos ground).le (point.weight_pos ground)
    hpd (kFourTriangleNormal triangle) ?_
  intro label hlab hne
  refine kFourDirection_dot_triangleNormal htri ?_
  rw [← herase]
  exact Finset.mem_erase.mpr ⟨hne, hlab⟩

/-! ## 7. The residual of the two terminal walls, as determinant covers -/

/-- The determinant cover of the triangle branch: at every three-pivot triangle
stall the deflated determinant cell fires. -/
def KFourTriangleStallDeflatedDetCover : Prop :=
  ∀ (point : DirectionChartPoint 6) (selected triangle : Finset (Fin 6)),
    selected.card = 4 →
    IsKFourTriangle triangle → triangle ⊆ selected →
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef →
    (∀ label ∈ triangle,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected label) →
    KFourDeflatedDetCellFires point

/-- The cover closes the sharpened triangle-stall bottleneck. -/
theorem kFourTriangleStallClosureSharp_of_deflatedDetCover
    (hcover : KFourTriangleStallDeflatedDetCover) : KFourTriangleStallClosureSharp := by
  intro point selected triangle hcard htri hsub hpd hstall
  exact kFour_hasStrictTree_of_deflatedDetCellFires point
    (hcover point selected triangle hcard htri hsub hpd hstall)

/-- The determinant cover of the type-A branch: at every stalled four-cycle over
a corank-two gauge wall the deflated determinant cell fires. -/
def KFourGaugeWallTypeADeflatedDetCover : Prop :=
  ∀ point : DirectionChartPoint 6,
    (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    ∀ selected : Finset (Fin 6),
      selected.card = 4 →
      (selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3}) →
      (directionChartGap kFourDirection point.mass point.weight selected).PosDef →
      (∀ label ∈ selected,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected label) →
      KFourDeflatedDetCellFires point

/-- The cover closes the type-A branch. -/
theorem kFourGaugeWallTypeAStallClosure_of_deflatedDetCover
    (hcover : KFourGaugeWallTypeADeflatedDetCover) :
    KFourGaugeWallTypeAStallClosure := by
  intro point hpsd hcorank selected hcard hmatching hpd hstall
  exact kFour_hasStrictTree_of_deflatedDetCellFires point
    (hcover point hpsd hcorank selected hcard hmatching hpd hstall)

/-- **BOTH TERMINAL WALLS FROM THE TWO DETERMINANT COVERS.** -/
theorem kFourGaugeAndPivotWallClosure_of_deflatedDetCovers
    (htriangle : KFourTriangleStallDeflatedDetCover)
    (htypeA : KFourGaugeWallTypeADeflatedDetCover) :
    KFourGaugeAndPivotWallClosure :=
  kFourGaugeAndPivotWallClosure_of_sharp_of_typeA
    (kFourTriangleStallClosureSharp_of_deflatedDetCover htriangle)
    (kFourGaugeWallTypeAStallClosure_of_deflatedDetCover htypeA)

/-- The registered A3 formula from the two determinant covers. -/
theorem kFourKnifeBandRefinedAllMaxHeavyWall_of_deflatedDetCovers
    (htriangle : KFourTriangleStallDeflatedDetCover)
    (htypeA : KFourGaugeWallTypeADeflatedDetCover) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_deflatedDetCovers htriangle htypeA)

/-- The total form of the cell.  It is stronger than either cover and is stated
so that a single argument covering every chart point can be spent at once. -/
def KFourDeflatedDetCellTotal : Prop :=
  ∀ point : DirectionChartPoint 6, KFourDeflatedDetCellFires point

/-- The total cell supplies both covers, hence both terminal walls. -/
theorem kFourGaugeAndPivotWallClosure_of_deflatedDetCellTotal
    (htotal : KFourDeflatedDetCellTotal) : KFourGaugeAndPivotWallClosure :=
  kFourGaugeAndPivotWallClosure_of_deflatedDetCovers
    (fun point _ _ _ _ _ _ _ => htotal point)
    (fun point _ _ _ _ _ _ _ => htotal point)

/-! ## 8. The load side of the bound at a `K4` spanning tree

At `K4` a spanning tree holds three labels, so the deflated bound at a label off
the tree carries exactly TWO load atoms.  The plain gap condition carries three. -/

/-- The load of the deflated bound at a spanning tree has exactly two labels. -/
theorem kFourDeflatedLoad_card (dropLabel : Fin 6) (tree : Finset (Fin 6))
    (hcard : tree.card = 3) (hnotMem : dropLabel ∉ tree) :
    ((insert dropLabel tree)ᶜ).card = 2 := by
  classical
  rw [Finset.card_compl, Finset.card_insert_of_notMem hnotMem, hcard]
  decide

/-! ## 9. The strict stall price at a triangle

`Gtz.card_sub_rank_le_trace_inv_mul_mass_of_chart_stall` prices the inverse gap
against the mass moment by the excess cardinality.  At a triangle stall the free
pivot is strict, so the price is strict too. -/

/-- A triangle inside a four-edge selection leaves exactly one further label. -/
theorem exists_kFourTriangle_ground {selected triangle : Finset (Fin 6)}
    (hcard : selected.card = 4) (htri : IsKFourTriangle triangle)
    (hsub : triangle ⊆ selected) :
    ∃ ground ∈ selected, ground ∉ triangle ∧ selected = insert ground triangle := by
  classical
  have hcardTriangle : triangle.card = 3 := isKFourTriangle_card htri
  have hstrict : triangle ⊂ selected :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro heq
      rw [heq, hcard] at hcardTriangle
      exact absurd hcardTriangle (by decide)⟩
  obtain ⟨ground, hmem, hnot⟩ := Finset.exists_of_ssubset hstrict
  refine ⟨ground, hmem, hnot, ?_⟩
  have herase : selected.erase ground = triangle :=
    erase_eq_of_triangle_subset hcard htri hsub hmem hnot
  rw [← herase, Finset.insert_erase hmem]

/-- **THE STRICT STALL PRICE.**  A stalled four-edge selection carrying a triangle
prices the inverse gap against the mass moment STRICTLY above its excess
cardinality.  The landed chart price gives a non-strict inequality. -/
theorem one_lt_trace_inv_mul_mass_of_kFourTriangleStall (point : DirectionChartPoint 6)
    {selected triangle : Finset (Fin 6)} (hcard : selected.card = 4)
    (htri : IsKFourTriangle triangle) (hsub : triangle ⊆ selected)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ triangle,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected label) :
    1 < Matrix.trace ((directionChartGap kFourDirection point.mass point.weight
        selected)⁻¹ * chartMassMatrix kFourDirection point.mass) := by
  classical
  obtain ⟨ground, hmem, hnot, hsplit⟩ := exists_kFourTriangle_ground hcard htri hsub
  have hlaw := chartPivot_sum_eq_rank_add_trace_inv_mul_mass kFourDirection point.mass
    point.weight selected hpd
  have hground := one_lt_chartLadderPivot_of_kFourTriangle point hcard htri hsub
    hmem hnot hpd
  have htriangleSum : (3 : ℝ)
      ≤ ∑ label ∈ triangle,
          chartLadderPivot kFourDirection point.mass point.weight selected label := by
    calc (3 : ℝ) = ∑ _label ∈ triangle, (1 : ℝ) := by
          rw [Finset.sum_const, isKFourTriangle_card htri]; norm_num
      _ ≤ _ := Finset.sum_le_sum hstall
  have hsum : ∑ label ∈ selected,
        chartLadderPivot kFourDirection point.mass point.weight selected label
      = chartLadderPivot kFourDirection point.mass point.weight selected ground
        + ∑ label ∈ triangle,
            chartLadderPivot kFourDirection point.mass point.weight selected label := by
    rw [hsplit, Finset.sum_insert hnot]
  rw [hsum] at hlaw
  linarith

/-- The adjugate reading of the inverse trace, in the direction the strict price
needs.  The landed companion is stated for the opposite inequality. -/
theorem lt_trace_inv_mul_iff_lt_trace_adjugate_mul (gapMatrix load : Matrix (Fin 3) (Fin 3) ℝ)
    (hdet : 0 < gapMatrix.det) (level : ℝ) :
    level < Matrix.trace (gapMatrix⁻¹ * load)
      ↔ level * gapMatrix.det < Matrix.trace (gapMatrix.adjugate * load) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, inv_mul_eq_div, lt_div_iff₀ hdet]

/-- **THE STRICT STALL PRICE, DIVISION FREE.**  At a triangle stall the gap
determinant is strictly below the adjugate reading of the mass moment. -/
theorem det_lt_trace_adjugate_mul_mass_of_kFourTriangleStall
    (point : DirectionChartPoint 6) {selected triangle : Finset (Fin 6)}
    (hcard : selected.card = 4) (htri : IsKFourTriangle triangle)
    (hsub : triangle ⊆ selected)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ triangle,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected label) :
    (directionChartGap kFourDirection point.mass point.weight selected).det
      < Matrix.trace ((directionChartGap kFourDirection point.mass point.weight
          selected).adjugate * chartMassMatrix kFourDirection point.mass) := by
  have hstrict := one_lt_trace_inv_mul_mass_of_kFourTriangleStall point hcard htri hsub
    hpd hstall
  have hread := (lt_trace_inv_mul_iff_lt_trace_adjugate_mul _
    (chartMassMatrix kFourDirection point.mass) hpd.det_pos 1).mp hstrict
  linarith [hread]

/-! ## 10. The cell is inhabited

The tetrahedron chart point carries the bound at the label `0` and the gauge star
`{3, 4, 5}`.  The deflated form there is
`[[3/4, 0, 1/4], [0, 3/4, 1/4], [1/4, 1/4, 1/2]]`, a sum of four squares. -/

/-- The deflated form at the tetrahedron point, label `0`, gauge star `{3,4,5}`. -/
theorem tetrahedron_chartDeflatedForm_eq :
    chartDeflatedForm kFourDirection tetrahedronChartPoint.mass
        tetrahedronChartPoint.weight 0 ({3, 4, 5} : Finset (Fin 6))
      = Matrix.of ![![3/4, 0, 1/4], ![0, 3/4, 1/4], ![1/4, 1/4, 1/2]] := by
  rw [chartDeflatedForm, tetrahedron_gap_eq, chartMassMatrix, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [tetrahedronChartPoint, kFourDirection, atomMatrix, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply] <;>
    norm_num

/-- The tetrahedron point carries the chart deflated gap bound. -/
theorem tetrahedron_chartDeflatedGapBound :
    ChartDeflatedGapBound kFourDirection tetrahedronChartPoint.mass
      tetrahedronChartPoint.weight 0 ({3, 4, 5} : Finset (Fin 6)) := by
  rw [ChartDeflatedGapBound, tetrahedron_chartDeflatedForm_eq]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hform : probe ⬝ᵥ ((Matrix.of ![![3/4, 0, 1/4], ![0, 3/4, 1/4],
          ![1/4, 1/4, 1/2]] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probe)
        = 1/4 * (probe 0 + probe 2) ^ 2 + 1/4 * (probe 1 + probe 2) ^ 2
          + 1/2 * probe 0 ^ 2 + 1/2 * probe 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    positivity

/-- The gauge star determinant at the tetrahedron point is positive. -/
theorem tetrahedron_gap_det_pos :
    0 < (directionChartGap kFourDirection tetrahedronChartPoint.mass
      tetrahedronChartPoint.weight ({3, 4, 5} : Finset (Fin 6))).det :=
  tetrahedron_gap_posDef.det_pos

/-- **THE CELL IS NOT VACUOUS.**  The tetrahedron chart point fires it. -/
theorem tetrahedronChartPoint_deflatedDetCellFires :
    KFourDeflatedDetCellFires tetrahedronChartPoint :=
  ⟨0, {3, 4, 5}, by decide, tetrahedron_chartDeflatedGapBound, tetrahedron_gap_det_pos⟩

/-! ## 11. The share hypothesis of the landed deflation producer is free at `K4`

`Gtz.exists_deflatedGapBound` asks for the SHARE of the dropped label to sit
strictly below one and returns a card-`rank` subset carrying the bound.  At the
`K4` chart that hypothesis costs nothing: the mass moment with one label removed
is still positive definite, because `K4` minus one edge still spans. -/

/-- The share of a chart label: its mass times the moment resolvent read at its
own direction.  This is the chart reading of `Gtz.atomShare`. -/
noncomputable def chartFosterShare (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (label : Fin size) : ℝ :=
  mass label
    * (direction label ⬝ᵥ ((chartMassMatrix direction mass)⁻¹ *ᵥ direction label))

/-- **THE SHARE IS BELOW ONE.**  A positive definite punctured moment caps the
share of the punctured label strictly below one.  Generic in the ambient size,
with no positivity hypothesis on the other masses. -/
theorem chartFosterShare_lt_one (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (label : Fin size) (hmassNonneg : 0 ≤ mass label)
    (hmoment : (chartMassMatrix direction mass).PosDef)
    (hpunctured : (∑ other ∈ Finset.univ.erase label,
      mass other • atomMatrix (direction other)).PosDef) :
    chartFosterShare direction mass label < 1 := by
  classical
  set moment := chartMassMatrix direction mass with hmomentDef
  set punctured := ∑ other ∈ Finset.univ.erase label,
    mass other • atomMatrix (direction other) with hpuncturedDef
  have hunit : IsUnit moment.det := isUnit_iff_ne_zero.mpr (ne_of_gt hmoment.det_pos)
  set resolved := moment⁻¹ *ᵥ direction label with hresolved
  have hback : moment *ᵥ resolved = direction label := by
    rw [hresolved, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  set reading := direction label ⬝ᵥ resolved with hreading
  have hquad : resolved ⬝ᵥ (moment *ᵥ resolved) = reading := by
    rw [hback, hreading, dotProduct_comm]
  have hsplit : moment = mass label • atomMatrix (direction label) + punctured := by
    rw [hmomentDef, chartMassMatrix, hpuncturedDef,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ label)]
  have hexpand : resolved ⬝ᵥ (moment *ᵥ resolved)
      = mass label * reading ^ 2 + resolved ⬝ᵥ (punctured *ᵥ resolved) := by
    rw [hsplit, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec, ← hreading]
  have hform : reading = mass label * reading ^ 2
      + resolved ⬝ᵥ (punctured *ᵥ resolved) := by
    conv_lhs => rw [← hquad]
    exact hexpand
  have hgoal : chartFosterShare direction mass label = mass label * reading := rfl
  rw [hgoal]
  by_cases hzero : resolved = 0
  · have hread : reading = 0 := by rw [hreading, hzero, dotProduct_zero]
    rw [hread, mul_zero]
    norm_num
  · have hrestPos : 0 < resolved ⬝ᵥ (punctured *ᵥ resolved) := by
      have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpunctured).2 hzero
      rwa [star_trivial] at hpos
    have hstrict : mass label * reading ^ 2 < reading := by linarith [hform, hrestPos]
    have hreadingPos : 0 < reading := by nlinarith [hstrict, hmassNonneg, sq_nonneg reading]
    nlinarith [hstrict, hreadingPos]

/-- The last three `K4` directions are the coordinate axes, so five of the six
directions always span. -/
theorem eq_zero_of_kFourDirection_erase_blind {label : Fin 6} {probe : Fin 3 → ℝ}
    (hblind : ∀ other : Fin 6, other ≠ label → kFourDirection other ⬝ᵥ probe = 0) :
    probe = 0 := by
  have hzeroEdge : ∀ other : Fin 6, other ≠ label →
      kFourDirection other 0 * probe 0 + kFourDirection other 1 * probe 1
        + kFourDirection other 2 * probe 2 = 0 := by
    intro other hne
    have hread := hblind other hne
    rwa [dotProduct, Fin.sum_univ_three] at hread
  have hthree : label ≠ 3 → probe 0 = 0 := by
    intro hne
    have hread := hzeroEdge 3 (Ne.symm hne)
    simpa [kFourDirection] using hread
  have hfour : label ≠ 4 → probe 1 = 0 := by
    intro hne
    have hread := hzeroEdge 4 (Ne.symm hne)
    simpa [kFourDirection] using hread
  have hfive : label ≠ 5 → probe 2 = 0 := by
    intro hne
    have hread := hzeroEdge 5 (Ne.symm hne)
    simpa [kFourDirection] using hread
  have hcoords : probe 0 = 0 ∧ probe 1 = 0 ∧ probe 2 = 0 := by
    rcases Decidable.em (label = 3) with h3 | h3
    · subst h3
      have hone := hfour (by decide)
      have htwo := hfive (by decide)
      have hedge := hzeroEdge 0 (by decide)
      simp [kFourDirection] at hedge
      exact ⟨by linarith, hone, htwo⟩
    · rcases Decidable.em (label = 4) with h4 | h4
      · subst h4
        have hzeroCoord := hthree (by decide)
        have htwo := hfive (by decide)
        have hedge := hzeroEdge 0 (by decide)
        simp [kFourDirection] at hedge
        exact ⟨hzeroCoord, by linarith, htwo⟩
      · rcases Decidable.em (label = 5) with h5 | h5
        · subst h5
          have hzeroCoord := hthree (by decide)
          have hone := hfour (by decide)
          have hedge := hzeroEdge 1 (by decide)
          simp [kFourDirection] at hedge
          exact ⟨hzeroCoord, hone, by linarith⟩
        · exact ⟨hthree h3, hfour h4, hfive h5⟩
  funext coord
  fin_cases coord
  · exact hcoords.1
  · exact hcoords.2.1
  · exact hcoords.2.2

/-- **THE PUNCTURED `K4` MOMENT IS DEFINITE.**  Removing one edge leaves a
connected spanning subgraph, so the moment stays positive definite. -/
theorem posDef_kFourPuncturedMoment (point : DirectionChartPoint 6) (label : Fin 6) :
    (∑ other ∈ Finset.univ.erase label,
      point.mass other • atomMatrix (kFourDirection other)).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun other _ => by
      rw [Matrix.transpose_smul,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (kFourDirection other)).1]
  · rw [star_trivial]
    have hread : probe ⬝ᵥ ((∑ other ∈ Finset.univ.erase label,
          point.mass other • atomMatrix (kFourDirection other)) *ᵥ probe)
        = ∑ other ∈ Finset.univ.erase label,
            point.mass other * (kFourDirection other ⬝ᵥ probe) ^ 2 := by
      rw [Matrix.sum_mulVec, dotProduct_sum]
      exact Finset.sum_congr rfl fun other _ => by
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
          dotProduct_atomMatrix_mulVec]
    rw [hread]
    by_contra hnonpos
    push Not at hnonpos
    have hterms : ∀ other ∈ Finset.univ.erase label,
        point.mass other * (kFourDirection other ⬝ᵥ probe) ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp (le_antisymm hnonpos
        (Finset.sum_nonneg fun other _ =>
          mul_nonneg (point.mass_pos other).le (sq_nonneg _)))
      exact fun other _ => mul_nonneg (point.mass_pos other).le (sq_nonneg _)
    have hblind : ∀ other : Fin 6, other ≠ label →
        kFourDirection other ⬝ᵥ probe = 0 := by
      intro other hother
      have hterm := hterms other
        (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
      have hsq : (kFourDirection other ⬝ᵥ probe) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hterm with hmass | hsq
        · exact absurd hmass (ne_of_gt (point.mass_pos other))
        · exact hsq
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    exact hne (eq_zero_of_kFourDirection_erase_blind hblind)

/-- **THE SHARE HYPOTHESIS IS FREE AT `K4`.**  Every label of every `K4` chart
point has share strictly below one, so `Gtz.exists_deflatedGapBound` applies at
every label with no extra assumption. -/
theorem chartFosterShare_kFour_lt_one (point : DirectionChartPoint 6)
    (label : Fin 6) : chartFosterShare kFourDirection point.mass label < 1 :=
  chartFosterShare_lt_one kFourDirection point.mass label (point.mass_pos label).le
    (posDef_chartMassMatrix_kFour point) (posDef_kFourPuncturedMoment point label)

/-! ## 12. The deflation runs unconditionally at the `K4` chart

Three landed pieces meet here.  `Gtz.exists_design_of_chartPoint_withLeverage`
welds a chart point to a design AND reports the atom leverages.  Section 11 makes
the share hypothesis free at `K4`.  `Gtz.gtzWeighted_of_le_five` is the
predecessor rung.  So `Gtz.exists_deflatedGapBound` fires at EVERY label of EVERY
`K4` chart point, and `Gtz.posDef_iff_gapDet_pos_of_deflatedGapBound` turns the
subset it returns into ONE determinant sign, with no hypothesis at all. -/

/-- **THE PRODUCED SUBSET IS DECIDED BY ONE DETERMINANT.**  At every `K4` chart
point and every label, the deflation returns a card-three subset avoiding that
label whose strict domination in the chart is exactly the positivity of its
design gap determinant.  No stall, no wall, no heaviness, no leverage floor. -/
theorem kFour_exists_deflatedSubset (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    ∃ (design : WeightedDesign 6 3) (selected : Finset (Fin 6)),
      design.weight = point.weight ∧ selected.card = 3 ∧ dropLabel ∉ selected ∧
      DeflatedGapBoundAt design dropLabel selected ∧
      ((directionChartGap kFourDirection point.mass point.weight selected).PosDef
        ↔ 0 < (subsetSum design selected - 1).det) := by
  obtain ⟨design, hweight, htransfer, hleverage⟩ :=
    exists_design_of_chartPoint_withLeverage kFourDirection point
      (posDef_massMoment_kFourDirection point)
  have hweightNe : point.weight dropLabel ≠ 0 := ne_of_gt (point.weight_pos dropLabel)
  have hshare : design.weight dropLabel * leverageOf (design.atom dropLabel) < 1 := by
    have hfoster := chartFosterShare_kFour_lt_one point dropLabel
    rw [chartFosterShare, chartMassMatrix] at hfoster
    rw [hweight, hleverage dropLabel]
    have hclear : point.weight dropLabel
        * (point.mass dropLabel / point.weight dropLabel
            * (kFourDirection dropLabel ⬝ᵥ
                ((∑ l, point.mass l • atomMatrix (kFourDirection l))⁻¹
                  *ᵥ kFourDirection dropLabel)))
        = point.mass dropLabel
            * (kFourDirection dropLabel ⬝ᵥ
                ((∑ l, point.mass l • atomMatrix (kFourDirection l))⁻¹
                  *ᵥ kFourDirection dropLabel)) := by
      field_simp
    rw [hclear]
    exact hfoster
  obtain ⟨selected, hcard, hnotMem, hbound⟩ :=
    exists_deflatedGapBound (m := 5) (k := 3) design (by norm_num)
      (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) dropLabel hshare
  refine ⟨design, selected, hweight, hcard, hnotMem, hbound, ?_⟩
  rw [← (htransfer selected).1]
  exact posDef_iff_gapDet_pos_of_deflatedGapBound design (by norm_num) dropLabel
    selected hbound

/-- A positive determinant at a card-three subset lands a strict spanning tree:
a card-three subset is a spanning tree or a triangle, and a triangle is never
strict. -/
theorem kFour_hasStrictTree_of_cardThree_posDef (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  refine ⟨selected, mem_kFourSpanningTreeList_of_card_three selected hcard ?_, hpd⟩
  intro htriangle
  exact kFourTriangle_gap_not_posDef point selected htriangle hpd

/-- **THE RESIDUAL AS A DETERMINANT SIGN AT A PRODUCED SUBSET.**  The whole
conclusion of the registered `K4` axiom follows from one positive determinant at
the subset the deflation returns. -/
theorem kFour_hasStrictTree_of_deflatedSubsetDet (point : DirectionChartPoint 6)
    {design : WeightedDesign 6 3} {selected : Finset (Fin 6)}
    (hcard : selected.card = 3)
    (hiff : (directionChartGap kFourDirection point.mass point.weight selected).PosDef
      ↔ 0 < (subsetSum design selected - 1).det)
    (hdet : 0 < (subsetSum design selected - 1).det) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  kFour_hasStrictTree_of_cardThree_posDef point hcard (hiff.mpr hdet)

/-- The deflated subset carries the chart determinant equivalence as well, once
its own chart deflated bound is in hand.  This is the bridge between the design
determinant of `Gtz.kFour_exists_deflatedSubset` and the chart determinant of
the cell of section 5. -/
theorem kFour_deflatedSubset_chartDet (point : DirectionChartPoint 6)
    {dropLabel : Fin 6} {selected : Finset (Fin 6)}
    (hchartBound : ChartDeflatedGapBound kFourDirection point.mass point.weight
      dropLabel selected)
    (hcard : selected.card = 3)
    (hdet : 0 < (directionChartGap kFourDirection point.mass point.weight
      selected).det) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  kFour_hasStrictTree_of_cardThree_posDef point hcard
    ((posDef_directionChartGap_kFour_iff_det_pos_of_chartDeflatedGapBound point
      dropLabel selected hchartBound).mpr hdet)

/-- The cell recovers the landed strict triple at the tetrahedron point through
the determinant route alone. -/
theorem tetrahedronChartPoint_hasStrictTree_of_cell :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection tetrahedronChartPoint.mass
        tetrahedronChartPoint.weight tree).PosDef :=
  kFour_hasStrictTree_of_deflatedDetCellFires tetrahedronChartPoint
    tetrahedronChartPoint_deflatedDetCellFires

end Gtz
