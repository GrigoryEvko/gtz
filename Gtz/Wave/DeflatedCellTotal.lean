/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.TriangleStallClosureDeflation
import Gtz.Design.StratumEmptinessLedger
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The produced subset of the deflation is a spanning tree

`Gtz.kFour_exists_deflatedSubset` returns a card-three subset at every `K4` chart
point and every label, and reads its strict domination as one determinant sign.
The subset itself is opaque there: nothing says it is a spanning tree, and the
determinant it names is the DESIGN determinant of a design that the statement
hides behind an existential.

This module closes both gaps.

## The punctured normal form

`Gtz.chartDeflatedForm_eq_puncturedForm` reads the chart deflated form a third
way, next to the two readings of `Gtz.TriangleStallClosureDeflation`:

  `(1 - w_d) * Sel(C)  -  (moment with the label `d` deleted)` .

The dropped label leaves the load ENTIRELY, and the selection keeps its own
conductance undiscounted.  No membership hypothesis appears.

The punctured moment is positive definite at every `K4` chart point, because
`K4` minus one edge still spans.  So the bound forces the SELECTED conductance
to be positive definite, and a positive definite conductance of a card-three
selection makes the three directions independent.  A dependent triple of `K4` is
a triangle, so `Gtz.kFour_mem_spanningTreeList_of_chartDeflatedGapBound` places
every card-three carrier of the bound in the sixteen-tree list.

`Gtz.kFourDeflatedDetCellFires_of_cardThree` is the consequence: the spanning
tree quantifier of the cell costs nothing.  Any card-three subset carrying the
bound with a positive gap determinant fires the cell.

## The whitening congruence, exported

`Gtz.exists_kFourWhitenedDesign` and `Gtz.exists_design_of_chartPoint_withLeverage`
both build a congruence matrix and both discard it.
`Gtz.exists_kFourChartCongruence` keeps it, together with the atom identity

  `atomMatrix (design.atom c) = (m_c / w_c) • (Rᵀ * atomMatrix (v_c) * R)` .

Those two identities congruate the design deflated form onto the chart deflated
form, so `Gtz.deflatedGapBoundAt_iff_chartDeflatedGapBound` is an equivalence and
not a transport in one direction.

## The chart deflation producer

`Gtz.kFour_exists_chartDeflatedTree` is the outcome.  At every `K4` chart point
and every label there is a SPANNING TREE avoiding that label which carries the
CHART deflated bound, and whose strict domination is the positivity of its own
CHART gap determinant.  Nothing in that statement mentions a design, a whitener
or a square root.  `Gtz.kFourDeflatedDetCellTotal_iff_cardThreeDet` then reads
the registered cell total as one determinant sign per chart point.

## Foster's law in the chart, and the light-label cell

`Gtz.sum_chartFosterShare_eq_three` is the chart reading of the resolvent trace:
the six shares of a `K4` chart point sum to the rank.  It is the exact chart
analogue of the landed `Gtz.sum_atomShare_eq_rank`.

The bound alone gives `gap >= (w_d * moment - m_d * atom_d) / (1 - w_d)`, so a
label whose share falls below its own weight makes the whole gap strict:
`Gtz.kFourDeflatedDetCellFires_of_share_lt_weight`.  That cell is inhabited (a
label of small mass has small share), but Foster's law forbids it at every label
at once, and in fact `Gtz.exists_three_mul_weight_le_chartFosterShare` names a
label whose share is at least three times its weight.  So this sufficient
condition is real and is far from total, which is the honest measure of what the
Loewner content of the deflation can and cannot buy.

## The sharp form, with no division

The punctured form gives a better floor than the moment comparison above, and
gives it for free:

  `gap  >=  w_d * Sel(C)  -  m_d * atom_d` .

The right side is a rank-one deflation of a matrix that the bound already makes
definite, so its definiteness is ONE scalar.
`Gtz.posDef_directionChartGap_of_selectedResolvent_price` reads that scalar as
the dropped label's reading of the SELECTED resolvent against its own weight.
The moment never appears and no factor `1 - w_d` is paid.  The two hypotheses
are not compared in kernel here.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The selected conductance and the punctured moment -/

/-- The selected conductance of a chart selection: the term the chart gap adds. -/
noncomputable def chartSelectedConductance (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label)

/-- The chart moment with one label deleted. -/
noncomputable def chartPuncturedMoment (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (dropLabel : Fin size) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ other ∈ Finset.univ.erase dropLabel, mass other • atomMatrix (direction other)

/-- The chart gap is the selected conductance minus the moment. -/
theorem directionChartGap_eq_selected_sub_moment (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    directionChartGap direction mass weight selected
      = chartSelectedConductance direction mass weight selected
        - chartMassMatrix direction mass := rfl

/-- The moment splits at any label into that label's atom and the punctured
moment. -/
theorem chartMassMatrix_eq_atom_add_punctured (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (dropLabel : Fin size) :
    chartMassMatrix direction mass
      = mass dropLabel • atomMatrix (direction dropLabel)
        + chartPuncturedMoment direction mass dropLabel := by
  classical
  rw [chartMassMatrix, chartPuncturedMoment,
    ← Finset.add_sum_erase _ (fun label => mass label • atomMatrix (direction label))
      (Finset.mem_univ dropLabel)]

/-- The quadratic form of the selected conductance at a probe. -/
theorem chartSelectedConductance_reading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (chartSelectedConductance direction mass weight selected *ᵥ probe)
      = ∑ label ∈ selected, mass label / weight label
          * (direction label ⬝ᵥ probe) ^ 2 := by
  rw [chartSelectedConductance, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- The selected conductance is symmetric. -/
theorem chartSelectedConductance_transpose (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    (chartSelectedConductance direction mass weight selected)ᵀ
      = chartSelectedConductance direction mass weight selected := by
  rw [chartSelectedConductance, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (direction label)).1]

/-- The punctured moment is symmetric. -/
theorem chartPuncturedMoment_transpose (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (dropLabel : Fin size) :
    (chartPuncturedMoment direction mass dropLabel)ᵀ
      = chartPuncturedMoment direction mass dropLabel := by
  classical
  rw [chartPuncturedMoment, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun other _ => by
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (direction other)).1]

/-! ## 2. The punctured normal form of the chart deflated bound

The landed complement form deletes the dropped label from both sides and
discounts every selected mass.  The form below deletes the dropped label from
the load ONLY, and discounts the whole selected conductance at one time.  It
needs no membership hypothesis, and its load side is a positive definite matrix
at every `K4` chart point. -/

/-- **THE PUNCTURED FORM.**  The chart deflated form is the discounted selected
conductance minus the moment of everything except the dropped label. -/
theorem chartDeflatedForm_eq_puncturedForm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {dropLabel : Fin size}
    (hweightNe : weight dropLabel ≠ 0) (selected : Finset (Fin size)) :
    chartDeflatedForm direction mass weight dropLabel selected
      = ((1 : ℝ) - weight dropLabel)
          • chartSelectedConductance direction mass weight selected
        - chartPuncturedMoment direction mass dropLabel := by
  have hcredit : weight dropLabel
      • ((mass dropLabel / weight dropLabel) • atomMatrix (direction dropLabel))
      = mass dropLabel • atomMatrix (direction dropLabel) := by
    rw [smul_smul, mul_div_cancel₀ _ hweightNe]
  rw [chartDeflatedForm, directionChartGap_eq_selected_sub_moment, smul_sub, smul_sub,
    hcredit, chartMassMatrix_eq_atom_add_punctured direction mass dropLabel]
  module

/-- The bound is exactly the discounted conductance dominating the punctured
moment. -/
theorem chartDeflatedGapBound_iff_punctured (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {dropLabel : Fin size}
    (hweightNe : weight dropLabel ≠ 0) (selected : Finset (Fin size)) :
    ChartDeflatedGapBound direction mass weight dropLabel selected
      ↔ (((1 : ℝ) - weight dropLabel)
          • chartSelectedConductance direction mass weight selected
        - chartPuncturedMoment direction mass dropLabel).PosSemidef := by
  rw [ChartDeflatedGapBound,
    chartDeflatedForm_eq_puncturedForm direction mass weight hweightNe selected]

/-- **THE SELECTED CONDUCTANCE IS DEFINITE.**  A positive definite punctured
moment upgrades the bound to strict positivity of the selection's own
conductance.  No card hypothesis, no spanning hypothesis, generic in the ambient
size. -/
theorem posDef_chartSelectedConductance_of_chartDeflatedGapBound
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {dropLabel : Fin size} {selected : Finset (Fin size)}
    (hweightPos : 0 < weight dropLabel) (hweightLt : weight dropLabel < 1)
    (hpunctured : (chartPuncturedMoment direction mass dropLabel).PosDef)
    (hbound : ChartDeflatedGapBound direction mass weight dropLabel selected) :
    (chartSelectedConductance direction mass weight selected).PosDef := by
  have hsurviving : (0 : ℝ) < 1 - weight dropLabel := by linarith
  have hbnd := (chartDeflatedGapBound_iff_punctured direction mass weight
    (ne_of_gt hweightPos) selected).mp hbound
  have hsplit : ((1 : ℝ) - weight dropLabel)
      • chartSelectedConductance direction mass weight selected
      = chartPuncturedMoment direction mass dropLabel
        + (((1 : ℝ) - weight dropLabel)
            • chartSelectedConductance direction mass weight selected
          - chartPuncturedMoment direction mass dropLabel) := by
    module
  have hscaled : (((1 : ℝ) - weight dropLabel)
      • chartSelectedConductance direction mass weight selected).PosDef := by
    rw [hsplit]
    exact hpunctured.add_posSemidef hbnd
  have hunscale : chartSelectedConductance direction mass weight selected
      = (((1 : ℝ) - weight dropLabel)⁻¹)
        • (((1 : ℝ) - weight dropLabel)
            • chartSelectedConductance direction mass weight selected) := by
    rw [smul_smul, inv_mul_cancel₀ hsurviving.ne', one_smul]
  rw [hunscale]
  exact hscaled.smul (inv_pos.mpr hsurviving)

/-! ## 3. The produced subset of a `K4` bound is a spanning tree

The punctured `K4` moment is positive definite at every chart point, so section
2 fires with no hypothesis.  A triangle reads zero at its own normal, so its
conductance is never definite, and the landed card-three dichotomy places the
selection on the tree list. -/

/-- The punctured `K4` moment is positive definite at every chart point. -/
theorem posDef_chartPuncturedMoment_kFour (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    (chartPuncturedMoment kFourDirection point.mass dropLabel).PosDef :=
  posDef_kFourPuncturedMoment point dropLabel

/-- **THE `K4` SELECTED CONDUCTANCE IS DEFINITE.**  Unconditional at every chart
point, every label and every selection carrying the bound. -/
theorem posDef_chartSelectedConductance_kFour (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) {selected : Finset (Fin 6)}
    (hbound : ChartDeflatedGapBound kFourDirection point.mass point.weight
      dropLabel selected) :
    (chartSelectedConductance kFourDirection point.mass point.weight selected).PosDef :=
  posDef_chartSelectedConductance_of_chartDeflatedGapBound kFourDirection point.mass
    point.weight (point.weight_pos dropLabel) (chartPoint_weight_lt_one point dropLabel)
    (posDef_chartPuncturedMoment_kFour point dropLabel) hbound

/-- A triangle never has a definite conductance: its normal reads zero on every
edge of the triangle. -/
theorem not_posDef_chartSelectedConductance_kFourTriangle (point : DirectionChartPoint 6)
    {triangle : Finset (Fin 6)} (htri : IsKFourTriangle triangle) :
    ¬ (chartSelectedConductance kFourDirection point.mass point.weight triangle).PosDef := by
  intro hpd
  have hread := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2
    (kFourTriangleNormal_ne_zero htri)
  rw [star_trivial, chartSelectedConductance_reading] at hread
  have hzero : ∑ label ∈ triangle, point.mass label / point.weight label
      * (kFourDirection label ⬝ᵥ kFourTriangleNormal triangle) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hmem => by
      rw [kFourDirection_dot_triangleNormal htri hmem]; ring
  rw [hzero] at hread
  exact lt_irrefl 0 hread

/-- **THE CARRIER OF THE BOUND IS A SPANNING TREE.**  Any card-three selection
carrying the chart deflated bound at ANY label lies on the sixteen-tree list.
The selection is not chosen here: whatever produces it, the bound alone forces
independence. -/
theorem kFour_mem_spanningTreeList_of_chartDeflatedGapBound (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hbound : ChartDeflatedGapBound kFourDirection point.mass point.weight
      dropLabel selected) :
    selected ∈ kFourSpanningTreeList := by
  refine mem_kFourSpanningTreeList_of_card_three selected hcard ?_
  intro htri
  exact not_posDef_chartSelectedConductance_kFourTriangle point
    (show IsKFourTriangle selected from htri)
    (posDef_chartSelectedConductance_kFour point dropLabel hbound)

/-- **THE TREE QUANTIFIER OF THE CELL IS FREE.**  A card-three selection carrying
the bound with a positive gap determinant fires the deflated determinant cell.
The cell's membership clause never has to be checked. -/
theorem kFourDeflatedDetCellFires_of_cardThree (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hbound : ChartDeflatedGapBound kFourDirection point.mass point.weight
      dropLabel selected)
    (hdet : 0 < (directionChartGap kFourDirection point.mass point.weight selected).det) :
    KFourDeflatedDetCellFires point :=
  ⟨dropLabel, selected,
    kFour_mem_spanningTreeList_of_chartDeflatedGapBound point dropLabel hcard hbound,
    hbound, hdet⟩

/-- Every listed spanning tree has three labels. -/
theorem card_eq_three_of_mem_kFourSpanningTreeList {tree : Finset (Fin 6)}
    (hmem : tree ∈ kFourSpanningTreeList) : tree.card = 3 := by
  revert hmem
  revert tree
  decide

/-- **THE CELL TOTAL IS ONE DETERMINANT SIGN PER CHART POINT.**  The registered
total is equivalent to the existence, at every chart point, of one label and one
card-three carrier of the bound with a positive determinant. -/
theorem kFourDeflatedDetCellTotal_iff_cardThreeDet :
    KFourDeflatedDetCellTotal
      ↔ ∀ point : DirectionChartPoint 6,
          ∃ (dropLabel : Fin 6) (selected : Finset (Fin 6)), selected.card = 3 ∧
            ChartDeflatedGapBound kFourDirection point.mass point.weight
              dropLabel selected ∧
            0 < (directionChartGap kFourDirection point.mass point.weight selected).det := by
  constructor
  · intro htotal point
    obtain ⟨dropLabel, tree, hmem, hbound, hdet⟩ := htotal point
    exact ⟨dropLabel, tree, card_eq_three_of_mem_kFourSpanningTreeList hmem, hbound, hdet⟩
  · intro hcard point
    obtain ⟨dropLabel, selected, hthree, hbound, hdet⟩ := hcard point
    exact kFourDeflatedDetCellFires_of_cardThree point dropLabel hthree hbound hdet

/-! ## 4. The design side twin

The design deflated bound forces the design subset sum to be positive definite,
by exactly the argument of section 2 with the pivot `1 - w_d g_d g_d^T` in place
of the punctured moment.  The converse of the landed pivot criterion reads the
share back off that pivot. -/

/-- **THE DESIGN SUBSET SUM IS DEFINITE.**  The deflated gap bound at a label
whose share is below one makes the selected atoms of the design span. -/
theorem posDef_subsetSum_of_deflatedGapBound {rank : ℕ} {atoms : ℕ}
    (design : WeightedDesign atoms rank) (dropLabel : Fin atoms)
    (selected : Finset (Fin atoms)) (hweightLt : design.weight dropLabel < 1)
    (hshare : design.weight dropLabel * leverageOf (design.atom dropLabel) < 1)
    (hbound : DeflatedGapBoundAt design dropLabel selected) :
    (subsetSum design selected).PosDef := by
  have hweightPos := design.weight_pos dropLabel
  have hsurviving : (0 : ℝ) < 1 - design.weight dropLabel := by linarith
  have hpivot : ((1 : Matrix (Fin rank) (Fin rank) ℝ)
      - design.weight dropLabel • atomMatrix (design.atom dropLabel)).PosDef :=
    posDef_one_sub_smul_atomMatrix_of_share_lt_one hweightPos hshare
  have hsplit : ((1 : ℝ) - design.weight dropLabel) • subsetSum design selected
      = ((1 : Matrix (Fin rank) (Fin rank) ℝ)
          - design.weight dropLabel • atomMatrix (design.atom dropLabel))
        + (((1 : ℝ) - design.weight dropLabel) • (subsetSum design selected - 1)
          - design.weight dropLabel • (1 - atomMatrix (design.atom dropLabel))) := by
    module
  have hscaled : (((1 : ℝ) - design.weight dropLabel)
      • subsetSum design selected).PosDef := by
    rw [hsplit]
    exact hpivot.add_posSemidef hbound
  have hunscale : subsetSum design selected
      = (((1 : ℝ) - design.weight dropLabel)⁻¹)
        • (((1 : ℝ) - design.weight dropLabel) • subsetSum design selected) := by
    rw [smul_smul, inv_mul_cancel₀ hsurviving.ne', one_smul]
  rw [hunscale]
  exact hscaled.smul (inv_pos.mpr hsurviving)

/-- **THE PIVOT READS THE SHARE BACK.**  The converse of
`Gtz.posDef_one_sub_smul_atomMatrix_of_share_lt_one`, with no positivity
hypothesis on the weight and no heaviness hypothesis on the atom. -/
theorem share_lt_one_of_posDef_one_sub_smul_atomMatrix {rank : ℕ} {weightValue : ℝ}
    {atomVector : Fin rank → ℝ}
    (hpd : ((1 : Matrix (Fin rank) (Fin rank) ℝ)
      - weightValue • atomMatrix atomVector).PosDef) :
    weightValue * leverageOf atomVector < 1 := by
  by_cases hzero : atomVector = 0
  · rw [hzero, leverageOf]
    simp
  · have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hzero
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec,
      ← leverageOf_eq_dotProduct] at hform
    have hlev : 0 < leverageOf atomVector := by
      rw [leverageOf_eq_dotProduct]
      exact dotProduct_self_pos hzero
    nlinarith [hform, hlev]

/-! ## 5. The whitening congruence, exported

`Gtz.exists_kFourWhitenedDesign` builds the congruence matrix and the gap
identity and then discards both.  The producer below keeps them, and adds the
atom identity, which is what carries the deflated form across. -/

/-- **THE WHITENING WITH ITS CONGRUENCE.**  Every `K4` chart point welds to a
design together with the matrix that congruates the chart onto it, the moment
identity, the atom identity and the gap identity. -/
theorem exists_kFourChartCongruence (point : DirectionChartPoint 6) :
    ∃ (design : WeightedDesign 6 3) (whitener : Matrix (Fin 3) (Fin 3) ℝ),
      design.weight = point.weight ∧ IsUnit whitener.det ∧
      whitenerᵀ * chartMassMatrix kFourDirection point.mass * whitener = 1 ∧
      (∀ label : Fin 6, atomMatrix (design.atom label)
        = (point.mass label / point.weight label)
            • (whitenerᵀ * atomMatrix (kFourDirection label) * whitener)) ∧
      (∀ selected : Finset (Fin 6), subsetSum design selected - 1
        = whitenerᵀ
            * directionChartGap kFourDirection point.mass point.weight selected
            * whitener) := by
  obtain ⟨whitener, hunit, hone⟩ := exists_congruence_to_one (kFourMomentMatrix_posDef point)
  set scaleOf : Fin 6 → ℝ :=
    fun label => Real.sqrt (point.mass label / point.weight label) with hscaleOf
  have hscaleSq : ∀ label, scaleOf label ^ 2 = point.mass label / point.weight label :=
    fun label => Real.sq_sqrt
      (div_nonneg (point.mass_pos label).le (point.weight_pos label).le)
  have hatomEq : ∀ label,
      atomMatrix (whitenerᵀ *ᵥ (scaleOf label • kFourDirection label))
        = (point.mass label / point.weight label)
            • (whitenerᵀ * atomMatrix (kFourDirection label) * whitener) := by
    intro label
    rw [atomMatrix_transpose_mulVec, atomMatrix_smul, ← hscaleSq label,
      Matrix.mul_smul, Matrix.smul_mul]
  have hsubsetEq : ∀ selected : Finset (Fin 6),
      (∑ label ∈ selected,
          atomMatrix (whitenerᵀ *ᵥ (scaleOf label • kFourDirection label)))
        = whitenerᵀ * (∑ label ∈ selected,
            (point.mass label / point.weight label)
              • atomMatrix (kFourDirection label)) * whitener := by
    intro selected
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun label _ => by
      rw [hatomEq label, Matrix.mul_smul, Matrix.smul_mul]
  have hparseval : (∑ label, point.weight label
      • atomMatrix (whitenerᵀ *ᵥ (scaleOf label • kFourDirection label))) = 1 := by
    have hmassEq : ∀ label,
        point.weight label
            • atomMatrix (whitenerᵀ *ᵥ (scaleOf label • kFourDirection label))
          = point.mass label
              • (whitenerᵀ * atomMatrix (kFourDirection label) * whitener) := by
      intro label
      rw [hatomEq label, smul_smul, mul_div_cancel₀ _ (point.weight_pos label).ne']
    calc (∑ label, point.weight label
          • atomMatrix (whitenerᵀ *ᵥ (scaleOf label • kFourDirection label)))
        = ∑ label, point.mass label
            • (whitenerᵀ * atomMatrix (kFourDirection label) * whitener) :=
          Finset.sum_congr rfl fun label _ => hmassEq label
      _ = whitenerᵀ * chartMassMatrix kFourDirection point.mass * whitener := by
          rw [chartMassMatrix, Matrix.mul_sum, Matrix.sum_mul]
          exact Finset.sum_congr rfl fun label _ => by
            rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = 1 := hone
  refine ⟨⟨fun label => whitenerᵀ *ᵥ (scaleOf label • kFourDirection label),
    point.weight, point.weight_pos, point.weight_sum_one, hparseval⟩, whitener,
    rfl, hunit, hone, hatomEq, ?_⟩
  intro selected
  show (∑ label ∈ selected,
      atomMatrix (whitenerᵀ *ᵥ (scaleOf label • kFourDirection label))) - 1
    = whitenerᵀ * directionChartGap kFourDirection point.mass point.weight selected
        * whitener
  rw [hsubsetEq selected, ← hone, directionChartGap, Matrix.mul_sub, Matrix.sub_mul]
  rfl

/-- Congruating a difference of two scaled matrices. -/
theorem congr_smul_sub_smul (whitener leftMatrix rightMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (leftScalar rightScalar : ℝ) :
    whitenerᵀ * (leftScalar • leftMatrix - rightScalar • rightMatrix) * whitener
      = leftScalar • (whitenerᵀ * leftMatrix * whitener)
        - rightScalar • (whitenerᵀ * rightMatrix * whitener) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-! ## 6. The design deflated form is the chart deflated form, congruated -/

/-- **THE DEFLATED CONGRUENCE.**  The design deflated form of a welded design is
the chart deflated form conjugated by the whitener.  Both the mass moment and the
dropped atom travel, which is why the atom identity is necessary. -/
theorem deflatedForm_eq_congr_chartDeflatedForm (point : DirectionChartPoint 6)
    (design : WeightedDesign 6 3) (whitener : Matrix (Fin 3) (Fin 3) ℝ)
    (hweight : design.weight = point.weight)
    (hone : whitenerᵀ * chartMassMatrix kFourDirection point.mass * whitener = 1)
    (hatom : ∀ label : Fin 6, atomMatrix (design.atom label)
      = (point.mass label / point.weight label)
          • (whitenerᵀ * atomMatrix (kFourDirection label) * whitener))
    (hgap : ∀ selected : Finset (Fin 6), subsetSum design selected - 1
      = whitenerᵀ
          * directionChartGap kFourDirection point.mass point.weight selected * whitener)
    (dropLabel : Fin 6) (selected : Finset (Fin 6)) :
    ((1 : ℝ) - design.weight dropLabel) • (subsetSum design selected - 1)
        - design.weight dropLabel • (1 - atomMatrix (design.atom dropLabel))
      = whitenerᵀ
          * chartDeflatedForm kFourDirection point.mass point.weight dropLabel selected
          * whitener := by
  have hinner : whitenerᵀ * (chartMassMatrix kFourDirection point.mass
        - (point.mass dropLabel / point.weight dropLabel)
            • atomMatrix (kFourDirection dropLabel)) * whitener
      = 1 - atomMatrix (design.atom dropLabel) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hone, Matrix.mul_smul, Matrix.smul_mul,
      hatom dropLabel]
  rw [chartDeflatedForm, congr_smul_sub_smul, ← hgap selected, hinner, hweight]

/-- **THE TWO BOUNDS ARE THE SAME BOUND.**  An equivalence, not a transport. -/
theorem deflatedGapBoundAt_iff_chartDeflatedGapBound (point : DirectionChartPoint 6)
    (design : WeightedDesign 6 3) (whitener : Matrix (Fin 3) (Fin 3) ℝ)
    (hweight : design.weight = point.weight) (hunit : IsUnit whitener.det)
    (hone : whitenerᵀ * chartMassMatrix kFourDirection point.mass * whitener = 1)
    (hatom : ∀ label : Fin 6, atomMatrix (design.atom label)
      = (point.mass label / point.weight label)
          • (whitenerᵀ * atomMatrix (kFourDirection label) * whitener))
    (hgap : ∀ selected : Finset (Fin 6), subsetSum design selected - 1
      = whitenerᵀ
          * directionChartGap kFourDirection point.mass point.weight selected * whitener)
    (dropLabel : Fin 6) (selected : Finset (Fin 6)) :
    DeflatedGapBoundAt design dropLabel selected
      ↔ ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel selected := by
  rw [DeflatedGapBoundAt, ChartDeflatedGapBound,
    deflatedForm_eq_congr_chartDeflatedForm point design whitener hweight hone hatom hgap
      dropLabel selected]
  exact (posSemidef_congr_right
    (chartDeflatedForm_transpose kFourDirection point.mass point.weight dropLabel selected)
    hunit).symm

/-- The dropped atom's pivot in the welded design is the punctured chart moment,
congruated.  This is what makes the share hypothesis of the landed deflation
producer free without a leverage computation. -/
theorem one_sub_smul_atomMatrix_eq_congr_punctured (point : DirectionChartPoint 6)
    (design : WeightedDesign 6 3) (whitener : Matrix (Fin 3) (Fin 3) ℝ)
    (hweight : design.weight = point.weight)
    (hone : whitenerᵀ * chartMassMatrix kFourDirection point.mass * whitener = 1)
    (hatom : ∀ label : Fin 6, atomMatrix (design.atom label)
      = (point.mass label / point.weight label)
          • (whitenerᵀ * atomMatrix (kFourDirection label) * whitener))
    (dropLabel : Fin 6) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - design.weight dropLabel • atomMatrix (design.atom dropLabel)
      = whitenerᵀ * chartPuncturedMoment kFourDirection point.mass dropLabel * whitener := by
  have hcredit : point.weight dropLabel
      • ((point.mass dropLabel / point.weight dropLabel)
        • (whitenerᵀ * atomMatrix (kFourDirection dropLabel) * whitener))
      = point.mass dropLabel
        • (whitenerᵀ * atomMatrix (kFourDirection dropLabel) * whitener) := by
    rw [smul_smul, mul_div_cancel₀ _ (point.weight_pos dropLabel).ne']
  have hpunctured : chartPuncturedMoment kFourDirection point.mass dropLabel
      = chartMassMatrix kFourDirection point.mass
        - point.mass dropLabel • atomMatrix (kFourDirection dropLabel) := by
    rw [chartMassMatrix_eq_atom_add_punctured kFourDirection point.mass dropLabel]
    abel
  rw [hpunctured, Matrix.mul_sub, Matrix.sub_mul, hone, Matrix.mul_smul, Matrix.smul_mul,
    hweight, hatom dropLabel, hcredit]

/-! ## 7. The chart deflation producer

Everything above meets here.  The welded design of section 5 carries the share
hypothesis for free through section 6, the landed deflation producer returns a
card-three subset, section 6 sends its bound to the chart, and section 3 places
the subset on the tree list. -/

/-- **THE PRODUCED SUBSET IS A SPANNING TREE, IN THE CHART.**  At every `K4`
chart point and every label the deflation returns a SPANNING TREE avoiding that
label which carries the CHART deflated bound, and whose strict domination is
exactly the positivity of its CHART gap determinant.  No design, no whitener and
no square root survive in the statement. -/
theorem kFour_exists_chartDeflatedTree (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree ∧
      ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel tree ∧
      ((directionChartGap kFourDirection point.mass point.weight tree).PosDef
        ↔ 0 < (directionChartGap kFourDirection point.mass point.weight tree).det) := by
  obtain ⟨design, whitener, hweight, hunit, hone, hatom, hgap⟩ :=
    exists_kFourChartCongruence point
  have hpivot : ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - design.weight dropLabel • atomMatrix (design.atom dropLabel)).PosDef := by
    rw [one_sub_smul_atomMatrix_eq_congr_punctured point design whitener hweight hone
      hatom dropLabel]
    exact (posDef_congr_right
      (chartPuncturedMoment_transpose kFourDirection point.mass dropLabel) hunit).mp
      (posDef_chartPuncturedMoment_kFour point dropLabel)
  have hshare : design.weight dropLabel * leverageOf (design.atom dropLabel) < 1 :=
    share_lt_one_of_posDef_one_sub_smul_atomMatrix hpivot
  obtain ⟨selected, hcard, hnotMem, hbound⟩ :=
    exists_deflatedGapBound (m := 5) (k := 3) design (by norm_num)
      (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) dropLabel hshare
  have hchart : ChartDeflatedGapBound kFourDirection point.mass point.weight
      dropLabel selected :=
    (deflatedGapBoundAt_iff_chartDeflatedGapBound point design whitener hweight hunit
      hone hatom hgap dropLabel selected).mp hbound
  refine ⟨selected,
    kFour_mem_spanningTreeList_of_chartDeflatedGapBound point dropLabel hcard hchart,
    hnotMem, hchart, ?_⟩
  exact posDef_directionChartGap_kFour_iff_det_pos_of_chartDeflatedGapBound point
    dropLabel selected hchart

/-- **THE RESIDUAL OF THE CELL, AT PRODUCED TREES.**  The cell fires at a chart
point as soon as ONE of the six produced trees has a positive gap determinant. -/
theorem kFourDeflatedDetCellFires_of_producedTreeDet (point : DirectionChartPoint 6)
    (dropLabel : Fin 6)
    (hdet : ∀ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree →
      ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel tree →
      0 < (directionChartGap kFourDirection point.mass point.weight tree).det) :
    KFourDeflatedDetCellFires point := by
  obtain ⟨tree, hmem, hnotMem, hbound, _⟩ := kFour_exists_chartDeflatedTree point dropLabel
  exact ⟨dropLabel, tree, hmem, hbound, hdet tree hmem hnotMem hbound⟩

/-! ## 8. Foster's law in the chart

The design side has `Gtz.sum_atomShare_eq_rank`.  The chart side has no such law.
The proof is the resolvent trace: the moment resolvent against the moment is the
identity, whose trace is the rank. -/

/-- **FOSTER'S LAW IN THE CHART.**  The chart shares of a chart point with a
definite moment sum to the rank.  Generic in the ambient size, with no
positivity hypothesis on the masses. -/
theorem sum_chartFosterShare_eq_three (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (hmoment : (chartMassMatrix direction mass).PosDef) :
    ∑ label, chartFosterShare direction mass label = 3 := by
  have hunit : IsUnit (chartMassMatrix direction mass).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hmoment.det_pos)
  have hterm : ∀ label : Fin size, chartFosterShare direction mass label
      = Matrix.trace ((chartMassMatrix direction mass)⁻¹
          * (mass label • atomMatrix (direction label))) := by
    intro label
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul,
      chartFosterShare]
  calc ∑ label, chartFosterShare direction mass label
      = ∑ label, Matrix.trace ((chartMassMatrix direction mass)⁻¹
          * (mass label • atomMatrix (direction label))) :=
        Finset.sum_congr rfl fun label _ => hterm label
    _ = Matrix.trace ((chartMassMatrix direction mass)⁻¹
          * ∑ label, mass label • atomMatrix (direction label)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = Matrix.trace ((chartMassMatrix direction mass)⁻¹
          * chartMassMatrix direction mass) := by rw [chartMassMatrix]
    _ = 3 := by
        rw [Matrix.nonsing_inv_mul _ hunit, Matrix.trace_one]
        norm_num

/-- **A LABEL CARRIES AT LEAST THREE TIMES ITS WEIGHT IN SHARE.**  Foster's law
against the weight normalisation.  There is no chart point whose every share
falls below three times the label's weight. -/
theorem exists_three_mul_weight_le_chartFosterShare (point : DirectionChartPoint 6) :
    ∃ label : Fin 6,
      3 * point.weight label ≤ chartFosterShare kFourDirection point.mass label := by
  by_contra hall
  push Not at hall
  have hsum : ∑ label, chartFosterShare kFourDirection point.mass label
      < ∑ label : Fin 6, 3 * point.weight label :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun label _ => hall label
  rw [sum_chartFosterShare_eq_three kFourDirection point.mass
    (posDef_chartMassMatrix_kFour point), ← Finset.mul_sum, point.weight_sum_one] at hsum
  norm_num at hsum

/-- Foster's law forbids the light-label condition at every label at once. -/
theorem not_forall_chartFosterShare_lt_weight (point : DirectionChartPoint 6) :
    ¬ ∀ label : Fin 6,
        chartFosterShare kFourDirection point.mass label < point.weight label := by
  intro hall
  obtain ⟨label, hheavy⟩ := exists_three_mul_weight_le_chartFosterShare point
  have hlight := hall label
  have hweight := point.weight_pos label
  linarith

/-! ## 9. The light-label cell

The bound gives `gap >= (w_d * moment - m_d * atom_d) / (1 - w_d)`.  The right
side is positive definite exactly when the dropped label's share falls below its
own weight, and then the produced tree is strict outright. -/

/-- **THE RESOLVENT PRICE OF A LABEL AGAINST THE MOMENT.**  Cauchy-Schwarz
through the moment resolvent.  Division free, no membership hypothesis. -/
theorem mass_mul_reading_sq_le_chartFosterShare_mul (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (label : Fin size) (hmassNonneg : 0 ≤ mass label)
    (hmoment : (chartMassMatrix direction mass).PosDef) (probe : Fin 3 → ℝ) :
    mass label * (direction label ⬝ᵥ probe) ^ 2
      ≤ chartFosterShare direction mass label
        * (probe ⬝ᵥ (chartMassMatrix direction mass *ᵥ probe)) := by
  set moment := chartMassMatrix direction mass with hmomentDef
  have hunit : IsUnit moment.det := isUnit_iff_ne_zero.mpr (ne_of_gt hmoment.det_pos)
  set resolved := moment⁻¹ *ᵥ direction label with hresolved
  have hback : moment *ᵥ resolved = direction label := by
    rw [hresolved, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hsymm : momentᵀ = moment := chartMassMatrix_transpose direction mass
  have hpivot : resolved ⬝ᵥ (moment *ᵥ resolved)
      = direction label ⬝ᵥ (moment⁻¹ *ᵥ direction label) := by
    rw [hback, hresolved, dotProduct_comm]
  have hcross : resolved ⬝ᵥ (moment *ᵥ probe) = direction label ⬝ᵥ probe := by
    rw [← dotProduct_mulVec_transpose moment resolved probe, hsymm, hback, dotProduct_comm]
  by_cases hzero : probe = 0
  · subst hzero
    simp
  · have hprobePos : 0 < probe ⬝ᵥ (moment *ᵥ probe) := by
      have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hzero
      rwa [star_trivial] at hform
    have hcs := quadForm_cross_sq_le hmoment.posSemidef resolved probe hprobePos
    rw [hcross, hpivot] at hcs
    have hexpand : chartFosterShare direction mass label
        = mass label * (direction label ⬝ᵥ (moment⁻¹ *ᵥ direction label)) := rfl
    rw [hexpand]
    nlinarith [hcs, hmassNonneg]

/-- **THE LIGHT LABEL BEATS THE MOMENT.**  A share strictly below the weight
makes the weighted moment strictly dominate the label's own atom. -/
theorem posDef_weight_smul_moment_sub_atom_of_share_lt_weight
    (direction : Fin size → (Fin 3 → ℝ)) (mass : Fin size → ℝ) (weightValue : ℝ)
    (label : Fin size) (hmassNonneg : 0 ≤ mass label)
    (hmoment : (chartMassMatrix direction mass).PosDef)
    (hlight : chartFosterShare direction mass label < weightValue) :
    (weightValue • chartMassMatrix direction mass
      - mass label • atomMatrix (direction label)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun probe hne => ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul,
      chartMassMatrix_transpose,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (direction label)).1]
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_atomMatrix_mulVec]
    have hcs := mass_mul_reading_sq_le_chartFosterShare_mul direction mass label
      hmassNonneg hmoment probe
    have hpos : 0 < probe ⬝ᵥ (chartMassMatrix direction mass *ᵥ probe) := by
      have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hne
      rwa [star_trivial] at hform
    nlinarith [hcs, hpos]

/-- **THE LIGHT LABEL MAKES THE BOUND STRICT.**  Any selection carrying the chart
deflated bound at a label whose share is below its weight dominates strictly.
The selection is arbitrary: no card, no spanning and no membership hypothesis. -/
theorem posDef_directionChartGap_of_share_lt_weight (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {dropLabel : Fin size} {selected : Finset (Fin size)}
    (hmassNonneg : 0 ≤ mass dropLabel) (hweightPos : 0 < weight dropLabel)
    (hweightLt : weight dropLabel < 1)
    (hmoment : (chartMassMatrix direction mass).PosDef)
    (hlight : chartFosterShare direction mass dropLabel < weight dropLabel)
    (hbound : ChartDeflatedGapBound direction mass weight dropLabel selected) :
    (directionChartGap direction mass weight selected).PosDef := by
  have hsurviving : (0 : ℝ) < 1 - weight dropLabel := by linarith
  have hcredit : weight dropLabel
      • ((mass dropLabel / weight dropLabel) • atomMatrix (direction dropLabel))
      = mass dropLabel • atomMatrix (direction dropLabel) := by
    rw [smul_smul, mul_div_cancel₀ _ (ne_of_gt hweightPos)]
  have hstrict : (weight dropLabel • chartMassMatrix direction mass
      - mass dropLabel • atomMatrix (direction dropLabel)).PosDef :=
    posDef_weight_smul_moment_sub_atom_of_share_lt_weight direction mass
      (weight dropLabel) dropLabel hmassNonneg hmoment hlight
  have hsplit : ((1 : ℝ) - weight dropLabel)
      • directionChartGap direction mass weight selected
      = (weight dropLabel • chartMassMatrix direction mass
          - mass dropLabel • atomMatrix (direction dropLabel))
        + chartDeflatedForm direction mass weight dropLabel selected := by
    rw [chartDeflatedForm, smul_sub, hcredit]
    abel
  have hscaled : (((1 : ℝ) - weight dropLabel)
      • directionChartGap direction mass weight selected).PosDef := by
    rw [hsplit]
    exact hstrict.add_posSemidef hbound
  have hunscale : directionChartGap direction mass weight selected
      = (((1 : ℝ) - weight dropLabel)⁻¹)
        • (((1 : ℝ) - weight dropLabel)
            • directionChartGap direction mass weight selected) := by
    rw [smul_smul, inv_mul_cancel₀ hsurviving.ne', one_smul]
  rw [hunscale]
  exact hscaled.smul (inv_pos.mpr hsurviving)

/-- **THE LIGHT-LABEL CELL.**  A `K4` chart point with one label whose share is
below its weight fires the deflated determinant cell.  No other hypothesis. -/
theorem kFourDeflatedDetCellFires_of_share_lt_weight (point : DirectionChartPoint 6)
    (dropLabel : Fin 6)
    (hlight : chartFosterShare kFourDirection point.mass dropLabel
      < point.weight dropLabel) :
    KFourDeflatedDetCellFires point := by
  obtain ⟨tree, hmem, _, hbound, _⟩ := kFour_exists_chartDeflatedTree point dropLabel
  have hpd : (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
    posDef_directionChartGap_of_share_lt_weight kFourDirection point.mass point.weight
      (point.mass_pos dropLabel).le (point.weight_pos dropLabel)
      (chartPoint_weight_lt_one point dropLabel) (posDef_chartMassMatrix_kFour point)
      hlight hbound
  exact ⟨dropLabel, tree, hmem, hbound, hpd.det_pos⟩

/-- The strict tree of the light-label cell, in the form the registry consumes. -/
theorem kFour_hasStrictTree_of_share_lt_weight (point : DirectionChartPoint 6)
    (dropLabel : Fin 6)
    (hlight : chartFosterShare kFourDirection point.mass dropLabel
      < point.weight dropLabel) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  kFour_hasStrictTree_of_deflatedDetCellFires point
    (kFourDeflatedDetCellFires_of_share_lt_weight point dropLabel hlight)

/-! ## 10. The light-label cell is inhabited

Uniform weights and one label of mass one tenth against five labels of mass one.
The moment resolvent of that label is an explicit rational multiple of its own
direction, so the share is `1/11` and the weight is `1/6`. -/

/-- A chart point with uniform weights and one light label. -/
noncomputable def lightLabelChartPoint : DirectionChartPoint 6 where
  mass := ![1/10, 1, 1, 1, 1, 1]
  weight := fun _ => 1/6
  mass_pos := fun label => by fin_cases label <;> norm_num
  weight_pos := fun _ => by norm_num
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num

theorem lightLabelChartPoint_mass_zero : lightLabelChartPoint.mass 0 = 1/10 := rfl

theorem lightLabelChartPoint_weight_zero : lightLabelChartPoint.weight 0 = 1/6 := rfl

/-- The moment of the light-label point, in closed form. -/
theorem lightLabelChartPoint_moment_eq :
    chartMassMatrix kFourDirection lightLabelChartPoint.mass
      = Matrix.of ![![21/10, -1/10, -1], ![-1/10, 21/10, -1], ![-1, -1, 3]] := by
  rw [chartMassMatrix, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [lightLabelChartPoint, kFourDirection, atomMatrix, Matrix.add_apply] <;>
    norm_num

/-- The moment resolvent of the light label is a rational multiple of its own
direction. -/
theorem lightLabelChartPoint_resolvent :
    (chartMassMatrix kFourDirection lightLabelChartPoint.mass)⁻¹ *ᵥ kFourDirection 0
      = ![5/11, -5/11, 0] := by
  have hunit : IsUnit (chartMassMatrix kFourDirection lightLabelChartPoint.mass).det :=
    isUnit_iff_ne_zero.mpr
      (ne_of_gt (posDef_chartMassMatrix_kFour lightLabelChartPoint).det_pos)
  have hsolve : chartMassMatrix kFourDirection lightLabelChartPoint.mass
      *ᵥ ![5/11, -5/11, 0] = kFourDirection 0 := by
    rw [lightLabelChartPoint_moment_eq]
    ext coord
    fin_cases coord <;>
      simp [kFourDirection, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  rw [← hsolve, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]

/-- The share of the light label is `1/11`. -/
theorem lightLabelChartPoint_share_eq :
    chartFosterShare kFourDirection lightLabelChartPoint.mass 0 = 1/11 := by
  rw [chartFosterShare, lightLabelChartPoint_resolvent, lightLabelChartPoint_mass_zero,
    kFourDirection_zero]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- **THE LIGHT-LABEL CELL IS NOT VACUOUS.**  The share `1/11` falls strictly
below the weight `1/6`. -/
theorem lightLabelChartPoint_share_lt_weight :
    chartFosterShare kFourDirection lightLabelChartPoint.mass 0
      < lightLabelChartPoint.weight 0 := by
  rw [lightLabelChartPoint_share_eq, lightLabelChartPoint_weight_zero]
  norm_num

/-- The light-label point fires the deflated determinant cell, with no
determinant computation anywhere in the proof. -/
theorem lightLabelChartPoint_deflatedDetCellFires :
    KFourDeflatedDetCellFires lightLabelChartPoint :=
  kFourDeflatedDetCellFires_of_share_lt_weight lightLabelChartPoint 0
    lightLabelChartPoint_share_lt_weight

/-! ## 11. The gap dominates the selected conductance, with no division

Section 9 prices the gap against the MOMENT and pays a factor `1 - w_d` for it.
The punctured form pays nothing.  The punctured moment is capped by the
DISCOUNTED conductance, so the gap is capped from below by the conductance
itself:

  `gap  >=  w_d * Sel(C)  -  m_d * atom_d` .

The conductance is positive definite under the same bound, so the right side is
a rank-one deflation of a definite matrix.  Its definiteness is ONE scalar: the
dropped label's reading of the SELECTED resolvent, priced against its own
weight.  The moment never appears. -/

/-- **CAUCHY-SCHWARZ THROUGH ANY DEFINITE RESOLVENT.**  Division free, no
symmetry hypothesis beyond definiteness, at every rank. -/
theorem reading_sq_le_resolvent_mul_reading {rank : ℕ}
    {form : Matrix (Fin rank) (Fin rank) ℝ} (hpd : form.PosDef)
    (vec probe : Fin rank → ℝ) :
    (vec ⬝ᵥ probe) ^ 2
      ≤ (vec ⬝ᵥ (form⁻¹ *ᵥ vec)) * (probe ⬝ᵥ (form *ᵥ probe)) := by
  have hunit : IsUnit form.det := isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  set resolved := form⁻¹ *ᵥ vec with hresolved
  have hback : form *ᵥ resolved = vec := by
    rw [hresolved, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hsymm : formᵀ = form := transpose_eq_of_isHermitian hpd.1
  have hpivot : resolved ⬝ᵥ (form *ᵥ resolved) = vec ⬝ᵥ (form⁻¹ *ᵥ vec) := by
    rw [hback, hresolved, dotProduct_comm]
  have hcross : resolved ⬝ᵥ (form *ᵥ probe) = vec ⬝ᵥ probe := by
    rw [← dotProduct_mulVec_transpose form resolved probe, hsymm, hback, dotProduct_comm]
  by_cases hzero : probe = 0
  · subst hzero
    simp
  · have hprobePos : 0 < probe ⬝ᵥ (form *ᵥ probe) := by
      have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hzero
      rwa [star_trivial] at hform
    have hcs := quadForm_cross_sq_le hpd.posSemidef resolved probe hprobePos
    rwa [hcross, hpivot] at hcs

/-- **THE RANK-ONE DEFLATION OF A DEFINITE FORM.**  A scaled definite form stays
definite after a scaled atom leaves it, as soon as the atom's own resolvent
reading is priced below the scale. -/
theorem posDef_smul_sub_smul_atomMatrix_of_resolvent_price {rank : ℕ}
    {form : Matrix (Fin rank) (Fin rank) ℝ} (hpd : form.PosDef)
    (scale atomWeight : ℝ) (vec : Fin rank → ℝ) (hatomWeight : 0 ≤ atomWeight)
    (hprice : atomWeight * (vec ⬝ᵥ (form⁻¹ *ᵥ vec)) < scale) :
    (scale • form - atomWeight • atomMatrix vec).PosDef := by
  have hsymm : formᵀ = form := transpose_eq_of_isHermitian hpd.1
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun probe hne => ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, hsymm,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix vec).1]
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_atomMatrix_mulVec]
    have hcs := reading_sq_le_resolvent_mul_reading hpd vec probe
    have hpos : 0 < probe ⬝ᵥ (form *ᵥ probe) := by
      have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
      rwa [star_trivial] at hform
    nlinarith [hcs, hpos, hatomWeight]

/-- **THE GAP DOMINATES THE SELECTED CONDUCTANCE.**  The bound splits the gap as
the conductance deflation plus the deflated form itself.  No division, no
scaling, no membership hypothesis. -/
theorem directionChartGap_eq_conductanceDeflation_add_chartDeflatedForm
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {dropLabel : Fin size} (hweightNe : weight dropLabel ≠ 0)
    (selected : Finset (Fin size)) :
    directionChartGap direction mass weight selected
      = (weight dropLabel • chartSelectedConductance direction mass weight selected
          - mass dropLabel • atomMatrix (direction dropLabel))
        + chartDeflatedForm direction mass weight dropLabel selected := by
  rw [chartDeflatedForm_eq_puncturedForm direction mass weight hweightNe selected,
    directionChartGap_eq_selected_sub_moment,
    chartMassMatrix_eq_atom_add_punctured direction mass dropLabel]
  module

/-- **THE SELECTED-RESOLVENT CELL.**  A selection carrying the chart deflated
bound at a label whose reading of the SELECTED resolvent is priced below its own
weight dominates strictly.  The moment does not appear, the selection is
arbitrary, and no factor `1 - w_d` is paid. -/
theorem posDef_directionChartGap_of_selectedResolvent_price
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {dropLabel : Fin size} {selected : Finset (Fin size)}
    (hmassNonneg : 0 ≤ mass dropLabel) (hweightPos : 0 < weight dropLabel)
    (hweightLt : weight dropLabel < 1)
    (hpunctured : (chartPuncturedMoment direction mass dropLabel).PosDef)
    (hbound : ChartDeflatedGapBound direction mass weight dropLabel selected)
    (hprice : mass dropLabel
        * (direction dropLabel ⬝ᵥ
            ((chartSelectedConductance direction mass weight selected)⁻¹
              *ᵥ direction dropLabel))
      < weight dropLabel) :
    (directionChartGap direction mass weight selected).PosDef := by
  have hselected : (chartSelectedConductance direction mass weight selected).PosDef :=
    posDef_chartSelectedConductance_of_chartDeflatedGapBound direction mass weight
      hweightPos hweightLt hpunctured hbound
  have hdeflation : (weight dropLabel
      • chartSelectedConductance direction mass weight selected
      - mass dropLabel • atomMatrix (direction dropLabel)).PosDef :=
    posDef_smul_sub_smul_atomMatrix_of_resolvent_price hselected (weight dropLabel)
      (mass dropLabel) (direction dropLabel) hmassNonneg hprice
  rw [directionChartGap_eq_conductanceDeflation_add_chartDeflatedForm direction mass
    weight (ne_of_gt hweightPos) selected]
  exact hdeflation.add_posSemidef hbound

/-- **THE SELECTED-RESOLVENT CELL AT `K4`.**  The produced tree of a label whose
selected resolvent price falls below its weight is strict, and the cell fires. -/
theorem kFourDeflatedDetCellFires_of_selectedResolvent_price
    (point : DirectionChartPoint 6) (dropLabel : Fin 6) {tree : Finset (Fin 6)}
    (hbound : ChartDeflatedGapBound kFourDirection point.mass point.weight
      dropLabel tree) (hcard : tree.card = 3)
    (hprice : point.mass dropLabel
        * (kFourDirection dropLabel ⬝ᵥ
            ((chartSelectedConductance kFourDirection point.mass point.weight tree)⁻¹
              *ᵥ kFourDirection dropLabel))
      < point.weight dropLabel) :
    KFourDeflatedDetCellFires point := by
  have hpd : (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
    posDef_directionChartGap_of_selectedResolvent_price kFourDirection point.mass
      point.weight (point.mass_pos dropLabel).le (point.weight_pos dropLabel)
      (chartPoint_weight_lt_one point dropLabel)
      (posDef_chartPuncturedMoment_kFour point dropLabel) hbound hprice
  exact kFourDeflatedDetCellFires_of_cardThree point dropLabel hcard hbound hpd.det_pos

/-- The produced tree of the chart deflation, with the selected-resolvent price
as the only remaining hypothesis.  This is the sharpest form of the residual that
the Loewner content of the deflation supplies. -/
theorem kFour_exists_chartDeflatedTree_priced (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree ∧
      ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel tree ∧
      (point.mass dropLabel
          * (kFourDirection dropLabel ⬝ᵥ
              ((chartSelectedConductance kFourDirection point.mass point.weight tree)⁻¹
                *ᵥ kFourDirection dropLabel))
        < point.weight dropLabel →
        (directionChartGap kFourDirection point.mass point.weight tree).PosDef) := by
  obtain ⟨tree, hmem, hnotMem, hbound, _⟩ := kFour_exists_chartDeflatedTree point dropLabel
  refine ⟨tree, hmem, hnotMem, hbound, fun hprice => ?_⟩
  exact posDef_directionChartGap_of_selectedResolvent_price kFourDirection point.mass
    point.weight (point.mass_pos dropLabel).le (point.weight_pos dropLabel)
    (chartPoint_weight_lt_one point dropLabel)
    (posDef_chartPuncturedMoment_kFour point dropLabel) hbound hprice

end Gtz
