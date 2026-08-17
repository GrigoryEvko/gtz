/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.WiringKFourWalls
import Gtz.Wave.KFourWedgeForestBridge
import Gtz.Wave.ThreeLinesSlideElimination
import Gtz.Wave.KFourTreeLaplacian
import Gtz.Wave.TriangleStallClosureDeflation
import Gtz.Design.KFourChartSample
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Reduction.ExchangeInvariant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The `M(K4)` backlog, wired

The `M(K4)` class is the only registered chart class with no direction modulus.
Five landed assets of that class had no consumer, and the reason was a naming
accident and not a shortage of mathematics.  This module removes the accident.

## 1.  One matrix carried four names

These four definitions have byte-identical bodies once the direction is fixed to
`Gtz.kFourDirection`:

* `Gtz.chartMassMatrix` (Gtz/Design/ChartInverseTrace.lean)
* `Gtz.chartMassMoment` (Gtz/Wave/ThreeLinesSlideElimination.lean)
* `Gtz.kFourLaplacian` (Gtz/Wave/KirchhoffSignTower.lean)
* `Gtz.kFourMassMoment` (Gtz/Wave/KFourTreeLaplacian.lean)

Exactly one bridge existed, `Gtz.chartMassMatrix_kFour_eq_kFourLaplacian`.
Section 1 adds the missing ones.  Each is `rfl`.

## 2.  The leverage toolkit reaches the `K4` chart

Every theorem of the leverage toolkit carries the hypothesis
`(chartMassMoment direction mass).PosDef`.  At `Gtz.kFourDirection` that
hypothesis is already a theorem, `Gtz.posDef_chartMassMatrix_kFour`, and the
only obstruction was the missing name bridge.  Section 2 instantiates the
counting law, the veto, the leverage total and the leverage cap at the `K4`
chart.  Each one is a single step.

## 3.  The wedge residual, and its exact strength

`Gtz.kFour_exists_tree_posDef_iff_massTreeSum` is unconditional and carries no
leading-block conjunct.  Section 3 states the class residual in that form and
composes it to the registered `A3` formula.

MEASURED CORRECTION.  The wedge form is NOT weaker than
`Gtz.KFourBlockAdmissibleDetTotal`.  Section 3 proves the two propositions
EQUIVALENT (`Gtz.kFourWedgeTreeSignTotal_iff_blockAdmissibleDetTotal`), because
both are equivalent to `Gtz.KFourUniversalStrictTree`.  The wedge form is a
cleaner statement of the same demand and never a smaller demand.

## 4.  A determinant floor that the lane recorded as impossible

The lane record cites `0 ≺ Q ⪯ 1 ⇒ Q ⪰ (det Q) • 1` as false.  The implication
is true, and this repository proves both halves already.  Section 4 lands the
composition.  Every eigenvalue of a contraction lies in the unit interval, so
the determinant is at most each single eigenvalue, and the Loewner form follows.

## 5.  The mass scaling

The signed gap weight is linear in the masses and the signed tree sum is a cubic
form, so the residual is invariant under a positive rescale of all six masses.
The eleven free reals of the class therefore carry a one-parameter freedom, and
the mass and weight cell is ten-dimensional.
-/

namespace Gtz

open Matrix

/-! ## 1.  The missing name bridges -/

section MassMatrixNames

variable {size : ℕ}

/-- **BRIDGE ONE, AT EVERY SIZE AND EVERY DIRECTION.**  The mass moment of
`Gtz/Wave/ThreeLinesSlideElimination.lean` and the mass matrix of
`Gtz/Design/ChartInverseTrace.lean` are the same matrix. -/
theorem chartMassMoment_eq_chartMassMatrix (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) :
    chartMassMoment direction mass = chartMassMatrix direction mass := rfl

/-- **BRIDGE TWO.**  The `K4` mass moment and the `K4` Laplacian are the same
matrix.  This retires the fourth name. -/
theorem kFourMassMoment_eq_kFourLaplacian (mass : Fin 6 → ℝ) :
    kFourMassMoment mass = kFourLaplacian mass := rfl

/-- The mass moment at the `K4` chart is the `K4` Laplacian. -/
theorem chartMassMoment_kFour_eq_kFourLaplacian (mass : Fin 6 → ℝ) :
    chartMassMoment kFourDirection mass = kFourLaplacian mass := rfl

/-- The `K4` mass moment is the mass matrix at the `K4` chart. -/
theorem kFourMassMoment_eq_chartMassMatrix (mass : Fin 6 → ℝ) :
    kFourMassMoment mass = chartMassMatrix kFourDirection mass := rfl

/-- The `K4` chart gap is the boosted moment less the `K4` Laplacian. -/
theorem directionChartGap_kFour_eq_sub_kFourLaplacian (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    directionChartGap kFourDirection mass weight selected
      = kFourSelectedMoment mass weight selected - kFourLaplacian mass := rfl

end MassMatrixNames

/-! ## 2.  The leverage toolkit at the `K4` chart

The hypothesis that blocked the whole toolkit is discharged once and reused. -/

/-- **THE `K4` MASS MOMENT IS POSITIVE DEFINITE.**  At every chart point, with no
admissibility, no line pattern and no weak antecedent.  This is the one step the
leverage toolkit was missing. -/
theorem posDef_chartMassMoment_kFour (point : DirectionChartPoint 6) :
    (chartMassMoment kFourDirection point.mass).PosDef :=
  posDef_chartMassMatrix_kFour point

/-- **THE COUNTING LAW AT THE `K4` CHART.**  At least three of the six labels
carry mass leverage above their own weight, at every chart point. -/
theorem three_le_card_overLevered_kFour (point : DirectionChartPoint 6) :
    3 ≤ (Finset.univ.filter
      (fun label => point.weight label
        < chartMassLeverage kFourDirection point.mass label)).card :=
  three_le_card_overLevered kFourDirection point (posDef_chartMassMoment_kFour point)

/-- **THE LEVERAGE VETO AT THE `K4` CHART.**  A label of a strictly dominating
selection carries mass leverage above its own weight, as soon as one probe reads
that label alone. -/
theorem weight_lt_chartMassLeverage_kFour (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (pivotLabel : Fin 6) (hmem : pivotLabel ∈ selected)
    (probe : Fin 3 → ℝ)
    (hblind : ∀ other ∈ selected, other ≠ pivotLabel →
      kFourDirection other ⬝ᵥ probe = 0)
    (hlive : kFourDirection pivotLabel ⬝ᵥ probe ≠ 0)
    (hgap : (directionChartGap kFourDirection point.mass point.weight selected).PosDef) :
    point.weight pivotLabel < chartMassLeverage kFourDirection point.mass pivotLabel :=
  weight_lt_chartMassLeverage_of_posDef_gap kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos (posDef_chartMassMoment_kFour point) selected
    pivotLabel hmem probe hblind hlive hgap

/-- **THE LEVERAGES TOTAL THREE AT THE `K4` CHART.** -/
theorem sum_chartMassLeverage_kFour (point : DirectionChartPoint 6) :
    ∑ label, chartMassLeverage kFourDirection point.mass label = 3 :=
  sum_chartMassLeverage_eq_three kFourDirection point.mass (posDef_chartMassMoment_kFour point)

/-- **THE LEVERAGE CAP AT THE `K4` CHART.** -/
theorem chartMassLeverage_kFour_le_one (point : DirectionChartPoint 6) (label : Fin 6) :
    chartMassLeverage kFourDirection point.mass label ≤ 1 :=
  chartMassLeverage_le_one kFourDirection point.mass point.mass_pos
    (posDef_chartMassMoment_kFour point) label

/-- Every `K4` mass leverage is nonnegative. -/
theorem chartMassLeverage_kFour_nonneg (point : DirectionChartPoint 6) (label : Fin 6) :
    0 ≤ chartMassLeverage kFourDirection point.mass label :=
  chartMassLeverage_nonneg kFourDirection point.mass point.mass_pos
    (posDef_chartMassMoment_kFour point) label

/-- **THE DUAL CRITERION AT THE `K4` CHART.**  One strict inequality over the
selection coefficients certifies strict domination.  No eigenvalue, no whitener
and no square root enters. -/
theorem posDef_directionChartGap_kFour_of_dualStrict (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hspan : ∀ target : Fin 3 → ℝ, ∃ coefficient : Fin 6 → ℝ,
      ∑ label ∈ selected, coefficient label • kFourDirection label = target)
    (hdual : ∀ coefficient : Fin 6 → ℝ,
      (∑ label ∈ selected, coefficient label • kFourDirection label) ≠ 0 →
      ∑ label ∈ selected, point.weight label / point.mass label * coefficient label ^ 2
        < (∑ label ∈ selected, coefficient label • kFourDirection label) ⬝ᵥ
            ((chartMassMoment kFourDirection point.mass)⁻¹ *ᵥ
              (∑ label ∈ selected, coefficient label • kFourDirection label))) :
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef :=
  posDef_directionChartGap_of_dualStrict kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos (posDef_chartMassMoment_kFour point) selected hspan hdual

/-! ## 3.  The wedge residual of the class

`Gtz.kFour_exists_tree_posDef_iff_massTreeSum` had zero consumers.  It is the
producer of both residual forms below. -/

/-- **THE WEDGE RESIDUAL.**  At every chart point some listed spanning tree makes
strict domination equivalent to one polynomial sign, and carries that sign.  No
leading block, no deflation bound and no whitener occurs. -/
def KFourWedgeTreeSignTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
    ((directionChartGap kFourDirection point.mass point.weight tree).PosDef
        ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree))
      ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE WEDGE RESIDUAL IS AN EQUIVALENCE, AND THIS THEOREM SAYS SO.**  A hunt
cannot refute the residual without refuting the class. -/
theorem kFourUniversalStrictTree_iff_wedgeTreeSignTotal :
    KFourUniversalStrictTree ↔ KFourWedgeTreeSignTotal := by
  constructor
  · intro hstrict point
    obtain ⟨tree, hmem, hposDef⟩ := hstrict point
    have hsign : 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree) := by
      rw [← det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight tree
        (fun label _ => (point.weight_pos label).ne')]
      exact hposDef.det_pos
    exact ⟨tree, hmem, ⟨fun _ => hsign, fun _ => hposDef⟩, hsign⟩
  · intro htotal point
    obtain ⟨tree, hmem, hiff, hsign⟩ := htotal point
    exact ⟨tree, hmem, hiff.mpr hsign⟩

/-- **THE WEDGE RESIDUAL AND THE BLOCK RESIDUAL ARE THE SAME DEMAND.**  The
wedge form drops the leading block conjunct, and this theorem records that the
drop costs nothing and gains nothing.  Read it as a correction: the wedge form
is a cleaner statement and never a smaller demand. -/
theorem kFourWedgeTreeSignTotal_iff_blockAdmissibleDetTotal :
    KFourWedgeTreeSignTotal ↔ KFourBlockAdmissibleDetTotal :=
  kFourUniversalStrictTree_iff_wedgeTreeSignTotal.symm.trans
    kFourUniversalStrictTree_iff_blockAdmissibleDetTotal

/-- The wedge residual closes the four registered consumers of the class. -/
theorem kFourWedgeTreeSignTotal_closes_all (htotal : KFourWedgeTreeSignTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourBlockAdmissibleDetTotal_closes_all
    (kFourWedgeTreeSignTotal_iff_blockAdmissibleDetTotal.mp htotal)

/-- **THE DROP-LABEL RESIDUAL.**  At every chart point some label makes every
tree that the wedge bridge can return from it carry a positive signed tree sum.
The guard is the returned equivalence itself, so no block and no deflation bound
occurs in the statement. -/
def KFourWedgeDropSignTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ dropLabel : Fin 6,
    ∀ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree →
      ((directionChartGap kFourDirection point.mass point.weight tree).PosDef
        ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)) →
      0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE DROP-LABEL RESIDUAL FEEDS THE CLASS.**  This is the first consumer of
`Gtz.kFour_exists_tree_posDef_iff_massTreeSum`.  The implication runs one way
only, because the guard set of the drop form is larger than the guard set of
`Gtz.KFourDeflatedMassTreeSumTotal`. -/
theorem kFourUniversalStrictTree_of_wedgeDropSignTotal
    (htotal : KFourWedgeDropSignTotal) : KFourUniversalStrictTree := by
  intro point
  obtain ⟨dropLabel, hdrop⟩ := htotal point
  obtain ⟨tree, hmem, hnotMem, hiff⟩ := kFour_exists_tree_posDef_iff_massTreeSum point dropLabel
  exact ⟨tree, hmem, hiff.mpr (hdrop tree hmem hnotMem hiff)⟩

/-- The drop-label residual closes the four registered consumers of the class. -/
theorem kFourWedgeDropSignTotal_closes_all (htotal : KFourWedgeDropSignTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all (kFourUniversalStrictTree_of_wedgeDropSignTotal htotal)

/-- The drop-label residual reaches the block residual. -/
theorem kFourBlockAdmissibleDetTotal_of_wedgeDropSignTotal
    (htotal : KFourWedgeDropSignTotal) : KFourBlockAdmissibleDetTotal :=
  kFourUniversalStrictTree_iff_blockAdmissibleDetTotal.mp
    (kFourUniversalStrictTree_of_wedgeDropSignTotal htotal)

/-! ## 4.  The determinant floor of a contraction

The lane record cites this implication as false.  It is true. -/

section DeterminantFloor

variable {dim : ℕ}

/-- **THE DETERMINANT FLOOR OF A CONTRACTION.**  A positive semidefinite matrix
below the identity dominates its own determinant times the identity, in the
Loewner order.  Every eigenvalue lies in the unit interval, so the determinant is
at most each single eigenvalue, and the shifted matrix stays positive
semidefinite.

This is the implication that the `M(K4)` lane record names as false.  The
quoted counterexample at invariants `(2, 1.95, 0.95)` is not a contraction: a
symmetric three by three matrix with every eigenvalue at most one and trace two
has determinant at most `8/27`. -/
theorem posSemidef_sub_det_smul_one_of_contraction
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hpsd : form.PosSemidef)
    (hcontraction : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form).PosSemidef) :
    (form - form.det • (1 : Matrix (Fin dim) (Fin dim) ℝ)).PosSemidef :=
  posSemidef_sub_smul_one_of_eigenvalue_ge hpsd.1 form.det
    fun eigenIndex =>
      det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub hpsd hcontraction eigenIndex

/-- The strict form of the floor, which is the shape the lane record quotes:
`0 ≺ Q ⪯ 1` gives `Q ⪰ (det Q) • 1`. -/
theorem posSemidef_sub_det_smul_one_of_posDef_of_contraction
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hposDef : form.PosDef)
    (hcontraction : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form).PosSemidef) :
    (form - form.det • (1 : Matrix (Fin dim) (Fin dim) ℝ)).PosSemidef :=
  posSemidef_sub_det_smul_one_of_contraction hposDef.posSemidef hcontraction

/-- The quadratic reading of the floor: the determinant of a contraction never
passes any of its own quadratic readings at a unit probe. -/
theorem det_mul_self_le_dotProduct_of_contraction
    {form : Matrix (Fin dim) (Fin dim) ℝ} (hpsd : form.PosSemidef)
    (hcontraction : ((1 : Matrix (Fin dim) (Fin dim) ℝ) - form).PosSemidef)
    (probe : Fin dim → ℝ) :
    form.det * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ (form *ᵥ probe) := by
  have hshift := posSemidef_sub_det_smul_one_of_contraction hpsd hcontraction
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hshift).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hform
  linarith

end DeterminantFloor

/-! ## 5.  The mass scaling of the residual

The class carries eleven free reals: six masses, six weights and one linear
constraint.  The residual sees the masses only through a cubic form, so one of
the eleven is free. -/

/-- The signed gap weight is linear in the masses. -/
theorem signedGapWeight_smul_mass {size : ℕ} (scale : ℝ) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) :
    signedGapWeight (scale • mass) weight selected
      = scale • signedGapWeight mass weight selected := by
  funext label
  simp only [signedGapWeight, Pi.smul_apply, smul_eq_mul]
  split <;> ring

/-- The signed tree sum is a cubic form. -/
theorem kFourMassTreeSum_smul (scale : ℝ) (vec : Fin 6 → ℝ) :
    kFourMassTreeSum (scale • vec) = scale ^ 3 * kFourMassTreeSum vec := by
  simp only [kFourMassTreeSum, Pi.smul_apply, smul_eq_mul]
  ring

/-- **THE RESIDUAL IS MASS-SCALE INVARIANT.**  Rescaling all six masses by one
positive number multiplies every signed tree sum by the cube of that number, so
it moves no sign.  The mass and weight cell of the class is ten-dimensional and
not eleven-dimensional. -/
theorem kFourMassTreeSum_signedGapWeight_smul_mass (scale : ℝ) (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) :
    kFourMassTreeSum (signedGapWeight (scale • mass) weight selected)
      = scale ^ 3 * kFourMassTreeSum (signedGapWeight mass weight selected) := by
  rw [signedGapWeight_smul_mass, kFourMassTreeSum_smul]

/-- The sign of the signed tree sum is invariant under a positive mass rescale. -/
theorem kFourMassTreeSum_pos_iff_smul_mass {scale : ℝ} (hscale : 0 < scale)
    (mass weight : Fin 6 → ℝ) (selected : Finset (Fin 6)) :
    0 < kFourMassTreeSum (signedGapWeight (scale • mass) weight selected)
      ↔ 0 < kFourMassTreeSum (signedGapWeight mass weight selected) := by
  have hpow : (0 : ℝ) < scale ^ 3 := pow_pos hscale 3
  rw [kFourMassTreeSum_signedGapWeight_smul_mass]
  constructor
  · intro hpos
    by_contra hnot
    push_neg at hnot
    nlinarith
  · intro hpos
    exact mul_pos hpow hpos

/-! ## 6.  The over-levered set contains a spanning tree

The veto says that a strictly dominating tree lies inside the over-levered set.
The counting law says the over-levered set holds at least three labels.  Neither
law says that the candidate list is ever usable, because a three-element
candidate set that is one of the four triangles carries no spanning tree at all.

This section closes that hole.  The dependent-triple cap of
`Gtz/Wave/ThreeLinesSlideElimination.lean` gives each triangle a leverage total
of at most two, and the leverages total three, so the three labels off a triangle
carry leverage total at least one.  Their weights total less than one, because
the three triangle weights are strictly positive.  So every triangle has an
over-levered label outside it.  A three-element set of `K4` edges that meets the
complement of every triangle covers every vertex, and a vertex cover of three
edges is a spanning tree. -/

/-- The leverage cap of the triangle `{0, 1, 2}`. -/
theorem kFour_leverage_cap_zeroOneTwo (point : DirectionChartPoint 6) :
    chartMassLeverage kFourDirection point.mass 0
      + chartMassLeverage kFourDirection point.mass 1
      + chartMassLeverage kFourDirection point.mass 2 ≤ 2 := by
  refine sum_leverage_le_two_of_dependent kFourDirection point.mass point.mass_pos
    (posDef_chartMassMoment_kFour point) 0 1 2 (by decide) (by decide) (by decide)
    1 (-1) 1 (Or.inl one_ne_zero) ?_
  funext idx
  fin_cases idx <;>
    simp [kFourDirection_zero, kFourDirection_one, kFourDirection_two] <;> norm_num

/-- The leverage cap of the triangle `{0, 3, 4}`. -/
theorem kFour_leverage_cap_zeroThreeFour (point : DirectionChartPoint 6) :
    chartMassLeverage kFourDirection point.mass 0
      + chartMassLeverage kFourDirection point.mass 3
      + chartMassLeverage kFourDirection point.mass 4 ≤ 2 := by
  refine sum_leverage_le_two_of_dependent kFourDirection point.mass point.mass_pos
    (posDef_chartMassMoment_kFour point) 0 3 4 (by decide) (by decide) (by decide)
    1 (-1) 1 (Or.inl one_ne_zero) ?_
  funext idx
  fin_cases idx <;>
    simp [kFourDirection_zero, kFourDirection_three, kFourDirection_four] <;> norm_num

/-- The leverage cap of the triangle `{1, 3, 5}`. -/
theorem kFour_leverage_cap_oneThreeFive (point : DirectionChartPoint 6) :
    chartMassLeverage kFourDirection point.mass 1
      + chartMassLeverage kFourDirection point.mass 3
      + chartMassLeverage kFourDirection point.mass 5 ≤ 2 := by
  refine sum_leverage_le_two_of_dependent kFourDirection point.mass point.mass_pos
    (posDef_chartMassMoment_kFour point) 1 3 5 (by decide) (by decide) (by decide)
    1 (-1) 1 (Or.inl one_ne_zero) ?_
  funext idx
  fin_cases idx <;>
    simp [kFourDirection_one, kFourDirection_three, kFourDirection_five] <;> norm_num

/-- The leverage cap of the triangle `{2, 4, 5}`. -/
theorem kFour_leverage_cap_twoFourFive (point : DirectionChartPoint 6) :
    chartMassLeverage kFourDirection point.mass 2
      + chartMassLeverage kFourDirection point.mass 4
      + chartMassLeverage kFourDirection point.mass 5 ≤ 2 := by
  refine sum_leverage_le_two_of_dependent kFourDirection point.mass point.mass_pos
    (posDef_chartMassMoment_kFour point) 2 4 5 (by decide) (by decide) (by decide)
    1 (-1) 1 (Or.inl one_ne_zero) ?_
  funext idx
  fin_cases idx <;>
    simp [kFourDirection_two, kFourDirection_four, kFourDirection_five] <;> norm_num

/-- **EVERY TRIANGLE HAS AN OVER-LEVERED LABEL OUTSIDE IT.**  The four triangles
are the four dependent triples of the `K4` chart.  Each one caps at leverage two,
the six leverages total three, and the six weights total one with every weight
strictly positive. -/
theorem kFour_exists_overLevered_outside_dependentTriple (point : DirectionChartPoint 6)
    (triple : Finset (Fin 6)) (htriple : triple ∈ kFourDependentTripleList) :
    ∃ label, label ∉ triple
      ∧ point.weight label < chartMassLeverage kFourDirection point.mass label := by
  have hlever : chartMassLeverage kFourDirection point.mass 0
      + chartMassLeverage kFourDirection point.mass 1
      + chartMassLeverage kFourDirection point.mass 2
      + chartMassLeverage kFourDirection point.mass 3
      + chartMassLeverage kFourDirection point.mass 4
      + chartMassLeverage kFourDirection point.mass 5 = 3 := by
    have := sum_chartMassLeverage_kFour point
    rwa [Fin.sum_univ_six] at this
  have hweight : point.weight 0 + point.weight 1 + point.weight 2
      + point.weight 3 + point.weight 4 + point.weight 5 = 1 := by
    have := point.weight_sum_one
    rwa [Fin.sum_univ_six] at this
  have hp0 := point.weight_pos 0
  have hp1 := point.weight_pos 1
  have hp2 := point.weight_pos 2
  have hp3 := point.weight_pos 3
  have hp4 := point.weight_pos 4
  have hp5 := point.weight_pos 5
  simp only [kFourDependentTripleList, List.mem_cons, List.not_mem_nil, or_false] at htriple
  rcases htriple with rfl | rfl | rfl | rfl
  · by_contra hcon
    push_neg at hcon
    have h3 := hcon 3 (by decide)
    have h4 := hcon 4 (by decide)
    have h5 := hcon 5 (by decide)
    have hcap := kFour_leverage_cap_zeroOneTwo point
    linarith
  · by_contra hcon
    push_neg at hcon
    have h1 := hcon 1 (by decide)
    have h2 := hcon 2 (by decide)
    have h5 := hcon 5 (by decide)
    have hcap := kFour_leverage_cap_zeroThreeFour point
    linarith
  · by_contra hcon
    push_neg at hcon
    have h0 := hcon 0 (by decide)
    have h2 := hcon 2 (by decide)
    have h4 := hcon 4 (by decide)
    have hcap := kFour_leverage_cap_oneThreeFive point
    linarith
  · by_contra hcon
    push_neg at hcon
    have h0 := hcon 0 (by decide)
    have h1 := hcon 1 (by decide)
    have h3 := hcon 3 (by decide)
    have hcap := kFour_leverage_cap_twoFourFive point
    linarith

set_option maxRecDepth 40000 in
/-- **THE COMBINATORIAL HALF.**  A set of `K4` edges with three or more members
that meets the complement of every triangle contains a spanning tree.  The four
triangle complements are the four vertex stars, so the hypothesis says that the
set covers every vertex. -/
theorem kFour_exists_tree_subset_of_meets_dependentTriples (candidate : Finset (Fin 6))
    (hcard : 3 ≤ candidate.card)
    (hmeet : ∀ triple ∈ kFourDependentTripleList,
      ∃ label ∈ candidate, label ∉ triple) :
    ∃ tree ∈ kFourSpanningTreeList, tree ⊆ candidate := by
  revert hcard hmeet
  revert candidate
  decide

/-- **THE OVER-LEVERED SET CONTAINS A SPANNING TREE.**  At every `K4` chart
point some listed spanning tree has all three of its labels over-levered.

The veto `Gtz.weight_lt_chartMassLeverage_kFour` says that a strictly dominating
tree has this property, so the candidate list of the class is exactly the set of
trees inside the over-levered set.  This theorem proves that the candidate list
is never empty, and that no chart point pushes it onto the four triangles, where
it would carry no tree at all. -/
theorem kFour_exists_overLevered_spanningTree (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourSpanningTreeList, ∀ label ∈ tree,
      point.weight label < chartMassLeverage kFourDirection point.mass label := by
  classical
  set candidate := Finset.univ.filter
    (fun label => point.weight label
      < chartMassLeverage kFourDirection point.mass label) with hcandidate
  have hcard : 3 ≤ candidate.card := three_le_card_overLevered_kFour point
  have hmeet : ∀ triple ∈ kFourDependentTripleList,
      ∃ label ∈ candidate, label ∉ triple := by
    intro triple htriple
    obtain ⟨label, hout, hover⟩ :=
      kFour_exists_overLevered_outside_dependentTriple point triple htriple
    exact ⟨label, by simp [hcandidate, hover], hout⟩
  obtain ⟨tree, hmem, hsubset⟩ :=
    kFour_exists_tree_subset_of_meets_dependentTriples candidate hcard hmeet
  refine ⟨tree, hmem, fun label hlabel => ?_⟩
  have := hsubset hlabel
  simpa [hcandidate] using this

/-! ## 7.  The mass-weighted tree total, and its refutation

A pigeonhole over the sixteen trees would discharge the determinant conjunct of
`Gtz.KFourBlockAdmissibleDetTotal` with no selection rule.  Give each tree the
product of its three masses, total the sixteen signed tree sums against those
coefficients, and a positive total forces one positive signed tree sum.

The total is NOT positive.  It is `-7/256` at `Gtz.tetrahedronChartPoint`, which
is the campaign's own canonical fixture.  Section 7 lands that value in kernel.

METHOD WARNING, and this is the fourth occurrence in this campaign.  Before the
refuter was found, this total scored ZERO failures at 20,000,000 double-precision
chart points and ZERO failures at 332,000 exact-rational chart points sampled
over twenty decades (MEASURED).  Every one of those samples drew the six masses
and the six weights independently over a wide range, so it never produced nearly
equal masses together with nearly uniform weights.  The refuter is the most
symmetric point in the whole campaign.  A wide-range independent sample is not
evidence about a symmetric locus. -/

/-- The mass product of a selection. -/
noncomputable def kFourTreeMassProduct (mass : Fin 6 → ℝ) (tree : Finset (Fin 6)) : ℝ :=
  ∏ label ∈ tree, mass label

/-- The mass-weighted total of the sixteen signed tree sums. -/
noncomputable def kFourMassWeightedTreeTotal (point : DirectionChartPoint 6) : ℝ :=
  (kFourSpanningTreeList.map fun tree =>
    kFourTreeMassProduct point.mass tree
      * kFourMassTreeSum (signedGapWeight point.mass point.weight tree)).sum

/-- A list of nonpositive reals totals at most zero. -/
theorem list_sum_nonpos {entries : List ℝ} (hentry : ∀ entry ∈ entries, entry ≤ 0) :
    entries.sum ≤ 0 := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
    rw [List.sum_cons]
    exact add_nonpos (hentry head (by simp)) (ih fun entry hmem => hentry entry (by simp [hmem]))

/-- **WHAT THE PIGEONHOLE WOULD HAVE BOUGHT.**  A positive mass-weighted total
forces one listed tree to carry a positive signed tree sum, with no selection
rule and no block condition. -/
theorem kFour_exists_massTreeSum_pos_of_total (point : DirectionChartPoint 6)
    (htotal : 0 < kFourMassWeightedTreeTotal point) :
    ∃ tree ∈ kFourSpanningTreeList,
      0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree) := by
  by_contra hcon
  push_neg at hcon
  have hnonpos : ∀ entry ∈ (kFourSpanningTreeList.map fun tree =>
      kFourTreeMassProduct point.mass tree
        * kFourMassTreeSum (signedGapWeight point.mass point.weight tree)), entry ≤ 0 := by
    intro entry hmem
    obtain ⟨tree, htree, rfl⟩ := List.mem_map.mp hmem
    have hprod : 0 ≤ kFourTreeMassProduct point.mass tree :=
      Finset.prod_nonneg fun label _ => (point.mass_pos label).le
    exact mul_nonpos_of_nonneg_of_nonpos hprod (hcon tree htree)
  exact absurd htotal (not_lt.mpr (list_sum_nonpos hnonpos))

/-- **THE MASS-WEIGHTED TOTAL AT THE TETRAHEDRON.**  Four stars each carry
`20/4096` and twelve paths each carry `-16/4096`, so the total is `-7/256`. -/
theorem tetrahedron_kFourMassWeightedTreeTotal :
    kFourMassWeightedTreeTotal tetrahedronChartPoint = -7/256 := by
  rw [kFourMassWeightedTreeTotal, kFourSpanningTreeList]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kFourTreeMassProduct, kFourMassTreeSum, signedGapWeight, tetrahedronChartPoint]
  norm_num +decide [Finset.prod_const, Finset.mem_insert, Finset.mem_singleton]

/-- **THE MASS-WEIGHTED PIGEONHOLE IS REFUTED, IN KERNEL.**  Do not reopen it.
The refuter is `Gtz.tetrahedronChartPoint`, and the class is untouched there:
the four vertex stars all dominate strictly at that point. -/
theorem kFourMassWeightedTreeTotal_not_always_pos :
    ¬ (∀ point : DirectionChartPoint 6, 0 < kFourMassWeightedTreeTotal point) := by
  intro htotal
  have hvalue := htotal tetrahedronChartPoint
  rw [tetrahedron_kFourMassWeightedTreeTotal] at hvalue
  norm_num at hvalue

/-! ## 8.  The flat-pair census of the `K4` chart

A FLAT PAIR is two labels that lie on one line of the pattern.  The line pattern
of `Gtz.kFourDirection` is the four triangles, which are the four dependent
triples.  Two `K4` edges lie on a common triangle unless they are opposite edges,
and the three opposite pairs are `{0, 5}`, `{1, 4}` and `{2, 3}`.

Three labels can never be pairwise opposite, because the opposite relation is a
perfect matching of the six labels.  So EVERY card-three subset of the `K4` chart
holds a flat pair, and the flat-pair-free residual is EMPTY.  At the four other
registered chart classes that residual is not empty. -/

/-- Two distinct `K4` labels lie on a common triangle, unless they are one of the
three opposite pairs. -/
theorem kFour_pair_on_dependentTriple_or_opposite (first second : Fin 6)
    (hne : first ≠ second) :
    (∃ triple ∈ kFourDependentTripleList, first ∈ triple ∧ second ∈ triple)
      ∨ (first = 0 ∧ second = 5) ∨ (first = 5 ∧ second = 0)
      ∨ (first = 1 ∧ second = 4) ∨ (first = 4 ∧ second = 1)
      ∨ (first = 2 ∧ second = 3) ∨ (first = 3 ∧ second = 2) := by
  revert hne
  revert first second
  decide

set_option maxRecDepth 40000 in
/-- **THE FLAT-PAIR-FREE RESIDUAL OF THE `K4` CHART IS EMPTY.**  Every one of the
twenty card-three subsets holds two labels on a common triangle.  A criterion
that reads a flat pair therefore reaches every selection of this chart, and no
selection escapes it. -/
theorem kFour_cardThree_holds_flatPair (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    ∃ triple ∈ kFourDependentTripleList, ∃ first ∈ selected, ∃ second ∈ selected,
      first ≠ second ∧ first ∈ triple ∧ second ∈ triple := by
  revert hcard
  revert selected
  decide

end Gtz
