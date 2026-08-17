/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.WiringKFourWalls
import Gtz.Wave.KFourWedgeForestBridge
import Gtz.Wave.ThreeLinesSlideElimination
import Gtz.Wave.KFourTreeLaplacian
import Gtz.Wave.TriangleStallClosureDeflation
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Reduction.ExchangeInvariant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

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

end Gtz
