/-
# The sign of an admissible chart stationarity value IS the cell

Every quantitative floor in `Gtz/Quantitative/` bounds `value` from below at a datum
carrying BOTH `Gtz.IsChartStationaryData` and `Gtz.IsChartArgmaxValue`: the shipped
Cauchy–Binet floors, the elementary floor, the `-1/size` floor and its strict form, and
the `(6,3)` crux frontier all have exactly that antecedent.  Each of them is trivially
true when the value is nonnegative, so all of their content sits on the NEGATIVE side.

This file measures that side.  The main theorem is four steps, all of them shipped
elsewhere:

* a stationarity datum IS a chart point — its seven `Gtz.ChartPoint` fields are seven of
  its own thirteen.  That coercion is `Gtz.chartPointOfIsChartStationaryData` and it is
  CONSUMED here, not restated: it was built twice independently, the two copies were
  compared in the kernel and found equal by `rfl`, and only one survives.  They differed
  only in the ORDER of their implicit binders, which is exactly why a type-level
  duplicate hunt could not see them;
* `Gtz.chartPointHasDesign` turns an interior chart point into a weighted design, with no
  hypothesis beyond the strict positivity the bundle already carries;
* `Gtz.GtzWeighted` then supplies a dominating subset of the right cardinality;
* `Gtz.IsChartArgmaxValue` supplies, at that very subset, a unit probe whose Rayleigh
  quotient is at most the value — and domination says that quotient is nonnegative.

Hence `0 ≤ value`, and at `(6, 3)` the converse holds too through the shipped
hypothesis-free variational principle, so the two statements are EQUIVALENT.

WHAT THIS BUYS AND WHAT IT COSTS.  It buys the rank-two and small-size instances outright:
an admissible stationarity datum at rank two has a nonnegative value at every size, which
gives the `(4,2)` uniform datum's inadmissibility in one line where the tree proves the
`(6,3)` analogue by hand.  It COSTS the floor programme its independence: at `(6, 3)` the
antecedent of every floor theorem, restricted to the negative values where those theorems
say anything, is INHABITED EXACTLY WHEN THE CELL FAILS.  No floor can be improved into a
proof of the cell without becoming a proof of the cell.
-/
import Mathlib
import Gtz.Quantitative.ChartStationary
import Gtz.Quantitative.ChartStationaryDesignFreeWindow
import Gtz.Quantitative.ChartTwoBlock
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Reduction.ChartRealization
import Gtz.Reduction.ChartAttainmentWeld
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {size : ℕ} {activeIndex : Type*} {rank : ℕ}
  {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
  {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The chart point underlying a stationarity datum

The coercion itself is `Gtz.chartPointOfIsChartStationaryData`, landed in
`Gtz/Quantitative/ChartStationaryDesignFreeWindow.lean` and consumed here.  What this
file adds to it is the gap bridge below, which the coercion's own module does not
carry and which the sign law needs. -/

/-- The two gap vocabularies agree on the underlying chart point, definitionally. -/
theorem chartPointGap_chartPointOfIsChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    chartPointGap (chartPointOfIsChartStationaryData hdata)
      = chartStationaryGap projection weight := rfl

/-! ## The sign law -/

/-- **THE SIGN LAW.**  If the cell holds, every admissible chart stationarity datum has a
nonnegative value.  The design hypothesis carried by every shipped floor theorem is not
needed: it is manufactured from the bundle by `Gtz.chartPointHasDesign`. -/
theorem zero_le_value_of_gtzWeighted_of_isChartArgmaxValue
    (hgtz : GtzWeighted size rank)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    0 ≤ value := by
  obtain ⟨design, hdesign⟩ :=
    chartPointHasDesign size rank (chartPointOfIsChartStationaryData hdata) hdata.weight_pos
  obtain ⟨selected, hcard, hdominates⟩ := hgtz design
  obtain ⟨probe, _hunit, hsupport, hquotient⟩ := hargmax selected hcard
  have hchartDominates : ChartDominates (chartPointOfIsChartStationaryData hdata) selected := by
    rw [← hdesign]
    exact (dominates_iff_chartDominates design selected hcard).mp hdominates
  have hnonneg := hchartDominates probe hsupport
  rw [chartPointGap_chartPointOfIsChartStationaryData hdata] at hnonneg
  linarith

/-- **THE CONTRAPOSITIVE, WHICH IS THE OPERATIVE FORM.**  An admissible chart stationarity
datum at a strictly negative value REFUTES the cell it lives in. -/
theorem not_gtzWeighted_of_isChartArgmaxValue_of_value_neg
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hneg : value < 0) :
    ¬ GtzWeighted size rank := fun hgtz =>
  absurd (zero_le_value_of_gtzWeighted_of_isChartArgmaxValue hgtz hargmax hdata) (not_le.mpr hneg)

/-! ## The instances that are unconditional -/

/-- **RANK TWO, EVERY SIZE, NO HYPOTHESIS.**  `Gtz.gtz_rank_two` is shipped, so at rank two
the sign law is a theorem outright. -/
theorem zero_le_value_rank_two_of_isChartArgmaxValue
    {projectionTwo : Matrix (Fin size) (Fin size) ℝ}
    (hargmax : IsChartArgmaxValue 2 projectionTwo weight value)
    (hdata : IsChartStationaryData 2 projectionTwo weight value activeSet activeSubset
      activeWeight tightDir) :
    0 ≤ value :=
  zero_le_value_of_gtzWeighted_of_isChartArgmaxValue (gtz_rank_two size) hargmax hdata

/-- **SIZE AT MOST FIVE, EVERY POSITIVE RANK, NO HYPOTHESIS.**  Off `Gtz.gtzWeighted_of_le_five`. -/
theorem zero_le_value_of_size_le_five_of_isChartArgmaxValue (hrank : 1 ≤ rank) (hsize : size ≤ 5)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    0 ≤ value :=
  zero_le_value_of_gtzWeighted_of_isChartArgmaxValue
    (gtzWeighted_of_le_five size rank hrank hsize) hargmax hdata

/-- **THE `(4,2)` UNIFORM DATUM IS INADMISSIBLE, FOR FREE.**  The tree proves the `(6,3)`
analogue `Gtz.not_chartTwoBlockTriple_isChartArgmaxValue` by hand, with an explicit probe
and a nonlinear arithmetic step, because `Gtz.GtzWeighted 6 3` is open.  At rank two the
cell is a theorem, so the same conclusion costs one line.  -/
theorem not_isChartArgmaxValue_chartTwoBlockUniformProjection :
    ¬ IsChartArgmaxValue 2 chartTwoBlockUniformProjection chartTwoBlockUniformWeight
      (-(4 : ℝ)⁻¹) := by
  intro hargmax
  have hsign := zero_le_value_rank_two_of_isChartArgmaxValue (size := 4) hargmax
    chartTwoBlockUniformProjection_isChartStationaryData
  norm_num at hsign

/-! ## The `(6,3)` equivalence -/

/-- The statement that every admissible chart stationarity datum of a cell has a
nonnegative value. -/
def ChartStationaryValueNonneg (size rank : ℕ) : Prop :=
  ∀ (activeIndex : Type) (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    (value : ℝ) (activeSet : Finset activeIndex) (activeSubset : activeIndex → Finset (Fin size))
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → Fin size → ℝ),
    IsChartArgmaxValue rank projection weight value →
    IsChartStationaryData rank projection weight value activeSet activeSubset activeWeight
      tightDir →
    0 ≤ value

theorem chartStationaryValueNonneg_of_gtzWeighted (hgtz : GtzWeighted size rank) :
    ChartStationaryValueNonneg size rank := fun _ _ _ _ _ _ _ _ hargmax hdata =>
  zero_le_value_of_gtzWeighted_of_isChartArgmaxValue hgtz hargmax hdata

/-- **THE FLOOR LAYER IS THE CELL.**  At `(6, 3)` the sign law is not merely implied by the
cell, it is EQUIVALENT to it.  The converse composes two shipped theorems: the
hypothesis-free variational principle
`Gtz.exists_design_minimiser_of_not_gtzWeighted_sixThree`, which realises a failure at a
weighted design minimising the chart objective over the whole closed domain with strictly
negative value, and `Gtz.exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin`,
which hands that minimiser both the bundle and admissibility.

CONSEQUENCE, and it is the reason to state this.  Every value floor in the layer —
`-4/27`, `-3/20`, `-1/6`, the elementary floor, the weight box — has an antecedent that,
on the negative values where the floor says anything at all, is inhabited exactly when the
cell fails.  Under the conjecture every one of them is VACUOUS on that side, and the
programme of improving them terminates only by reaching `0 ≤ value`, which IS the cell. -/
theorem gtzWeighted_six_three_iff_chartStationaryValueNonneg :
    GtzWeighted 6 3 ↔ ChartStationaryValueNonneg 6 3 := by
  refine ⟨chartStationaryValueNonneg_of_gtzWeighted, fun hnonneg => ?_⟩
  by_contra hfail
  obtain ⟨design, hminimal, hnegative, _hnoSelection⟩ :=
    exists_design_minimiser_of_not_gtzWeighted_sixThree hfail
  obtain ⟨⟨multiplier, selection, hdata⟩, hargmax⟩ :=
    exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin (chartPointOfDesign design)
      design.weight_pos hminimal
  exact absurd (hnonneg _ _ _ _ _ _ multiplier selection hargmax hdata) (not_le.mpr hnegative)

/-! ## The two landed negative-value data sit exactly at the pinch -/

/-- At the `(6,3)` endpoint datum every weight sits SIMULTANEOUSLY at the shipped floor
`-value` and at the cap `1 + (size - 1) * value`, so the two faces pinch. -/
theorem chartTwoBlockTripleWeight_eq_floor_and_cap (atomIndex : Fin 6) :
    chartTwoBlockTripleWeight atomIndex = -(-(6 : ℝ)⁻¹) ∧
      chartTwoBlockTripleWeight atomIndex = 1 + ((6 : ℝ) - 1) * (-(6 : ℝ)⁻¹) := by
  constructor <;> norm_num [chartTwoBlockTripleWeight]

/-- The same pinch at the `(4,2)` endpoint datum. -/
theorem chartTwoBlockUniformWeight_eq_floor_and_cap (atomIndex : Fin 4) :
    chartTwoBlockUniformWeight atomIndex = -(-(4 : ℝ)⁻¹) ∧
      chartTwoBlockUniformWeight atomIndex = 1 + ((4 : ℝ) - 1) * (-(4 : ℝ)⁻¹) := by
  constructor <;> norm_num [chartTwoBlockUniformWeight]

end Gtz
