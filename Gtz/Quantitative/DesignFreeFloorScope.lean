import Mathlib
import Gtz.Quantitative.ChartDescentFromMinimality
import Gtz.Quantitative.ChartDiamondValueZero
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Quantitative.ChartStationaryDesignFreeWindow
import Gtz.Reduction.ChartPointFactorisation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The design-free floor at its widest scope, and its non-vacuity

`Gtz/Quantitative/ChartStationaryDesignFreeWindow.lean` discharges the design
hypothesis of the value-floor layer and carries the SHARP design-free floors:
`-4/27` at `(6,3)` and `-10/77` at `(7,3)`, off `Gtz.combinedValueFloor`.  Two
things it does not carry are supplied here.

## What is added

* `Gtz.cauchyBinetValueFloor_le_value_of_isChartStationaryData_designFree` —
  the Cauchy–Binet floor, design-free, **at every cell without exception**.  It is
  weaker than the combined floor wherever both apply, by the landed
  `Gtz.cauchyBinetValueFloor_le_combinedValueFloor` — but that comparison carries
  `0 < rank` and `rank ≤ size`, and this theorem carries neither.  ITS ONLY CONTENT
  IS SCOPE: it survives at the degenerate cells where the sharper route does not
  reach, and nowhere else does it say anything the window does not say better.
* the two NON-VACUITY witnesses.  The design-free strict bound
  `Gtz.neg_inv_size_lt_value_of_isChartStationaryData_designFree` is instantiated at
  two SHIPPED chart witnesses, so the whole design-free layer is known to have an
  inhabited antecedent rather than merely an unrefuted one.

## What was deleted rather than landed

The `(6,3)` and `(7,3)` instances of the Cauchy–Binet floor, `-3/20` and `-2/15`,
were proved here as well.  **BOTH ARE STRICTLY WEAKER COROLLARIES OF THE LANDED
SHARP FLOORS, WITH NO EXTRA HYPOTHESIS**: `-4/27 > -3/20` and `-10/77 > -2/15`, and
each follows from its sharp sibling by `linarith` alone.  They are deleted.  A
reader wanting a floor at either cell should take the sharp one; a reader wanting
the Cauchy–Binet floor at a cell where the rank hypotheses fail should take the
general theorem below.

## The honest scope of the whole layer

Every floor here, sharp or not, is trivially true at a nonnegative value, so all of
its content sits on the negative side — and
`Gtz.gtzWeighted_six_three_iff_chartStationaryValueNonneg` makes that side, at
`(6,3)`, EQUIVALENT to the failure of the cell.  The two witnesses below live at
`(4,3)` and `(5,3)`, where `Gtz.gtzWeighted_of_le_five` makes a negative value
IMPOSSIBLE, so neither of them exercises a floor: they establish that the
antecedent is inhabited, and nothing more.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*} {projection : Matrix (Fin size) (Fin size) ℝ}
  {weight : Fin size → ℝ} {value : ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The Cauchy–Binet floor, design-free, at every cell -/

/-- **FLOOR-CB, DESIGN-FREE, WITH NO RANK HYPOTHESIS.**  The Cauchy–Binet floor holds
of every chart stationarity datum that is an argmax, with no design supplied.  The
combined floor is sharper wherever `0 < rank ≤ size`; this one carries no such
condition, and that is the whole of what it adds. -/
theorem cauchyBinetValueFloor_le_value_of_isChartStationaryData_designFree
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    cauchyBinetValueFloor size rank ≤ value := by
  obtain ⟨design, hchart⟩ := exists_design_of_isChartStationaryData hdata
  exact cauchyBinetValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata

/-! ## Non-vacuity: the antecedent is inhabited at two shipped chart witnesses -/

/-- **THE ANTECEDENT IS INHABITED at the `(4,3)` tetrahedron**, and the design-free
strict bound fires there: `-1/4 < 0`. -/
theorem chartTetra_neg_inv_four_lt_zero : -((4 : ℝ))⁻¹ < (0 : ℝ) := by
  have hfires :=
    neg_inv_size_lt_value_of_isChartStationaryData_designFree
      chartTetraProjection_isChartArgmaxValue chartTetraProjection_isChartStationaryData
  exact_mod_cast hfires

/-- **THE ANTECEDENT IS INHABITED at the `(5,3)` diamond chart** as well.  Note the
`Fin 8` in its bundle is the ACTIVE INDEX — eight active blocks over five atoms. -/
theorem chartDiamond_neg_inv_five_lt_zero : -((5 : ℝ))⁻¹ < (0 : ℝ) := by
  have hfires :=
    neg_inv_size_lt_value_of_isChartStationaryData_designFree
      diamondChart_isChartArgmaxValue diamondChart_isChartStationaryData
  exact_mod_cast hfires

end Gtz
