/-
# The corank-three hinge: the rank-3 frontier stated rank-generically

`Gtz.StressFreeHingeHoldsSixThree` is the single Prop to which the whole of
rank-three GTZ reduces.  Its quantifier shape does not mention the number 3 in
any essential way: it says that on the corank-3 cell — support size
`rank + 3` at rank `rank` — a stress-free tie forces a parallel pair.  This
file states that Prop at general rank and records that the rank-3 instance IS
the tree's frontier, definitionally: `Fin (3 + 3)` and `WeightedDesign (3 + 3) 3`
reduce to their literal forms in the kernel, so the bridge is `Iff.rfl` — no
transport, no congruence, no cast.

Consequence: every future attack on the frontier may be phrased against
`StressFreeHingeHoldsAtCorankThree rank` and specialized for free, and the
capstone of the rigidity bridge re-exports through it unchanged.  This serves
the standing general-k directive — uniform induction over rank, never per-rank
closure.

Rank-dependence warning carried from the general-k design lane: at rank 3 the
cell size `rank + 3 = 6` EQUALS `dim Sym(3)`, so stress-freeness means the six
atom matrices form a basis — a codimension-0 (generic) condition.  For rank
`k >= 4`, `k + 3 < k * (k + 1) / 2`, so stress-freeness is generic for a
different reason (fewer atoms than dimensions), and the trichotomy weight
shifts: the stressed strata become thinner, but the window above corank 3
opens up.  The rank-generic statement is the honest induction candidate, not a
claim that the rank-3 proof pattern transfers unchanged.
-/
import Mathlib
import Gtz.Design.RigidityBridge

namespace Gtz

/-- **The stress-free hinge at the corank-3 cell, rank-generic.**  Every
stress-free tie on `rank + 3` atoms at rank `rank` carries a parallel pair.
At `rank = 3` this is `Gtz.StressFreeHingeHoldsSixThree` on the nose
(`stressFreeHingeHoldsAtCorankThree_three_iff_sixThree` below is `Iff.rfl`). -/
def StressFreeHingeHoldsAtCorankThree (rank : ℕ) : Prop :=
  ∀ design : WeightedDesign (rank + 3) rank,
    (∀ stress : Fin (rank + 3) → ℝ,
      (∑ label, stress label • atomMatrix (design.atom label)) = 0 →
        stress = 0) →
    IsTie design → HasParallelPair design

/-- **The definitional bridge.**  The rank-3 instance of the corank-three
hinge is the tree's frontier Prop — not equivalent to it, EQUAL to it up to
kernel reduction of the numeral `3 + 3`. -/
theorem stressFreeHingeHoldsAtCorankThree_three_iff_sixThree :
    StressFreeHingeHoldsAtCorankThree 3 ↔ StressFreeHingeHoldsSixThree :=
  Iff.rfl

/-- **The capstone, re-exported rank-generically.**  The rigidity-bridge
reduction of the hinge — three chart-free classes plus the two chart
obligations — delivers the corank-three hinge at rank 3 verbatim. -/
theorem stressFreeHingeHoldsAtCorankThree_three_of_bothCharts
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hchartFree : ∀ lines ∈ chartFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines))
    (hthreeLinesChart : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide →
      DirectionChartIsTieFree (threeLinesDirection slide))
    (hkFourChart : DirectionChartIsTieFree kFourDirection) :
    StressFreeHingeHoldsAtCorankThree 3 :=
  stressFreeHingeHoldsSixThree_of_bothCharts hcomplete hchartFree
    hthreeLinesChart hkFourChart

end Gtz
