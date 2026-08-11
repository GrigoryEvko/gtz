import Mathlib
import Gtz.Quantitative.ChartFloorAtomSpan
import Gtz.Quantitative.ZeroLeakCollinearClosure
import Gtz.Quantitative.ZeroLeakDependency

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The zero-leak branch, closed at rank three

Three landed modules meet here and the composition is short.

* `Gtz/Quantitative/ChartFloorAtomSpan.lean` supplies the master identity, the row
  law that kills every projected tight direction at an atom on the weight floor,
  and the closing theorem forbidding the projected tight directions from being
  collinear inside the open value window.
* `Gtz/Quantitative/ZeroLeakCollinearClosure.lean` supplies the rank-three
  rigidity that turns two floor atoms into one line.
* `Gtz/Quantitative/ZeroLeakDependency.lean` supplies the fibre-kernel step, that a
  vector killed by the chart is killed by the fibre map.  ** IT IS CONSUMED HERE
  AND NOT RESTATED: that theorem was proved twice independently with the same
  statement, and only one copy survives. **

The composition runs: a zero-leak tight direction is supported at TWO DISTINCT
atoms (a single supported atom would make its direction the zero vector, which a
parallel-free design does not carry); its support sits on the weight floor; the row
law then kills every projected tight direction at both of those atoms; the rigidity
makes them all multiples of one normal; and the closing theorem forbids that.

## The satisfiability caveat, which is the whole honest content of this file

`Gtz.false_of_two_floorAtoms` and `Gtz.false_of_zeroLeak` carry BOTH `value < 0` and
`-1/size < value`.  ** THE UNIQUE LANDED NEGATIVE-VALUE `(6,3)` STATIONARITY DATUM,
`Gtz.chartTwoBlockTripleProjection_isChartStationaryData`, SITS AT `value = -1/6`
EXACTLY: it clears the first and FAILS THE SECOND BY EQUALITY. **  So the hypothesis
bundle of the general closure has NO EXHIBITED INHABITANT AT ANY CELL, and the crux
corollary is vacuous if the conjecture holds.  Closing a branch of a case analysis
over a conjecturally empty set makes the residual finite and named; it is not
evidence about the conjecture, and the ledger does not move.

Building a rank-three chart stationarity datum at a value strictly inside
`(-1/size, 0)` would settle whether any of this has an instance.  Nobody has one.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}

/-- The coordinates of the fibre image of an ambient vector. -/
theorem transposeScaledAtomRows_mulVec_apply {rank : ℕ} (design : WeightedDesign size rank)
    (ambient : Fin size → ℝ) (coordinate : Fin rank) :
    ((scaledAtomRows design)ᵀ *ᵥ ambient) coordinate
      = ∑ atomIndex : Fin size, Real.sqrt (design.weight atomIndex)
          * design.atom atomIndex coordinate * ambient atomIndex := by
  show (fun atomIndex => (scaledAtomRows design)ᵀ coordinate atomIndex) ⬝ᵥ ambient = _
  simp only [dotProduct, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hentry : scaledAtomRows design atomIndex coordinate
      = Real.sqrt (design.weight atomIndex) * design.atom atomIndex coordinate := by
    have := congrFun (scaledAtomRows_row design atomIndex) coordinate
    simpa using this
  rw [hentry]

/-- **A ZERO-LEAK TIGHT DIRECTION IS SUPPORTED AT TWO DISTINCT ATOMS.**  A single
supported atom would make its direction the zero vector, which a parallel-free
design does not carry. -/
theorem exists_ne_supported_of_zeroLeak
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData 3 (projectionOfDesign design) design.weight value
      activeSet activeSubset activeWeight tightDir)
    (hnegative : value < 0) {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hzeroLeak : ∀ atomIndex : Fin size, atomIndex ∉ activeSubset activeLabel →
      (projectionOfDesign design *ᵥ tightDir activeLabel) atomIndex = 0) :
    ∃ first second : Fin size, first ≠ second
      ∧ tightDir activeLabel first ≠ 0 ∧ tightDir activeLabel second ≠ 0 := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hunit := hdata.tightDir_unit activeLabel hmem
  have hexists : ∃ atomIndex : Fin size, tightDir activeLabel atomIndex ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [show tightDir activeLabel = 0 from funext hall, dotProduct_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨support, hsupport⟩ := hexists
  have honly : ∀ other : Fin size, other ≠ support → tightDir activeLabel other = 0 := by
    intro other hother
    by_contra hnonzero
    exact hsupport (hcontra other support hother hnonzero)
  have hkernel := projection_mulVec_eq_zero_of_zeroLeak hdata hnegative hmem hzeroLeak
  have hfibre := transposeScaledAtomRows_mulVec_eq_zero_of_projectionOfDesign_mulVec_eq_zero
    design hkernel
  have hatomZero : design.atom support = 0 := by
    funext coordinate
    show design.atom support coordinate = (0 : ℝ)
    have hcoord := transposeScaledAtomRows_mulVec_apply design (tightDir activeLabel) coordinate
    rw [congrFun hfibre coordinate] at hcoord
    have hcollapse : ∑ atomIndex : Fin size, Real.sqrt (design.weight atomIndex)
        * design.atom atomIndex coordinate * tightDir activeLabel atomIndex
        = Real.sqrt (design.weight support) * design.atom support coordinate
            * tightDir activeLabel support := by
      refine Finset.sum_eq_single support ?_ ?_
      · intro other _ hother
        rw [honly other hother, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_univ support) hnot
    rw [hcollapse] at hcoord
    have hsqrt : Real.sqrt (design.weight support) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (design.weight_pos support))
    rcases mul_eq_zero.mp hcoord.symm with hleft | hright
    · exact (mul_eq_zero.mp hleft).resolve_left hsqrt
    · exact absurd hright hsupport
  have hthree : 3 ≤ size := by
    have hcard := hdata.activeSubset_card activeLabel hmem
    have hle := Finset.card_le_univ (activeSubset activeLabel)
    rw [hcard, Fintype.card_fin] at hle
    exact hle
  obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_fin]; omega) support
  exact hsimple ⟨other, support, 0, hother, by rw [hatomZero, zero_smul]⟩

/-- **THE CLOSURE.**  A chart stationarity datum carried by a parallel-free
rank-three design, at a value strictly inside the shipped window, has no two
distinct atoms at the weight floor.

The floor-atom row law kills the two coordinates, the rank-three rigidity turns
that into collinearity, and the closing theorem does the rest. -/
theorem false_of_two_floorAtoms
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData 3 (projectionOfDesign design) design.weight value
      activeSet activeSubset activeWeight tightDir)
    (hnegative : value < 0) (hinterior : -((size : ℝ))⁻¹ < value)
    {first second : Fin size} (hne : first ≠ second)
    (hfirstFloor : design.weight first = -value)
    (hsecondFloor : design.weight second = -value) :
    False := by
  obtain ⟨normal, hfixed, hunit, hcollinear⟩ :=
    exists_unitNormal_projected_tightDir_collinear design hsimple hdata hne
      (fun activeLabel hmem hpositive =>
        ⟨projection_mulVec_tightDir_eq_zero_of_weight_eq_neg_value hdata hfirstFloor hmem
          hpositive,
         projection_mulVec_tightDir_eq_zero_of_weight_eq_neg_value hdata hsecondFloor hmem
          hpositive⟩)
  exact false_of_projected_tightDir_collinear hdata hnegative hinterior normal hfixed hunit
    hcollinear

/-- **THE ZERO-LEAK BRANCH IS EMPTY AT RANK THREE.**  No active block of a chart
stationarity datum carried by a parallel-free rank-three design, at a value
strictly inside the shipped window, has a tight direction without off-block
residual.

This is the branch the campaign has carried as "the hard core" of the support-two
stratum.  It needs no case split on the support size, no multiplier, and no
enumeration. -/
theorem false_of_zeroLeak
    (design : WeightedDesign size 3) (hsimple : ¬ HasParallelPair design)
    {value : ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData 3 (projectionOfDesign design) design.weight value
      activeSet activeSubset activeWeight tightDir)
    (hnegative : value < 0) (hinterior : -((size : ℝ))⁻¹ < value)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hzeroLeak : ∀ atomIndex : Fin size, atomIndex ∉ activeSubset activeLabel →
      (projectionOfDesign design *ᵥ tightDir activeLabel) atomIndex = 0) :
    False := by
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    exists_ne_supported_of_zeroLeak design hsimple hdata hnegative hmem hzeroLeak
  exact false_of_two_floorAtoms design hsimple hdata hnegative hinterior hne
    (weight_eq_neg_value_of_zeroLeak hdata hnegative hmem hzeroLeak hfirst)
    (weight_eq_neg_value_of_zeroLeak hdata hnegative hmem hzeroLeak hsecond)

/-- **AT A `(6,3)` CRUX, NO ACTIVE BLOCK HAS A ZERO-LEAK TIGHT DIRECTION.**

Every hypothesis of the general closure is a crux field or a landed consequence of
one: the design is parallel-free by `hasNoParallelPair`, the value is negative by
`hasNegativeChartValue`, and the interior bound `-1/6 < value` is the shipped
`Gtz.neg_inv_size_lt_value_of_isChartStationaryData` read off the crux's own argmax
field.  Nothing is assumed about the size of the active family, the support of the
tight direction, or the orbit of the active set. -/
theorem SixThreeCrux.false_of_zeroLeak_tightDirection (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ} {selection : Finset (Fin 6) → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection)
    {block : Finset (Fin 6)}
    (hmem : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hzeroLeak : ∀ atomIndex : Fin 6, atomIndex ∉ block →
      ((chartPointOfDesign crux.design).chart *ᵥ selection block) atomIndex = 0) :
    False :=
  false_of_zeroLeak crux.design crux.hasNoParallelPair hdata crux.hasNegativeChartValue
    (neg_inv_size_lt_value_of_isChartStationaryData crux.design rfl crux.isChartArgmaxValue
      hdata)
    hmem hzeroLeak
end Gtz
