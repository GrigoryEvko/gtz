/-
# The chart-value-ZERO locus

Chart value zero is the one level at which the chart-to-quadric bridge of
`Gtz.Quantitative.ChartMultiplierSplit` is EXACT: off it the manufactured
multiplier misses the design-side quadric law by an order-one amount (deviation
`2.000` at the octahedron, `0.500` at the D3 root design [numeric, outside Lean,
not mechanized]), and at it every atom lands on the central quadric at level
exactly one.  This file mechanizes what is true about that level set, and states
precisely what a compactness or deformation argument would have to deliver for it
to decide the `(6,3)` cell.

## What is proved here

* **THE VALUE-ZERO SATURATION EXCLUSION**, `not_saturatedAtom_of_chartValueZero`.
  No atom of a chart stationarity datum at value zero lies in every active subset,
  as soon as the datum carries two atoms.  This completes a trichotomy the tree
  had two thirds of.  The shipped `sq_value_add_weight_of_saturatedAtom` says a
  saturated atom's eigenvalue `value + t_c` is idempotent, hence `0` or `1`.  At a
  NEGATIVE value the first root survives and the second dies, which is the shipped
  `weight_eq_neg_value_of_saturatedAtom_of_negativeValue` -- an equation, not an
  exclusion, and the file that owns it says so.  At value `1/2` the second root
  survives, which is the shipped two-atom witness
  `exists_isChartStationaryData_saturatedAtom_value_add_weight_eq_one`.  At value
  ZERO the first root asks for `t_c = 0` against strict interiority and the second
  asks for `t_c = 1` against a second positive weight, so BOTH die and saturation
  is impossible outright.  Both hypotheses are needed and the tree witnesses each:
  at value `1/2` the second root is attained by the shipped two-atom datum, and at
  a negative value the first is exactly the shipped equation.  The census-facing
  form is `not_hasSaturatedAtom_of_chartValueZero`, which removes from a covering
  class census precisely the classes with a saturated atom.

  THIS DOES NOT CLOSE THE CRUX-SIDE WALL.  A crux has value strictly NEGATIVE, never
  zero, and there the law remains the equation it always was; the recorded chart-side
  attempts at a saturated-atom exclusion AT A CRUX stand refuted exactly as before.
  What is new is a different regime -- the one the bridge is exact on.

* **THE TIE HALF**, `not_posDef_subsetSum_sub_one_of_chartValueZeroAdmissible`.
  Admissibility at level zero -- every `rank`-subset carrying a supported unit
  probe of nonpositive chart quotient -- forbids a STRICT dominator, at every size
  and rank.  The route is determinant-free on the design side: a strict dominator
  makes the projection block positive semidefinite (it dominates) with nonzero
  determinant (it dominates strictly, and
  `det_projectionBlock_sub_weightDiagonal` rescales the design gap's determinant
  by the positive weight product), hence positive definite, hence strictly
  positive on the probe's nonzero restriction -- contradicting the cap.

* **THE BRIDGE PACKAGE**, `exists_multiplier_of_chartValueZero`, collecting the
  three shipped bridge conclusions and the gap-trace law into one existential, and
  `one_le_leverageOf_of_chartValueZero`: at value zero every atom is heavy in the
  NON-STRICT sense for free, because the manufactured multiplier is positive
  semidefinite of trace one and the shipped `quadForm_le_trace_mul_dotProduct`
  turns the quadric law `g_c^T Lambda g_c = 1` into `1 <= |g_c|^2`.  So
  `Gtz.AllHeavy` at a value-zero limit is only the STRICT upgrade.

* **THE COMPACTNESS INTERFACE**, `IsChartValueZeroLimit`, with the two leaves
  `HasChartValueZeroLimitAtEveryCrux` and `HasNoChartValueZeroLimit` and the
  mechanized composition into `IsEmpty Gtz.SixThreeCrux` and `Gtz.GtzWeighted 6 3`.
  Route C becomes ONE named obligation rather than a research direction.

* **ROUTE C's SECOND LEAF IS THE SHIPPED HINGE**,
  `hasNoChartValueZeroLimit_of_hingeHoldsAtSize`.  A value-zero limit object is an
  exact tie (`isTie_of_isChartValueZeroLimit`, the two halves being the interface's
  domination field and the admissibility exclusion above) with no parallel pair, so
  `Gtz.HingeHoldsAtSize 6 3` empties the class.  This is a reduction of the second
  leaf to a statement the tree already names and already knows to be FALSE one size
  down (`Gtz.not_hingeHoldsAtSize_five_three`), so no size-generic argument reaches
  it.

## What is NOT proved, and the negative that says why

The quadric-side kills DO NOT FIRE at value zero and this file does not pretend
otherwise.  `Gtz.one_le_value_of_saturatedAtom`,
`Gtz.rank_le_value_of_disjointPair_activeSubsetImage` and
`Gtz.three_le_card_activeSubsetImage_sixThree` all consume the full
`Gtz.IsQuadricStationaryData` bundle, and the bridge manufactures only three of
its conclusions -- the quadric law, the trace and semidefiniteness -- never its
`atomStationarity`, `activeSubset_card`, `tightDir_isEigenvector` or
`activeWeight_sum_one` fields.  `exists_chartValueZero_bridge_and_dominates`
records the consequence as a theorem: a genuine `(6,3)` weighted design carries a
value-zero stationarity datum, feeds the bridge, receives the whole package, and
DOMINATES.  Value zero plus the bridge cannot on its own contradict anything.

`exists_chartValueZero_stationary_allHeavy_hasParallelPair` records the second
negative: with parallel-freeness deleted the interface is INHABITED, by the
shipped split-tetrahedron datum whose atoms `2 ~ 3` and `4 ~ 5` repeat.  So the
target is the PARALLEL-FREE part of the value-zero locus and nothing weaker.

The first leaf is untouched here and is the hard one.  Every crux is a global
minimiser of one and the same `Gtz.chartObjective` over one and the same compact
domain, so all cruxes carry the same value in `[-4/27, 0)` and no minimising
sequence has values tending to zero; producing a value-zero limit is a deformation
argument, not a subsequence extraction.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.DiamondLeverage
import Gtz.Design.StratumEmptinessLedger
import Gtz.Quantitative.ChartInstances
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The saturation exclusion at value zero -/

/-- **A saturated atom at value zero would carry the whole weight.**  Its
eigenvalue `value + t_c` is idempotent by `sq_value_add_weight_of_saturatedAtom`,
so at `value = 0` the weight squares to itself and is `0` or `1`; strict
interiority rules out `0`. -/
theorem weight_eq_one_of_saturatedAtom_of_chartValueZero
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) {atomLabel : Fin size}
    (hsaturated : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel) :
    weight atomLabel = 1 := by
  have hsquare := sq_value_add_weight_of_saturatedAtom hdata hsaturated
  have hpositive := hdata.weight_pos atomLabel
  nlinarith [hsquare, hpositive]

/-- **NO ATOM OF A VALUE-ZERO DATUM IS SATURATED.**  The exclusion the negative
value branch does not give: there the shipped law only pins a saturated atom's
weight at `-value`, and `Gtz.Quantitative.ChartDisjointBlockExclusion`'s header
records that this is rigidity rather than exclusion.  At value zero both roots of
the idempotence law die -- `t_c = 0` against strict interiority, `t_c = 1` against
any second positive weight -- so saturation is impossible.

The hypothesis `2 <= size` cannot be dropped: at one atom the whole weight sits on
it and the datum is the degenerate full-rank chart. -/
theorem not_saturatedAtom_of_chartValueZero
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) (htwoAtoms : 2 ≤ size) (atomLabel : Fin size) :
    ¬ ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel := by
  intro hsaturated
  have hwhole := weight_eq_one_of_saturatedAtom_of_chartValueZero hdata hsaturated
  obtain ⟨otherAtom, hdistinct⟩ : ∃ otherAtom : Fin size, otherAtom ≠ atomLabel :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) atomLabel
  have hpairMass : weight atomLabel + weight otherAtom
      ≤ ∑ atomIndex : Fin size, weight atomIndex := by
    have hpairSum : ∑ atomIndex ∈ ({atomLabel, otherAtom} : Finset (Fin size)), weight atomIndex
        = weight atomLabel + weight otherAtom :=
      Finset.sum_pair (Ne.symm hdistinct)
    rw [← hpairSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun atomIndex _ _ => (hdata.weight_pos atomIndex).le
  rw [hdata.weight_sum_one, hwhole] at hpairMass
  linarith [hdata.weight_pos otherAtom]

/-- The positive reading, in the shape a covering census consumes: at value zero
every atom is left out of at least one active subset. -/
theorem exists_notMem_activeSubset_of_chartValueZero
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) (htwoAtoms : 2 ≤ size) (atomLabel : Fin size) :
    ∃ activeLabel ∈ activeSet, atomLabel ∉ activeSubset activeLabel := by
  by_contra hnone
  refine not_saturatedAtom_of_chartValueZero hdata htwoAtoms atomLabel fun activeLabel hmember => ?_
  by_contra hmiss
  exact hnone ⟨activeLabel, hmember, hmiss⟩

/-- **THE CENSUS-FACING FORM.**  At value zero the active family has no saturated
atom, in the shipped combinatorial vocabulary the `(6,3)` covering census consumes.
The filter is exactly the one a crux's own NEGATIVE value cannot apply: there the
saturated classes survive with their weight pinned at `-value`, and the census must
carry them. -/
theorem not_hasSaturatedAtom_of_chartValueZero
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) (htwoAtoms : 2 ≤ size) {family : Finset (Finset (Fin size))}
    (hfamily : IsActiveFamily activeSet activeSubset family) :
    ¬ HasSaturatedAtom family := by
  rintro ⟨atomLabel, hsaturated⟩
  exact not_saturatedAtom_of_chartValueZero hdata htwoAtoms atomLabel
    fun activeLabel hactive => hsaturated _ (mem_of_isActiveFamily hfamily hactive)

/-- **The negative-value companion, read at the sharp window.**  The shipped
`Gtz.SixThreeCrux.weight_eq_neg_chartObjective_of_saturatedAtom` pins a saturated
atom's weight at `-chartObjective`, and the shipped
`Gtz.SixThreeCrux.neg_four_div_twentySeven_le_chartObjective` confines the crux's
value to `[-4/27, 0)`, so the weight sits in `(0, 4/27]`.  Composition of two
shipped facts, not a rederivation of either.

The value-zero exclusion above is the limiting case: as the value rises to zero the
window closes on the endpoint that strict interiority forbids. -/
theorem SixThreeCrux.weight_mem_window_of_saturatedAtom (crux : SixThreeCrux)
    {atomLabel : Fin 6}
    (hsaturated : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      atomLabel ∈ block) :
    0 < crux.design.weight atomLabel ∧ crux.design.weight atomLabel ≤ 4 / 27 := by
  have hweight := crux.weight_eq_neg_chartObjective_of_saturatedAtom hsaturated
  have hwindow := crux.neg_four_div_twentySeven_le_chartObjective
  exact ⟨crux.design.weight_pos atomLabel, by rw [hweight]; linarith⟩

/-- The `(7,3)` twin, at that cell's own window `-10/77`.  Both ingredients are
shipped and size-generic, so the composition costs nothing.  After
`Gtz.gtzWeighted_six_three_iff_seven_three` the two cells are equivalent, so this is
a reading of the same fact and not a second result. -/
theorem SevenThreeCrux.weight_mem_window_of_saturatedAtom (crux : SevenThreeCrux)
    {atomLabel : Fin 7}
    (hsaturated : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      atomLabel ∈ block) :
    0 < crux.design.weight atomLabel ∧ crux.design.weight atomLabel ≤ 10 / 77 := by
  have hweight := crux.weight_eq_neg_chartObjective_of_saturatedAtom hsaturated
  have hwindow := crux.neg_ten_div_seventySeven_le_chartObjective
  exact ⟨crux.design.weight_pos atomLabel, by rw [hweight]; linarith⟩

/-! ## The bridge at value zero -/

/-- **Value zero makes every atom heavy, non-strictly.**  The manufactured
multiplier is positive semidefinite of trace one and pins every atom's quadratic
form at one, so `quadForm_le_trace_mul_dotProduct` reads `1 <= 1 * |g_c|^2`.

This is NOT `Gtz.AllHeavy`, which is strict; strictness would need the multiplier
to have no unit eigenvector at eigenvalue one, i.e. to have rank above one. -/
theorem one_le_leverageOf_of_chartValueZero (design : WeightedDesign size rank)
    (hdata : IsChartStationaryData rank (projectionOfDesign design) design.weight 0
      activeSet activeSubset activeWeight tightDir) (atomLabel : Fin size) :
    1 ≤ leverageOf (design.atom atomLabel) := by
  have hquadric :=
    quadricLaw_of_chartQuadricMultiplier_of_value_zero design rfl rfl hdata atomLabel
  have htrace := trace_chartQuadricMultiplier_of_value_zero design rfl hdata
  have hposSemidef := posSemidef_chartQuadricMultiplier
    (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata) (scaledAtomRows design)
  have hbound := quadForm_le_trace_mul_dotProduct hposSemidef (design.atom atomLabel)
  rw [hquadric, htrace, one_mul] at hbound
  rw [leverageOf, ← dotProduct_self_eq_sum_sq]
  exact hbound

/-- **AT VALUE ZERO ALL-HEAVINESS IS EXACTLY THE ABSENCE OF UNIT ATOMS.**  The
non-strict half is free, so the only content left in `Gtz.AllHeavy` there is that no
atom has leverage exactly one -- equivalently, that no atom is a unit eigenvector of
the manufactured multiplier at eigenvalue one. -/
theorem allHeavy_iff_forall_leverageOf_ne_one_of_chartValueZero
    (design : WeightedDesign size rank)
    (hdata : IsChartStationaryData rank (projectionOfDesign design) design.weight 0
      activeSet activeSubset activeWeight tightDir) :
    AllHeavy design ↔ ∀ atomLabel : Fin size, leverageOf (design.atom atomLabel) ≠ 1 :=
  ⟨fun hheavy atomLabel => (hheavy atomLabel).ne',
    fun hnoUnit atomLabel =>
      lt_of_le_of_ne (one_le_leverageOf_of_chartValueZero design hdata atomLabel)
        (Ne.symm (hnoUnit atomLabel))⟩

/-- **THE VALUE-ZERO PACKAGE.**  Everything the chart hands the design side at
value zero, in one existential: a positive semidefinite multiplier of trace one
whose central quadric carries every atom at level exactly one, and whose gap trace
against EVERY `rank`-subset is `rank - 1`.

Read it at its size.  These are CONCLUSIONS of `Gtz.IsQuadricStationaryData` at
design value one, not that structure -- no active family, no tight eigenvectors,
no atom stationarity -- which is exactly why the quadric-side exclusions cannot be
invoked against it.  The gap-trace clause is the reason the one-subset kill
`Gtz.not_isCriticalMultiplierAt` is unreachable too: `rank - 1 = 2` at rank three
is never zero, so a chart-manufactured multiplier never annihilates a triple gap. -/
theorem exists_multiplier_of_chartValueZero (design : WeightedDesign size rank)
    (hdata : IsChartStationaryData rank (projectionOfDesign design) design.weight 0
      activeSet activeSubset activeWeight tightDir) :
    ∃ multiplier : Matrix (Fin rank) (Fin rank) ℝ,
      multiplier.PosSemidef
        ∧ Matrix.trace multiplier = 1
        ∧ (∀ atomLabel : Fin size,
            design.atom atomLabel ⬝ᵥ (multiplier *ᵥ design.atom atomLabel) = 1)
        ∧ (∀ chosenSubset : Finset (Fin size), chosenSubset.card = rank →
            Matrix.trace (multiplier * (subsetSum design chosenSubset - 1)) = (rank : ℝ) - 1) :=
  ⟨chartQuadricMultiplier (scaledAtomRows design)
      (chartMultiplierAssembly activeSet activeWeight tightDir),
    posSemidef_chartQuadricMultiplier
      (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata) _,
    trace_chartQuadricMultiplier_of_value_zero design rfl hdata,
    fun atomLabel => quadricLaw_of_chartQuadricMultiplier_of_value_zero design rfl rfl hdata
      atomLabel,
    fun chosenSubset hcard =>
      trace_mul_gap_of_chartQuadricMultiplier design rfl rfl hdata chosenSubset hcard⟩

/-! ## Admissibility at level zero forbids a strict dominator -/

/-- The chart gap's block along an injective selection is the projection block
minus the selected weight diagonal.  The shipped
`Gtz.chartPointGap_submatrix_chartPointOfDesign` is the same computation for a
design's chart point along an order embedding; this is the generic statement, for
any chart, any weights and any injective selection, which is what the transport
below needs. -/
theorem submatrix_chartStationaryGap (chartMatrix : Matrix (Fin size) (Fin size) ℝ)
    (weights : Fin size → ℝ) {pick : Fin rank → Fin size}
    (hinjective : Function.Injective pick) :
    (chartStationaryGap chartMatrix weights).submatrix pick pick
      = chartMatrix.submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => weights (pick selectedIndex)) := by
  ext leftIndex rightIndex
  simp only [chartStationaryGap, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.diagonal_apply]
  rcases eq_or_ne leftIndex rightIndex with rfl | hdistinct
  · rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hdistinct, if_neg fun heq => hdistinct (hinjective heq)]

/-- **The square transpose flip, at the level of determinants.**  For a square
matrix the two Gram gaps have equal determinant, because
`Matrix.det_one_sub_mul_comm` exchanges the two products and the two sign factors
are the same. -/
theorem det_gramGap_eq_det_transposeGap (square : Matrix (Fin rank) (Fin rank) ℝ) :
    (square * squareᵀ - 1).det = (squareᵀ * square - 1).det := by
  rw [← neg_sub (1 : Matrix (Fin rank) (Fin rank) ℝ) (square * squareᵀ),
    ← neg_sub (1 : Matrix (Fin rank) (Fin rank) ℝ) (squareᵀ * square),
    Matrix.det_neg, Matrix.det_neg, Matrix.det_one_sub_mul_comm]

/-- **NO STRICT DOMINATOR UNDER ADMISSIBILITY AT LEVEL ZERO.**  If every
`rank`-subset carries a supported unit probe whose chart quotient is at most zero,
then no `rank`-subset dominates strictly.

A strict dominator would make the projection block positive semidefinite -- it
dominates -- with nonzero determinant, since
`det_projectionBlock_sub_weightDiagonal` rescales the design gap's determinant by
the strictly positive weight product and the square transpose flip identifies the
two Gram gaps.  A positive semidefinite block of nonzero determinant is positive
definite, so it is strictly positive on the probe's restriction, which is nonzero
because the probe is a unit vector supported on the subset.  That contradicts the
cap.  Nothing here is specific to `(6,3)` and nothing needs the stationarity
bundle: admissibility alone does it. -/
theorem not_posDef_subsetSum_sub_one_of_chartValueZeroAdmissible
    (design : WeightedDesign size rank)
    (hadmissible : IsChartArgmaxValue rank (projectionOfDesign design) design.weight 0)
    {selected : Finset (Fin size)} (hcard : selected.card = rank) :
    ¬ (subsetSum design selected - 1).PosDef := by
  intro hstrict
  obtain ⟨probe, hunit, hsupport, hquotient⟩ := hadmissible selected hcard
  set pick : Fin rank → Fin size := fun selectedIndex => selected.orderEmbOfFin hcard selectedIndex
    with hpick
  have hinjective : Function.Injective pick := (selected.orderEmbOfFin hcard).injective
  have himage : Finset.image pick Finset.univ = selected := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hpick, Finset.range_orderEmbOfFin]
  have hblockPosSemidef :=
    (dominates_iff_posSemidef_projectionBlock_finset design selected hcard).mp hstrict.posSemidef
  have hgapDetPos : 0 < (subsetSum design selected - 1).det := hstrict.det_pos
  have hweightProductPos : 0 < ∏ selectedIndex, design.weight (pick selectedIndex) :=
    Finset.prod_pos fun selectedIndex _ => design.weight_pos (pick selectedIndex)
  have hgramDet : (selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ - 1).det
      = (subsetSum design selected - 1).det := by
    rw [det_gramGap_eq_det_transposeGap, transpose_mul_selectedAtomRows design pick hinjective,
      himage]
  have hblockDet : ((projectionOfDesign design).submatrix pick pick
      - Matrix.diagonal (fun selectedIndex => design.weight (pick selectedIndex))).det ≠ 0 := by
    rw [det_projectionBlock_sub_weightDiagonal design pick, hgramDet]
    positivity
  have hblockPosDef := hblockPosSemidef.posDef_iff_det_ne_zero.mpr hblockDet
  have hrestrictedNorm := dotProduct_self_pick_eq_of_support pick hinjective himage hsupport
  rw [hunit] at hrestrictedNorm
  have hrestrictedNe : (fun selectedIndex => probe (pick selectedIndex)) ≠ 0 := by
    intro hvanishes
    rw [hvanishes] at hrestrictedNorm
    simp only [dotProduct_zero] at hrestrictedNorm
    exact absurd hrestrictedNorm (by norm_num)
  have hpositiveForm := (Matrix.posDef_iff_dotProduct_mulVec.mp hblockPosDef).2 hrestrictedNe
  rw [star_trivial] at hpositiveForm
  have htransport := dotProduct_mulVec_submatrix_pick_eq_of_support
    (chartStationaryGap (projectionOfDesign design) design.weight) pick hinjective himage hsupport
  rw [submatrix_chartStationaryGap (projectionOfDesign design) design.weight hinjective]
    at htransport
  rw [htransport] at hpositiveForm
  linarith

/-! ## The compactness interface at `(6,3)` -/

/-- **THE OBJECT A DEFORMATION ARGUMENT MUST PRODUCE.**  A `(6,3)` weighted design
sitting exactly on the chart-value-zero level set, in the strongest shape a limit
of cruxes could carry.  Every field is load-bearing.

* The stationarity datum AT VALUE ZERO is the bridge's input; off zero the bridge
  fails audibly and the whole construction is about this level set.
* Admissibility at level zero -- no `rank`-subset beats the value -- is what
  forbids a strict dominator, and without it the class is satisfied at
  non-extremal points.
* A DOMINATING triple: domination is a closed condition, so a limit of designs
  whose margin rises to zero has margin exactly zero.  Together with admissibility
  this is the exact tie.
* `Gtz.AllHeavy`, inherited from `Gtz.SixThreeCrux.isAllHeavy`.  Only the STRICT
  half is a genuine demand; the non-strict half is free at value zero by
  `one_le_leverageOf_of_chartValueZero`.
* Parallel-freeness, inherited from `Gtz.SixThreeCrux.hasNoParallelPair`, and the
  ONLY field separating the class from the shipped value-zero inhabitant
  `Gtz.chartSplitSixDesign` -- see
  `exists_chartValueZero_stationary_allHeavy_hasParallelPair`. -/
def IsChartValueZeroLimit (design : WeightedDesign 6 3) : Prop :=
  (∃ (activeCount : ℕ) (activeSubset : Fin activeCount → Finset (Fin 6))
      (activeWeight : Fin activeCount → ℝ) (tightDir : Fin activeCount → (Fin 6 → ℝ)),
      IsChartStationaryData 3 (projectionOfDesign design) design.weight 0
        (Finset.univ : Finset (Fin activeCount)) activeSubset activeWeight tightDir)
    ∧ IsChartArgmaxValue 3 (projectionOfDesign design) design.weight 0
    ∧ (∃ chosenSubset : Finset (Fin 6), chosenSubset.card = 3 ∧ Dominates design chosenSubset)
    ∧ AllHeavy design
    ∧ ¬ HasParallelPair design

/-- **LEAF ONE, the deformation obligation.**  Stated, never assumed and never
proved.  What makes it hard is that every crux is a global minimiser of the SAME
`Gtz.chartObjective` over the SAME compact domain, so all cruxes carry one value in
`[-4/27, 0)` and no minimising sequence has values tending to zero: this is a
deformation statement, not a subsequence extraction. -/
def HasChartValueZeroLimitAtEveryCrux : Prop :=
  ∀ crux : SixThreeCrux, IsChartValueZeroLimit crux.design

/-- **LEAF TWO, route C's own target**: the parallel-free part of the `(6,3)`
value-zero locus is empty. -/
def HasNoChartValueZeroLimit : Prop :=
  ∀ design : WeightedDesign 6 3, ¬ IsChartValueZeroLimit design

/-- **THE TWO LEAVES EMPTY THE CRUX.** -/
theorem isEmpty_sixThreeCrux_of_chartValueZeroLimit
    (hdeformation : HasChartValueZeroLimitAtEveryCrux) (hempty : HasNoChartValueZeroLimit) :
    IsEmpty SixThreeCrux :=
  ⟨fun crux => hempty crux.design (hdeformation crux)⟩

/-- ... and therefore decide the cell, through the shipped hypothesis-free iff. -/
theorem gtzWeighted_six_three_of_chartValueZeroLimit
    (hdeformation : HasChartValueZeroLimitAtEveryCrux) (hempty : HasNoChartValueZeroLimit) :
    GtzWeighted 6 3 := by
  by_contra hfails
  exact (isEmpty_sixThreeCrux_of_chartValueZeroLimit hdeformation hempty).elim
    (nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three.mpr hfails).some

/-- **A VALUE-ZERO LIMIT IS AN EXACT TIE.**  Its domination field is the first half
of `Gtz.IsTie`; admissibility at level zero supplies the second through
`not_posDef_subsetSum_sub_one_of_chartValueZeroAdmissible`. -/
theorem isTie_of_isChartValueZeroLimit {design : WeightedDesign 6 3}
    (hlimit : IsChartValueZeroLimit design) : IsTie design :=
  ⟨hlimit.2.2.1, fun _chosenSubset hcard =>
    not_posDef_subsetSum_sub_one_of_chartValueZeroAdmissible design hlimit.2.1 hcard⟩

/-- **ROUTE C's SECOND LEAF IS THE SHIPPED HINGE.**  A value-zero limit is an exact
tie with no parallel pair, so `Gtz.HingeHoldsAtSize 6 3` empties the class outright.

This is a reduction, not a proof: the hinge is OPEN at size six, and
`Gtz.not_hingeHoldsAtSize_five_three` proves it FALSE at `(5,3)` on the diamond, so
no size-generic argument reaches leaf two.  What the reduction buys is that leaf
two is not a new question. -/
theorem hasNoChartValueZeroLimit_of_hingeHoldsAtSize (hhinge : HingeHoldsAtSize 6 3) :
    HasNoChartValueZeroLimit :=
  fun design hlimit => hlimit.2.2.2.2 (hhinge design (isTie_of_isChartValueZeroLimit hlimit))

/-- The whole route, assembled: the deformation leaf and the hinge decide the cell. -/
theorem gtzWeighted_six_three_of_chartValueZeroLimit_of_hinge
    (hdeformation : HasChartValueZeroLimitAtEveryCrux) (hhinge : HingeHoldsAtSize 6 3) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_chartValueZeroLimit hdeformation
    (hasNoChartValueZeroLimit_of_hingeHoldsAtSize hhinge)

/-- No atom of a value-zero limit is saturated in its own active family. -/
theorem not_saturatedAtom_of_isChartValueZeroLimit {design : WeightedDesign 6 3}
    (hlimit : IsChartValueZeroLimit design) (atomLabel : Fin 6) :
    ∃ (activeCount : ℕ) (activeSubset : Fin activeCount → Finset (Fin 6))
      (activeWeight : Fin activeCount → ℝ) (tightDir : Fin activeCount → (Fin 6 → ℝ)),
      IsChartStationaryData 3 (projectionOfDesign design) design.weight 0
          (Finset.univ : Finset (Fin activeCount)) activeSubset activeWeight tightDir
        ∧ ¬ ∀ activeLabel ∈ (Finset.univ : Finset (Fin activeCount)),
            atomLabel ∈ activeSubset activeLabel := by
  obtain ⟨activeCount, activeSubset, activeWeight, tightDir, hdata⟩ := hlimit.1
  exact ⟨activeCount, activeSubset, activeWeight, tightDir, hdata,
    not_saturatedAtom_of_chartValueZero hdata (by norm_num) atomLabel⟩

/-- The bridge package at a value-zero limit: the strict all-heaviness field is
the only part of `Gtz.AllHeavy` the interface actually has to demand. -/
theorem exists_multiplier_of_isChartValueZeroLimit {design : WeightedDesign 6 3}
    (hlimit : IsChartValueZeroLimit design) :
    ∃ multiplier : Matrix (Fin 3) (Fin 3) ℝ,
      multiplier.PosSemidef
        ∧ Matrix.trace multiplier = 1
        ∧ (∀ atomLabel : Fin 6,
            design.atom atomLabel ⬝ᵥ (multiplier *ᵥ design.atom atomLabel) = 1)
        ∧ ∀ atomLabel : Fin 6, 1 ≤ leverageOf (design.atom atomLabel) := by
  obtain ⟨activeCount, activeSubset, activeWeight, tightDir, hdata⟩ := hlimit.1
  obtain ⟨multiplier, hposSemidef, htrace, hquadric, _⟩ :=
    exists_multiplier_of_chartValueZero design hdata
  exact ⟨multiplier, hposSemidef, htrace, hquadric,
    fun atomLabel => one_le_leverageOf_of_chartValueZero design hdata atomLabel⟩

/-! ## The two negatives -/

/-- **THE BRIDGE CANNOT BITE AT VALUE ZERO.**  A genuine `(6,3)` weighted design
carries a value-zero stationarity datum, receives the whole bridge package, and
DOMINATES.  So no composition of the three bridge conclusions with the quadric-side
exclusions can contradict anything at value zero, and route C's payoff is not
available in advance. -/
theorem exists_chartValueZero_bridge_and_dominates :
    ∃ (design : WeightedDesign 6 3) (activeSubset : Fin 12 → Finset (Fin 6))
      (activeWeight : Fin 12 → ℝ) (tightDir : Fin 12 → (Fin 6 → ℝ))
      (multiplier : Matrix (Fin 3) (Fin 3) ℝ),
      IsChartStationaryData 3 (projectionOfDesign design) design.weight 0
          (Finset.univ : Finset (Fin 12)) activeSubset activeWeight tightDir
        ∧ multiplier.PosSemidef
        ∧ Matrix.trace multiplier = 1
        ∧ (∀ atomLabel : Fin 6,
            design.atom atomLabel ⬝ᵥ (multiplier *ᵥ design.atom atomLabel) = 1)
        ∧ ∃ chosenSubset : Finset (Fin 6),
            chosenSubset.card = 3 ∧ Dominates design chosenSubset := by
  obtain ⟨multiplier, hposSemidef, htrace, hquadric, _⟩ :=
    exists_multiplier_of_chartValueZero chartSplitSixDesign
      chartSplitSixDesign_isChartStationaryData
  exact ⟨chartSplitSixDesign, chartSplitSixSubset, chartSplitSixMultiplierWeight,
    chartSplitSixTightDir, multiplier, chartSplitSixDesign_isChartStationaryData,
    hposSemidef, htrace, hquadric, chartSplitSixDesign_isTie.1⟩

/-- **WHERE THE SIZE-GENERICITY OBSTRUCTION BITES, EXACTLY.**  One size down the
class "exact tie, all-heavy, no parallel pair" is INHABITED, by the shipped diamond
`M(K4 - e)`: all three properties are theorems of the tree
(`Gtz.diamondDesign_isTie`, `Gtz.diamondDesign_allHeavy`,
`Gtz.not_hasParallelPair_diamondDesign`), which is exactly why
`Gtz.not_hingeHoldsAtSize_five_three` holds.

The consequence for route C's second leaf is sharp and worth stating.  Any argument
that emptied `IsChartValueZeroLimit` using ONLY the tie, all-heaviness and
parallel-freeness would prove a statement that is false one size down, so no such
argument exists.  Whatever strength the leaf has beyond the plain hinge must come
from the two fields the diamond is not known to carry: the value-zero chart
stationarity datum and admissibility at level zero.  Those are where any attempt
should be aimed. -/
theorem exists_isTie_allHeavy_not_hasParallelPair_fiveThree :
    ∃ design : WeightedDesign 5 3, IsTie design ∧ AllHeavy design ∧ ¬ HasParallelPair design :=
  ⟨diamondDesign, diamondDesign_isTie, diamondDesign_allHeavy, not_hasParallelPair_diamondDesign⟩

/-- **PARALLEL-FREENESS IS INDISPENSABLE.**  Delete it from the interface and the
class is INHABITED: the shipped split-tetrahedron design is a genuine `(6,3)`
weighted design with a value-zero stationarity datum on twelve active triples, an
exact tie, and all six leverages equal to three -- and its atoms `2 ~ 3` and
`4 ~ 5` repeat a tetrahedron direction.

The admissibility field is not asserted here, so this witnesses inhabitation of the
interface's other four demands and not of the interface itself. -/
theorem exists_chartValueZero_stationary_allHeavy_hasParallelPair :
    ∃ (design : WeightedDesign 6 3) (activeSubset : Fin 12 → Finset (Fin 6))
      (activeWeight : Fin 12 → ℝ) (tightDir : Fin 12 → (Fin 6 → ℝ)),
      IsChartStationaryData 3 (projectionOfDesign design) design.weight 0
          (Finset.univ : Finset (Fin 12)) activeSubset activeWeight tightDir
        ∧ (∃ chosenSubset : Finset (Fin 6), chosenSubset.card = 3 ∧ Dominates design chosenSubset)
        ∧ AllHeavy design
        ∧ HasParallelPair design := by
  refine ⟨chartSplitSixDesign, chartSplitSixSubset, chartSplitSixMultiplierWeight,
    chartSplitSixTightDir, chartSplitSixDesign_isChartStationaryData,
    chartSplitSixDesign_isTie.1,
    splitTetraDesign_allHeavy (1 / 8) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    2, 3, 1, by decide, ?_⟩
  funext coord
  simp only [chartSplitSixDesign, splitTetraDesign_atom, splitTetraAtom, splitTetraDirIndex,
    one_smul]
  congr 1

end Gtz
