/-
# The deformation lane and the Grassmannian curvature of the chart objective

Two independent contributions of the `think-deform` rung, both stated here as
COMPILING drafts for `land-secondorder` / `land-sweep`.

## A. Route C's first leaf is the cell itself

`Gtz.HasChartValueZeroLimitAtEveryCrux` asks that EVERY crux's own design be a
`Gtz.IsChartValueZeroLimit`, and the third conjunct of that predicate is
`∃ chosenSubset, chosenSubset.card = 3 ∧ Gtz.Dominates design chosenSubset` --
verbatim the negation of the crux field `Gtz.SixThreeCrux.hasNoDominatingTriple`.
So leaf one alone empties the crux, leaf two is never consumed, and
`Gtz.gtzWeighted_six_three_of_chartValueZeroLimit` is a true theorem with a
vacuous second hypothesis.  `leafOne_iff_gtzWeighted_six_three` below records the
equivalence in the kernel.

This is NOT a defect of route C's mathematics -- the value-zero locus results in
`Gtz.Quantitative.ChartValueZeroLocus` stand -- it is a defect of the INTERFACE:
the deformation obligation was stated at the crux's own design instead of at a
deformed one.  The repair is in section D: state the deformation at a design
REACHED FROM the crux, not at the crux.

## B. A negative chart value forces stress-freeness (hypothesis-free)

The tree knows `Gtz.SixThreeCrux.stress_eq_zero` for a crux, which carries eight
fields.  Only ONE of them is used: a strictly negative chart value.
`stress_eq_zero_of_chartObjective_neg` is the sharp form, and it says that the
whole open sublevel set `{chartObjective < 0}` is conic-free -- which is what
makes the value-zero crossing of section D land on a stress-free-or-boundary
point, and what gives weight rigidity throughout that set.

## C. The trace identities and the GRASSMANNIAN CURVATURE (gap 10)

At any chart stationarity datum, with `Xi` the assembly:

    trace (Xi * W)  =  value                               (`trace_assembly_mul_chartStationaryGap`)
    trace (Xi * P)  =  value + 1/size                      (`trace_assembly_mul_projection`)

and for ANY curve `s ↦ P s` of projections with `P 0 = P`, velocity `B` and
acceleration `A` -- the constraint `A P + P A - A = -2 B²` being the second
derivative of `P² = P` -- the multiplier-averaged Grassmannian curvature is

    trace (Xi * A)  =  -2 * trace (Xi * (2 P - 1) * B²)    (`trace_mul_grassmannAcceleration`)

which depends on `B` alone: the free part of the acceleration cancels because
`Xi` commutes with `P`.  In a joint eigenbasis it is the DIAGONAL form
`2 Σ_{i ∈ range P, j ∈ ker P} (a_j - a_i) B_ij²`, and summing over an orthonormal
basis of velocities gives `rank - 1 - size * value` -- STRICTLY POSITIVE at a
crux (`> 2` at `(6,3)`, since the value is negative).  So the Grassmannian half
of the second-order test is on the STABILISING side on average; measured
verdicts are in the rung's report.

## D. The crossing, and exactly which fields it supplies

`exists_chartValueZero_of_path` is the intermediate value theorem against the
shipped `Gtz.continuous_chartObjectiveRaw`.  At the crossing point two of the
five `Gtz.IsChartValueZeroLimit` fields are FREE (`isChartArgmaxValue_chartObjective`
holds at every chart point, and the dominating triple is the zero threshold);
the stationarity field is not, and that is the honest residue of leaf one.
-/
import Mathlib
import Gtz.Quantitative.ChartValueZeroLocus
import Gtz.Quantitative.ChartSecondOrder
import Gtz.Reduction.StressConditionalWalk
import Gtz.Reduction.WeightFloorWindow
import Gtz.Quantitative.ChartSecondOrderStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## A. Route C's first leaf is the cell -/

/-- **LEAF ONE ALREADY EMPTIES THE CRUX.**  `Gtz.IsChartValueZeroLimit` demands a
DOMINATING triple; `Gtz.SixThreeCrux.hasNoDominatingTriple` forbids one.  So the
second leaf `Gtz.HasNoChartValueZeroLimit` is never consumed by
`Gtz.gtzWeighted_six_three_of_chartValueZeroLimit`. -/
theorem isEmpty_sixThreeCrux_of_hasChartValueZeroLimitAtEveryCrux
    (hleaf : HasChartValueZeroLimitAtEveryCrux) : IsEmpty SixThreeCrux := by
  refine ⟨fun crux => ?_⟩
  obtain ⟨chosenSubset, hcard, hdominates⟩ := (hleaf crux).2.2.1
  exact crux.hasNoDominatingTriple chosenSubset hcard hdominates

/-- The converse is vacuous quantification. -/
theorem hasChartValueZeroLimitAtEveryCrux_of_isEmpty (hempty : IsEmpty SixThreeCrux) :
    HasChartValueZeroLimitAtEveryCrux :=
  fun crux => (hempty.false crux).elim

/-- **LEAF ONE IS THE CELL.**  Not a reduction of `Gtz.GtzWeighted 6 3` but a
restatement of it, so no deformation argument can be BUILT against this
interface: producing it is exactly as hard as the conjecture. -/
theorem hasChartValueZeroLimitAtEveryCrux_iff_gtzWeighted_six_three :
    HasChartValueZeroLimitAtEveryCrux ↔ GtzWeighted 6 3 := by
  constructor
  · intro hleaf
    by_contra hfails
    exact (isEmpty_sixThreeCrux_of_hasChartValueZeroLimitAtEveryCrux hleaf).false
      (nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three.mpr hfails).some
  · intro hholds
    refine hasChartValueZeroLimitAtEveryCrux_of_isEmpty ⟨fun crux => ?_⟩
    exact (nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three.mp ⟨crux⟩) hholds

/-- The same collapse read on the second leaf: `Gtz.HasNoChartValueZeroLimit` is a
free rider in `Gtz.gtzWeighted_six_three_of_chartValueZeroLimit`. -/
theorem gtzWeighted_six_three_of_hasChartValueZeroLimitAtEveryCrux
    (hleaf : HasChartValueZeroLimitAtEveryCrux) : GtzWeighted 6 3 :=
  hasChartValueZeroLimitAtEveryCrux_iff_gtzWeighted_six_three.mp hleaf

/-! ## B. A negative chart value forces stress-freeness -/

/-- **A STRESSED `(6,3)` DESIGN HAS NONNEGATIVE CHART VALUE.**  The shipped
unconditional walk `Gtz.exists_dominating_sixThree_of_stress` produces a
dominating triple, and the zero threshold turns it into a chart bound. -/
theorem chartObjective_nonneg_of_stress (design : WeightedDesign 6 3)
    {stress : Fin 6 → ℝ} (hnonzero : stress ≠ 0)
    (hstress : (∑ atomIndex, stress atomIndex • atomMatrix (design.atom atomIndex)) = 0) :
    0 ≤ chartObjective (chartPointOfDesign design) := by
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_sixThree_of_stress design hnonzero hstress
  exact (zero_le_chartObjective_iff_exists_chartDominates (chartPointOfDesign design)).mpr
    ⟨selected, hcard, (dominates_iff_chartDominates design selected hcard).mp hdominates⟩

/-- **THE WHOLE NEGATIVE SUBLEVEL SET IS STRESS-FREE.**  Sharper than
`Gtz.SixThreeCrux.stress_eq_zero`, which consumes eight crux fields: only the
strictly negative chart value is used. -/
theorem stress_eq_zero_of_chartObjective_neg (design : WeightedDesign 6 3)
    (hnegative : chartObjective (chartPointOfDesign design) < 0)
    (stress : Fin 6 → ℝ)
    (hstress : (∑ atomIndex, stress atomIndex • atomMatrix (design.atom atomIndex)) = 0) :
    stress = 0 := by
  by_contra hnonzero
  exact absurd (chartObjective_nonneg_of_stress design hnonzero hstress) (not_le.mpr hnegative)

/-- No two atoms of a negative-value design are parallel. -/
theorem not_hasParallelPair_of_chartObjective_neg (design : WeightedDesign 6 3)
    (hnegative : chartObjective (chartPointOfDesign design) < 0) :
    ¬ HasParallelPair design :=
  not_hasParallelPair_of_no_stress design (stress_eq_zero_of_chartObjective_neg design hnegative)

/-- The six Veronese images of a negative-value design are a BASIS of the
symmetric forms: the real-only content of the cell, off the crux bundle. -/
theorem linearIndependent_veronese_of_chartObjective_neg (design : WeightedDesign 6 3)
    (hnegative : chartObjective (chartPointOfDesign design) < 0) :
    LinearIndependent ℝ fun atomIndex : Fin 6 => atomMatrix (design.atom atomIndex) := by
  rw [Fintype.linearIndependent_iff]
  intro stress hstress
  exact fun atomIndex =>
    congrFun (stress_eq_zero_of_chartObjective_neg design hnegative stress hstress) atomIndex

/-- Weight rigidity on the whole negative sublevel set. -/
theorem weight_unique_of_chartObjective_neg (design : WeightedDesign 6 3)
    (hnegative : chartObjective (chartPointOfDesign design) < 0)
    (candidateWeight : Fin 6 → ℝ)
    (hparseval :
      (∑ atomIndex, candidateWeight atomIndex • atomMatrix (design.atom atomIndex)) = 1) :
    candidateWeight = design.weight := by
  have hstress : (∑ atomIndex, (candidateWeight atomIndex - design.weight atomIndex)
      • atomMatrix (design.atom atomIndex)) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hparseval, design.isParseval, sub_self]
  have hzero := stress_eq_zero_of_chartObjective_neg design hnegative _ hstress
  funext atomIndex
  have hentry : candidateWeight atomIndex - design.weight atomIndex = 0 := congrFun hzero atomIndex
  linarith [hentry]


/-- **THE WHOLE NEGATIVE SUBLEVEL SET IS ALL-HEAVY.**  A light atom deflates onto
`(5,3)` by the shipped `Gtz.exists_dominating_triple_of_light_atom_sixThree`, and a
dominating triple pushes the chart value to zero.  Together with
`stress_eq_zero_of_chartObjective_neg` this says the open set `{chartObjective < 0}`
is all-heavy, conic-free and parallel-free -- three of the eight crux fields, from
the value alone. -/
theorem allHeavy_of_chartObjective_neg (design : WeightedDesign 6 3)
    (hnegative : chartObjective (chartPointOfDesign design) < 0) :
    AllHeavy design := by
  intro atomIndex
  by_contra hlight
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_triple_of_light_atom_sixThree design (not_lt.mp hlight)
  have hnonneg : 0 ≤ chartObjective (chartPointOfDesign design) :=
    (zero_le_chartObjective_iff_exists_chartDominates (chartPointOfDesign design)).mpr
      ⟨selected, hcard, (dominates_iff_chartDominates design selected hcard).mp hdominates⟩
  linarith


/-- **EVERY COMMON QUADRIC OF A DESIGN IS TRACELESS.**  Pairing the Parseval
identity with the form gives `trace form = sum_c t_c * (g_c . form g_c)`, and each
summand vanishes.  Size- and rank-generic, two lines, and it is what makes the
conic picture of the `(6,3)` stress locus concrete: the six directions of a design
lie on a common conic exactly when they lie on a TRACELESS one, and the line-pair
conic `(n_A . x)(n_B . x)` is traceless precisely when the two planes are
PERPENDICULAR. -/
theorem trace_eq_zero_of_forall_quadForm_eq_zero {size rank : ℕ}
    (design : WeightedDesign size rank) {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hsymmetric : formᵀ = form)
    (hcommon : ∀ atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (form *ᵥ design.atom atomIndex) = 0) :
    Matrix.trace form = 0 := by
  have hone : Matrix.trace ((1 : Matrix (Fin rank) (Fin rank) ℝ) * form)
      = Matrix.trace form := by rw [Matrix.one_mul]
  rw [← hone, ← design.isParseval, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun atomIndex _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, trace_atomMatrix_mul_of_symmetric _ hsymmetric,
    hcommon atomIndex, smul_zero]

/-! ## C. The trace identities and the Grassmannian curvature: LANDED ELSEWHERE

The harvested prototype carried three theorems here and all three are now in
`Gtz/Quantitative/ChartSecondOrderStep.lean`, so the section is gone and that module
is imported instead.

* `Gtz.trace_assembly_mul_chartStationaryGap` and `Gtz.trace_mul_grassmannAcceleration`
  landed under the prototype's own names and with the prototype's own statements; the
  gap identity landed as a COROLLARY of the shipped
  `Gtz.trace_projection_mul_multiplier_of_isChartStationaryData` rather than as a
  second proof of it.
* the prototype's third theorem, a projection trace identity
  `trace (Xi * P) = value + 1/size`, is the trace-commuted twin of that same shipped
  lemma (ChartStationary.lean:629) and was dropped as a duplicate.  Anything below or
  downstream that wants it should use the shipped name.

The curvature identity's SIGN is worth carrying with it: the averaged trace is
`rank - 1 - size * value`, which is POSITIVE at a crux, so the Grassmannian directions
are stabilising on average and the curvature cannot by itself contradict minimality.
That reading is measurement, not theorem, and it is recorded so the identity is not
mistaken for an escape mechanism. -/

/-! ## D. The value-zero crossing, and the two fields it supplies -/

section Crossing

variable {size rank : ℕ} [Nonempty (Fin rank)]

/-- **ADMISSIBILITY IS FREE AT EVERY CHART POINT.**  `Gtz.IsChartArgmaxValue` at
the point's OWN objective needs no minimality: the argmax family carries unit
tight directions and every other block has a strictly-below probe.  The tree
derives this only inside
`Gtz.exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin`; here it is
isolated. -/
theorem isChartArgmaxValue_chartObjective (point : ChartPoint size rank) :
    IsChartArgmaxValue rank point.chart point.weight (chartObjective point) :=
  isChartArgmaxValue_of_isChartInactiveStrict (isChartInactiveStrict_chartArgmaxFamily point)
    fun _activeLabel hmember =>
      exists_isChartTightDirection_of_mem_chartArgmaxFamily point hmember

/-- **THE VALUE-ZERO CROSSING.**  Along any continuous path in the raw chart
configuration space that starts strictly below zero and ends at or above zero,
the chart objective vanishes somewhere.  This is the intermediate value theorem
against the shipped `Gtz.continuous_chartObjectiveRaw`; no compactness and no
minimality. -/
theorem exists_chartObjectiveRaw_eq_zero_of_path (hrank : rank ≤ size)
    (path : ℝ → (Fin size → Fin size → ℝ) × (Fin size → ℝ)) (hcontinuous : Continuous path)
    (hstart : chartObjectiveRaw size rank hrank (path 0) < 0)
    (hend : 0 ≤ chartObjectiveRaw size rank hrank (path 1)) :
    ∃ crossing ∈ Set.Icc (0 : ℝ) 1, chartObjectiveRaw size rank hrank (path crossing) = 0 := by
  have hcomposite : Continuous fun parameter : ℝ =>
      chartObjectiveRaw size rank hrank (path parameter) :=
    (continuous_chartObjectiveRaw size rank hrank).comp hcontinuous
  have hmember : (0 : ℝ) ∈ Set.Icc (chartObjectiveRaw size rank hrank (path 0))
      (chartObjectiveRaw size rank hrank (path 1)) := ⟨hstart.le, hend⟩
  obtain ⟨crossing, hinterval, hvalue⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcomposite.continuousOn hmember
  exact ⟨crossing, hinterval, hvalue⟩

/-- **WHAT THE CROSSING SUPPLIES, AND WHAT IT DOES NOT.**  At a chart point of
value exactly zero, two of the five fields of `Gtz.IsChartValueZeroLimit` are
immediate: admissibility at level zero, and a chart-dominating subset.  The
stationarity datum, all-heaviness and parallel-freeness are NOT, and that is the
honest residue of route C's first leaf once it is restated at a deformed
design. -/
theorem isChartArgmaxValue_zero_and_exists_chartDominates_of_chartObjective_eq_zero
    (point : ChartPoint size rank) (hzero : chartObjective point = 0) :
    IsChartArgmaxValue rank point.chart point.weight 0
      ∧ ∃ selected : Finset (Fin size), selected.card = rank ∧ ChartDominates point selected := by
  refine ⟨hzero ▸ isChartArgmaxValue_chartObjective point, ?_⟩
  exact (zero_le_chartObjective_iff_exists_chartDominates point).mp hzero.ge

end Crossing

/-- **THE CROSSING AT A DESIGN.**  A `(6,3)` weighted design whose chart value is
exactly zero satisfies the second and third conjuncts of
`Gtz.IsChartValueZeroLimit` outright. -/
theorem isChartArgmaxValue_zero_and_dominates_of_chartObjective_eq_zero
    (design : WeightedDesign 6 3)
    (hzero : chartObjective (chartPointOfDesign design) = 0) :
    IsChartArgmaxValue 3 (projectionOfDesign design) design.weight 0
      ∧ ∃ chosenSubset : Finset (Fin 6), chosenSubset.card = 3 ∧ Dominates design chosenSubset := by
  obtain ⟨hadmissible, selected, hcard, hdominates⟩ :=
    isChartArgmaxValue_zero_and_exists_chartDominates_of_chartObjective_eq_zero
      (chartPointOfDesign design) hzero
  exact ⟨hadmissible, selected, hcard,
    (dominates_iff_chartDominates design selected hcard).mpr hdominates⟩

end Gtz
