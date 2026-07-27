/-
# The CHART stationarity system — as an IMPLICATION FROM STATIONARITY DATA

The sibling of `Gtz.Quantitative.CriticalQuadric`, one chart to the left.  That
file bundles the first-order data of the DESIGN objective
`F(D) = max_{|C| = k} lambda_min(S_C)` in the raw `(g, t)` coordinates.  This one
bundles the first-order data of the CHART objective

    G(P, t) = max_{|C| = k} lambda_min(W[C]),   W = P - diag t,

in the projection coordinates of `Gtz.Design.ProjectionChart`, where `P = V Vᵀ`
with `Vᵀ V = 1`.  The two objectives share their THRESHOLD — `Gtz.ChartDominates`
is `W[C] ⪰ 0` and `Gtz.dominates_iff_chartDominates` proves it is domination — but
NOT their minimisers, because the congruence `diag(sqrt t_C)` of
`Gtz.chartBlock_sub_weightDiagonal` rescales non-uniformly.  So this is a
parallel system, not a transported one; the "TRANSPORT DOES NOT WORK" section
below records the exact residuals.

**Where the analysis lives is the whole point, exactly as in the sibling.**  The
nonsmooth first-order theory that would PRODUCE the system — Clarke
subdifferentials, the eigenvalue superdifferential, the Grassmannian tangent
space, Danskin's theorem — stays OUTSIDE Lean, as a stated hypothesis.  What is
inside Lean is the pure linear algebra the hypothesis implies.  No derivative, no
limit, no manifold, no subdifferential appears anywhere below.
`IsChartStationaryData` is a bundle of finitely many equations and inequalities;
every theorem here is a consequence of those equations by algebra alone.

## The data

`IsChartStationaryData rank projection weight value activeSet activeSubset
activeWeight tightDir` packages what a nonsmooth first-order analysis of `G` at
an INTERIOR critical point of value `value` would produce:

* a chart point — `projection` symmetric idempotent of trace `rank`, `weight`
  strictly positive summing to one.  Note the chart, not a design, is primitive:
  the bundle never asks that `P` factor as `V Vᵀ`;
* an index set `activeSet` for the attaining `rank`-subsets, with nonnegative
  multipliers `activeWeight` summing to one;
* per active index a `rank`-subset `activeSubset i` and a UNIT AMBIENT vector
  `tightDir i` supported inside that subset, with `W[C] u = value * u` read
  coordinatewise ON the subset;
* the assembled multiplier `Xi = sum_i lambda_i u_i u_iᵀ`
  (`chartMultiplierAssembly`) having CONSTANT diagonal `1/size` (the simplex
  stationarity condition) and COMMUTING with the projection (the Grassmannian
  stationarity condition).

Two design decisions, both deliberate and both departures from the first draft of
the brief this file was built from:

* the per-subset multipliers `Theta_C` enter as unit VECTORS, not as positive
  semidefinite trace-one matrices.  Multiplicity is packaged by repeating one
  subset across several `activeIndex` values, exactly as
  `Gtz.value_eq_rank_of_constant_activeSubset` documents on the design side.  The
  two formulations describe the SAME set of assemblies `Xi` — a PSD trace-one
  `Theta_C` supported on the tight eigenspace is a convex combination of rank-one
  projectors onto tight unit vectors — but the vector form needs no spectral
  decomposition, which this repository deliberately does not carry.
* `Xi ⪰ 0` and `tr Xi = 1` are NOT fields.  They are THEOREMS
  (`posSemidef_chartMultiplierAssembly`,
  `trace_chartMultiplierAssembly_of_isChartStationaryData`), the first from
  nonnegative multipliers and the second from unit tight directions.  The bundle
  is therefore strictly weaker than the brief's, which makes every consequence
  below strictly stronger.

## PROVED here (unconditional, given that data)

* `size_pos_of_isChartStationaryData`, `activeSet_nonempty_of_isChartStationaryData`,
  `exists_pos_activeWeight_of_isChartStationaryData` — well-formedness.
* `posSemidef_chartMultiplierAssembly_of_isChartStationaryData`,
  `transpose_chartMultiplierAssembly_of_isChartStationaryData`,
  `trace_chartMultiplierAssembly_of_isChartStationaryData` — the three properties
  the brief asked for as fields, recovered as consequences.
* `diagonal_eq_inv_size_iff_diagonal_constant` — the constant diagonal and the
  value `1/size` are interchangeable ONCE the trace is one, which it always is.
  So the bundle's `assembly_diagonal` field says exactly "`Xi` has a constant
  diagonal" and nothing more.
* `trace_chartStationaryGap_of_isChartStationaryData` — **(I1)** `tr W = rank - 1`,
  the one place `hasTraceRank` and `weight_sum_one` meet.
* `exists_mem_activeSubset_of_isChartStationaryData` — **the active subsets COVER
  every atom**, and — the difference from the design side that matters —
  UNCONDITIONALLY.  `Gtz.exists_mem_activeSubset_of_isQuadricStationaryData` needs
  `value ≠ 0`; here the constant diagonal `Xi_cc = 1/size > 0` supplies coverage
  with no hypothesis on the value at all.  Consequence
  `size_le_rank_mul_card_activeSet_of_isChartStationaryData`, again with no
  `value ≠ 0`.
* `diagonal_projection_mul_multiplier_of_isChartStationaryData` — **THE FORCED
  DIAGONAL (E4)**: `(P Xi)_cc = (value + t_c)/size` at every atom.  Tightness turns
  `W[C] Theta_C = value Theta_C` into `P[C] Theta_C = (value + D[C]) Theta_C`, the
  support kills the off-subset terms, and the constant diagonal collapses the
  weighted sum.  `trace_projection_mul_multiplier_of_isChartStationaryData` is the
  trace form, `tr(P Xi) = value + 1/size`.
* `weight_ge_neg_value_of_isChartStationaryData` — **THE WEIGHT FLOOR (E5)**:
  `-value ≤ t_c` at every atom.  Commutation makes `P Xi = P Xi Pᵀ` positive
  semidefinite, and a positive semidefinite matrix has a nonnegative diagonal.
* `neg_inv_size_le_value_of_isChartStationaryData` — the ONE-SIDED consequence,
  `-1/size ≤ value`, by summing the floor against `sum_c t_c = 1`.
* `value_le_one_sub_weight_of_isChartStationaryData` — **THE DUAL BOUND**:
  `value ≤ 1 - t_c`, the Naimark mirror obtained by running the floor argument on
  the complementary projection `1 - P`.  With strictly positive weights this gives
  `value_lt_one_of_isChartStationaryData`, `value < 1`.  READ THE THRESHOLD
  CORRECTLY: the chart objective dominates at `0 ≤ value`, not at `1 ≤ value`, so
  neither of these is a GTZ statement — see the note on that theorem.
* `not_isChartStationaryData_of_value_eq_neg_inv_size` — **STRICTNESS (E7)**, with
  BOTH hypotheses it genuinely needs: chart-side admissibility
  (`IsChartArgmaxValue`) and a design behind the projection.  At `value = -1/size`
  the floor forces `t` uniform, admissibility then forces `lambda_min(P[C]) ≤ 0` at
  EVERY `rank`-subset while `P ⪰ 0` forces `≥ 0`, so every `det P[C]` vanishes —
  contradicting `Gtz.sum_shadowDeterminant_eq_one`, which is IMPORTED, not
  re-proved.  `neg_inv_size_lt_value_of_isChartStationaryData` is the usable form:
  under the same two hypotheses, `-1/size < value` strictly.

## MECHANIZED WITNESSES — the bundle is inhabited, twice, and both matter

* `chartTetraProjection_isChartStationaryData` — the `(4,3)` TETRAHEDRON at
  `value = 0`, whose assembly `chartTetraMultiplierAssembly_eq` is exactly the
  hand-computed reference `Xi = I_4/12 + J_4/6`.  This is the EXTREMAL locus, and
  its assembly is NOT a scalar matrix, so `assembly_commutes` is a genuine
  condition there and not an automatic one.
* `chartOctaProjection_isChartStationaryData` — the `(6,3)` OCTAHEDRON at
  `value = 1/3`, which is `2/size`.  It is the witness behind
  `not_forall_value_le_inv_size_of_isChartStationaryData`, and it sits at an OPEN
  cell.

## HONESTY — five statements, each with the witness that forces it

**(a) The variational derivation is not formalized, and the paper says so.**
Every theorem below takes `IsChartStationaryData` as a HYPOTHESIS in its
statement, never as something derived.  The conditionality is in the types, not
only in this prose.  The same firewall as `Gtz.Quantitative.CriticalQuadric`
applies verbatim: instantiating the bundle at a tie presupposes that the tie is a
critical point of `G`, which presupposes `ChartGtz` near it.

**(b) The system is NECESSARY ONLY, and not because of the composition rule.**
It is tempting to advertise the chart route as cleaner than the design route
because `(P, t) ↦ W[C]` is AFFINE while `(g, t) ↦ S_C` is quadratic, so the chain
rule is an equality rather than an inclusion.  That is true and it buys nothing:
the MAX rule stays an inclusion in both systems, because `lambda_min` is CONCAVE
hence not Clarke-regular where the least eigenvalue is multiple, and the max rule
is the only rule a necessary condition uses.  What the chart genuinely buys is
different and should be stated instead: the constraint set is
Grassmannian x simplex, with no quadratic Parseval constraint and no
`rank(rank-1)/2`-dimensional orthogonal gauge, whereas the design side carries
both.  Practical consequence: an exhaustive search finding NO admissible root
would prove the conjecture, while exhibiting one proves nothing.

**(c) The system is satisfied at ADMISSIBLE NON-MINIMA.**  Three witnesses; the
first is mechanized below, the other two are EXACT arithmetic outside Lean and are
NOT mechanized here:

  * the OCTAHEDRON at `(6,3)` — six atoms `±e_1, ±e_2, ±e_3` of leverage three at
    uniform weight `1/6`, `P` the direct sum of three copies of
    `[[1/2, -1/2], [-1/2, 1/2]]`.  The eight rainbow triples have
    `W[C] = (1/3) I_3`, so the BARYCENTRIC choice `Theta_C = I_3/3`,
    `lambda_C = 1/8` — no solve, no free parameter — gives `Xi = I_6/6`
    satisfying (CS1)–(CS4) EXACTLY at `value = 1/3`, which is what
    `chartOctaProjection_isChartStationaryData` mechanizes.  Two facts about it
    are exact-outside-Lean and are not: the datum is ADMISSIBLE, and it is NOT a
    minimiser — an exact reweighting with `P` held fixed drops the objective from
    `1/3` to `0.282638888…`.  It is also the witness that makes the two-sided
    bound false, see (e);
  * the `(4,2)` REACH TRANSPORT — the chart image of the design-side witness
    behind `Gtz.belowOneDesign`, where `[Xi, P] = 0` holds EXACTLY at
    `value = (1 - sqrt 2)/4 < 0` while the true chart objective there is `+1/4`
    and TWO subsets dominate strictly.  So dropping `IsChartArgmaxValue` is fatal,
    exactly as `Gtz.not_isArgmaxDominated_belowOneDesign` is on the design side;
  * a `(6,3)` point over `Q(sqrt 2)` with `value = -1/6 = -1/size`, all four
    conditions exact, and only three of its twenty blocks singular.  This is what
    refutes the UNCONDITIONAL reading of (E7) and is the reason
    `not_isChartStationaryData_of_value_eq_neg_inv_size` carries
    `IsChartArgmaxValue`.

**(d) `Gtz.ChartPointHasDesign` does NOT drop out.**  The campaign brief this
file was built from claimed that running the compactness argument entirely in
chart coordinates deletes that unproved leaf, because the minimiser is never
identified with a design.  One of its TWO uses is deleted; the other is not.  The
interior corollary `Gtz.weight_pos_of_forall_not_chartDominates` carries
`ChartGtz size (rank+1)` and `ChartGtz size rank` as hypotheses, and the only
unconditional producers of `ChartGtz` anywhere are `Gtz.chartGtz_size_zero` and
`Gtz.chartGtz_rank_zero`; every route from a DECIDED smaller cell runs through
`Gtz.chartGtzInterior_of_gtzWeighted`, which takes the leaf.  So the chart route
needs the same THREE non-formal steps as the design route, and
`Gtz.Reduction.CompactnessReduction`'s own "UNPROVED LEAVES" note already said so.
The leaf is TRUE (an orthonormal basis of `range P`) and merely unmechanized; the
brief's practical conclusion survives, its structural claim does not.

**(e) The two-sided bound `|value| ≤ 1/size` is FALSE, and is not stated.**  Only
`neg_inv_size_le_value_of_isChartStationaryData` is proved.  The positive side
fails at the octahedron, where `value = 1/3 = 2/size` — mechanized below as
`not_forall_value_le_inv_size_of_isChartStationaryData`, so the one-sidedness
cannot be silently repaired by a later edit.  Nor is `0 < value` provable:
`chartTetraProjection_isChartStationaryData` sits at `value = 0` exactly, and the
`Q(sqrt 2)` witness of (c) at `value < 0`.

## WHAT THIS DELIVERS, stated at its true size

The paper carries an open work-in-progress box asking for exactly this system —
"restate the system of the interior section for `G`; either removes the hypothesis
of the extremal-counterexample definition from the rank-three theorem".  That
hypothesis is what this bundle discharges, and that is a PRESENTATIONAL
improvement of a real kind: the rank-three theorem stops carrying an extremality
side condition.  It is NOT a route to the open cells `(6,3)` and `(7,3)`.  At the
only counterexamples anyone has exhibited — the complex SIC and the complex trine
— the multiplier conditions are strictly satisfied with room to spare, so they
exclude nothing of the only kind of counterexample known.

## TRANSPORT DOES NOT WORK — measured, not conjectured

The design-side datum of `Gtz.splitSevenDesign_isQuadricStationaryData` does NOT
push forward to a chart datum with the same multipliers: the naive transport
leaves exact residuals `1/140` on the constant diagonal, `1/1280` on the
commutation and `1/560` on the forced diagonal [EXACT rational arithmetic,
outside Lean, not mechanized].  The chart system IS satisfiable at that point,
but by a DIFFERENT multiplier vector (`1/28` on eight indices and `5/84` on
twelve, against `1/32` and `1/16`).  So no theorem here may be obtained by
transporting one from `Gtz.Quantitative.CriticalQuadric`, and none is.

## NOT here, deliberately

* No eigenvalue function.  `Gtz.lambdaMinMat` exists and is workable, but it is
  indexed by `Fin dim`, so using it would force a submatrix reindexing at every
  statement and buy nothing.  Everything below is phrased through
  `Matrix.PosSemidef` and ambient Rayleigh quotients, matching
  `Gtz.ChartDominates` and `Gtz.IsArgmaxDominated`, which are the shipped
  vocabularies for exactly these two jobs.
* No re-derivation of Cauchy–Binet.  `Gtz.sum_shadowDeterminant_eq_one` is
  imported.  It is stated for a design, which is why
  `not_isChartStationaryData_of_value_eq_neg_inv_size` carries a design behind its
  projection; an abstract chart-point version would need the factorisation
  `P = V Vᵀ`, i.e. `Gtz.ChartPointHasDesign` again.
* No chart or gap definition duplicated.  `Gtz.chartGap`
  (`Gtz.Design.ProjectionChart`) is field-generic and takes a design;
  `Gtz.chartPointGap` (`Gtz.Reduction.CompactnessReduction`) takes a
  `Gtz.ChartPoint`, whose weights may VANISH.  `chartStationaryGap` below takes
  the raw matrix and the raw weight vector, because the bundle's weights are
  strictly positive and no design is available.  The three agree wherever two of
  them are defined; the `chartStationary`/`chartMultiplier` prefix keeps the flat
  `Gtz` namespace unambiguous.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.ExchangeInvariant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}

/-! ## Two design-free brackets -/

/-- **A symmetric idempotent reads its own Rayleigh quotient as a squared
length**: `⟨u, P u⟩ = |P u|²`.  This single identity does all three jobs the
strictness argument needs — it makes `P` positive semidefinite, it makes a
vanishing quotient force `P u = 0`, and it needs no spectral theory. -/
theorem dotProduct_mulVec_eq_image_dotProduct_self
    {projection : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection) (probe : Fin size → ℝ) :
    probe ⬝ᵥ (projection *ᵥ probe) = (projection *ᵥ probe) ⬝ᵥ (projection *ᵥ probe) := by
  have hadjoint := dotProduct_mulVec_transpose projection probe (projection *ᵥ probe)
  rw [hsymmetric, Matrix.mulVec_mulVec, hidempotent] at hadjoint
  exact hadjoint.symm

/-- **A trace-one matrix has constant diagonal exactly when every diagonal entry
is `1/size`.**  This is why the bundle's `assembly_diagonal` field carries no
information beyond constancy: the trace of the assembly is always one. -/
theorem diagonal_eq_inv_size_iff_diagonal_constant (hsize : 0 < size)
    (target : Matrix (Fin size) (Fin size) ℝ) (htrace : Matrix.trace target = 1) :
    (∀ atomIndex : Fin size, target atomIndex atomIndex = ((size : ℝ))⁻¹)
      ↔ ∀ firstIndex secondIndex : Fin size,
          target firstIndex firstIndex = target secondIndex secondIndex := by
  have hsizeCastPos : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  constructor
  · intro huniform firstIndex secondIndex
    rw [huniform firstIndex, huniform secondIndex]
  · intro hconstant atomIndex
    have hdiagSum : ∑ otherIndex : Fin size, target otherIndex otherIndex = 1 := htrace
    have hcollapse : ∑ otherIndex : Fin size, target otherIndex otherIndex
        = (size : ℝ) * target atomIndex atomIndex := by
      rw [Finset.sum_congr rfl fun otherIndex _ => hconstant otherIndex atomIndex,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hcollapse] at hdiagSum
    field_simp at hdiagSum ⊢
    linarith

/-! ## The chart gap and the assembled multiplier -/

/-- The chart gap `W = P - diag t` at a RAW chart point: the matrix and the weight
vector are unconstrained arguments, because the stationarity bundle carries its
own constraints on them and no design is available.  Agrees with `Gtz.chartGap`
and with `Gtz.chartPointGap` wherever those are defined. -/
def chartStationaryGap (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  projection - Matrix.diagonal weight

theorem chartStationaryGap_transpose {projection : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : projectionᵀ = projection) (weight : Fin size → ℝ) :
    (chartStationaryGap projection weight)ᵀ = chartStationaryGap projection weight := by
  rw [chartStationaryGap, Matrix.transpose_sub, hsymmetric, Matrix.diagonal_transpose]

/-- **The assembled multiplier** `Xi = sum_i lambda_i u_i u_iᵀ`.  It is a
DEFINITION, not a bundled datum, so its positive semidefiniteness and its unit
trace are theorems rather than hypotheses. -/
def chartMultiplierAssembly (activeSet : Finset activeIndex) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin size → ℝ)) : Matrix (Fin size) (Fin size) ℝ :=
  ∑ activeLabel ∈ activeSet, activeWeight activeLabel • atomMatrix (tightDir activeLabel)

/-- The assembly's entries, unfolded once. -/
theorem chartMultiplierAssembly_apply (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (rowIndex colIndex : Fin size) :
    chartMultiplierAssembly activeSet activeWeight tightDir rowIndex colIndex
      = ∑ activeLabel ∈ activeSet,
          activeWeight activeLabel
            * (tightDir activeLabel rowIndex * tightDir activeLabel colIndex) := by
  simp only [chartMultiplierAssembly, Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
    Matrix.vecMulVec_apply, smul_eq_mul]

/-- The assembly's diagonal is the overlap mass at that atom. -/
theorem chartMultiplierAssembly_diagonal (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) (tightDir : activeIndex → (Fin size → ℝ))
    (atomIndex : Fin size) :
    chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
      = ∑ activeLabel ∈ activeSet,
          activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 := by
  rw [chartMultiplierAssembly_apply]
  exact Finset.sum_congr rfl fun activeLabel _ => by rw [pow_two]

/-! ## The stationarity data -/

/-- **The first-order stationarity data of the CHART objective
`G = max_{|C| = rank} lambda_min(W[C])` at an interior critical point of value
`value`** — as a bundle of equations, with the analysis that would produce it left
entirely outside.

The first five fields are the chart point itself (a symmetric idempotent of trace
`rank`, and strictly positive weights summing to one); the next six are the active
family with its multipliers and tight directions; the last two are the two
stationarity conditions, one from varying the SIMPLEX (constant diagonal) and one
from varying the GRASSMANNIAN (commutation).

This is a HYPOTHESIS, never a theorem.  See the honesty section of the file
header: the system is NECESSARY only, it is satisfied at admissible non-minima,
and instantiating it at a tie presupposes `ChartGtz` near that tie. -/
structure IsChartStationaryData (rank : ℕ) (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin size)) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin size → ℝ)) : Prop where
  /-- The chart is symmetric. -/
  isSymmetric : projectionᵀ = projection
  /-- The chart is idempotent — over ℝ with symmetry, an orthogonal projection. -/
  isIdempotent : projection * projection = projection
  /-- The chart's trace is the rank. -/
  hasTraceRank : Matrix.trace projection = (rank : ℝ)
  /-- The weights are strictly positive: this is the INTERIOR of the simplex. -/
  weight_pos : ∀ atomIndex : Fin size, 0 < weight atomIndex
  /-- The weights sum to one. -/
  weight_sum_one : ∑ atomIndex : Fin size, weight atomIndex = 1
  /-- The multipliers are nonnegative. -/
  activeWeight_nonneg : ∀ activeLabel ∈ activeSet, 0 ≤ activeWeight activeLabel
  /-- The multipliers sum to one. -/
  activeWeight_sum_one : ∑ activeLabel ∈ activeSet, activeWeight activeLabel = 1
  /-- Every active subset has exactly `rank` atoms. -/
  activeSubset_card : ∀ activeLabel ∈ activeSet, (activeSubset activeLabel).card = rank
  /-- Every tight direction is a unit vector. -/
  tightDir_unit : ∀ activeLabel ∈ activeSet, tightDir activeLabel ⬝ᵥ tightDir activeLabel = 1
  /-- Every tight direction is supported inside its own subset. -/
  tightDir_support : ∀ activeLabel ∈ activeSet, ∀ atomIndex : Fin size,
    atomIndex ∉ activeSubset activeLabel → tightDir activeLabel atomIndex = 0
  /-- Tightness: `W[C] u = value * u`, read coordinatewise ON the subset.  Nothing
  is asserted about the coordinates OFF the subset, where the ambient product is
  generally nonzero. -/
  tightDir_isTight : ∀ activeLabel ∈ activeSet, ∀ atomIndex ∈ activeSubset activeLabel,
    (chartStationaryGap projection weight *ᵥ tightDir activeLabel) atomIndex
      = value * tightDir activeLabel atomIndex
  /-- Stationarity in the WEIGHTS: the assembly's diagonal is the constant
  `1/size`.  By `diagonal_eq_inv_size_iff_diagonal_constant` this says exactly
  that the diagonal is constant. -/
  assembly_diagonal : ∀ atomIndex : Fin size,
    chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
      = ((size : ℝ))⁻¹
  /-- Stationarity in the GRASSMANNIAN: the assembly commutes with the chart. -/
  assembly_commutes :
    projection * chartMultiplierAssembly activeSet activeWeight tightDir
      = chartMultiplierAssembly activeSet activeWeight tightDir * projection

variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## L1: accessors and well-formedness -/

/-- **The size is positive.**  An empty index set carries no weights, so the
weight sum would be zero rather than one.  Every division by `size` below is
licensed by this. -/
theorem size_pos_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    0 < size := by
  by_contra hnonpositive
  have hsizeZero : size = 0 := Nat.le_zero.mp (not_lt.mp hnonpositive)
  subst hsizeZero
  have hsum := hdata.weight_sum_one
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact absurd hsum (by norm_num)

theorem size_cast_pos_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (0 : ℝ) < (size : ℝ) := by
  exact_mod_cast size_pos_of_isChartStationaryData hdata

/-- The multipliers sum to one, so the active family is not empty. -/
theorem activeSet_nonempty_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    activeSet.Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hsum := hdata.activeWeight_sum_one
  rw [hempty, Finset.sum_empty] at hsum
  exact absurd hsum (by norm_num)

/-- Nonnegative multipliers summing to one cannot all vanish. -/
theorem exists_pos_activeWeight_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∃ activeLabel ∈ activeSet, 0 < activeWeight activeLabel := by
  by_contra hnone
  simp only [not_exists, not_and, not_lt] at hnone
  have hvanish : ∀ activeLabel ∈ activeSet, activeWeight activeLabel = 0 :=
    fun activeLabel hmem =>
      le_antisymm (hnone activeLabel hmem) (hdata.activeWeight_nonneg activeLabel hmem)
  have hsum := hdata.activeWeight_sum_one
  rw [Finset.sum_congr rfl hvanish, Finset.sum_const_zero] at hsum
  exact absurd hsum (by norm_num)

/-- **The assembly's trace is one**, from the unit tight directions and the
multiplier normalisation ALONE — no use of the constant-diagonal field. -/
theorem trace_chartMultiplierAssembly_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace (chartMultiplierAssembly activeSet activeWeight tightDir) = 1 := by
  rw [chartMultiplierAssembly, Matrix.trace_sum]
  have hperActive : ∀ activeLabel ∈ activeSet,
      Matrix.trace (activeWeight activeLabel • atomMatrix (tightDir activeLabel))
        = activeWeight activeLabel := by
    intro activeLabel hmem
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
    simp only [leverageOf]
    rw [← dotProduct_self_eq_sum_sq, hdata.tightDir_unit activeLabel hmem, mul_one]
  rw [Finset.sum_congr rfl hperActive, hdata.activeWeight_sum_one]

/-- **The constant-diagonal field says exactly "constant diagonal".**  The value
`1/size` is forced by the trace, which is always one, so nothing is lost by
writing the field in the pinned form. -/
theorem assembly_diagonal_iff_constant_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (∀ atomIndex : Fin size,
        chartMultiplierAssembly activeSet activeWeight tightDir atomIndex atomIndex
          = ((size : ℝ))⁻¹)
      ↔ ∀ firstIndex secondIndex : Fin size,
          chartMultiplierAssembly activeSet activeWeight tightDir firstIndex firstIndex
            = chartMultiplierAssembly activeSet activeWeight tightDir secondIndex secondIndex :=
  diagonal_eq_inv_size_iff_diagonal_constant (size_pos_of_isChartStationaryData hdata) _
    (trace_chartMultiplierAssembly_of_isChartStationaryData hdata)

/-- **The assembly is positive semidefinite** — a nonnegative combination of
rank-one projectors.  This is (CS1)'s first half, recovered rather than assumed. -/
theorem posSemidef_chartMultiplierAssembly_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (chartMultiplierAssembly activeSet activeWeight tightDir).PosSemidef :=
  Finset.sum_induction _ Matrix.PosSemidef (fun _ _ hleft hright => hleft.add hright)
    Matrix.PosSemidef.zero
    fun activeLabel hmem =>
      (posSemidef_atomMatrix (tightDir activeLabel)).smul
        (hdata.activeWeight_nonneg activeLabel hmem)

/-- **The assembly is symmetric** — the real reading of the Hermitian half of
positive semidefiniteness. -/
theorem transpose_chartMultiplierAssembly_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (chartMultiplierAssembly activeSet activeWeight tightDir)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir := by
  have hhermitian := (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata).1
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hhermitian

/-- **(I1)**: `tr W = rank - 1`.  The one identity where `hasTraceRank` and
`weight_sum_one` meet, and the reason the gap is never negative definite once the
rank exceeds one. -/
theorem trace_chartStationaryGap_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace (chartStationaryGap projection weight) = (rank : ℝ) - 1 := by
  rw [chartStationaryGap, Matrix.trace_sub, hdata.hasTraceRank, Matrix.trace_diagonal,
    hdata.weight_sum_one]

/-- **THE COVERAGE LAW, unconditionally.**  Every atom lies in some active subset.

The design-side sibling `Gtz.exists_mem_activeSubset_of_isQuadricStationaryData`
needs `value ≠ 0`, because it reads coverage off the coverage law
`sum_{C ∋ c} lambda_C ⟨u_C, g_c⟩² = t_c * value`.  Here the constant diagonal
supplies `sum_{C ∋ c} lambda_C (u_C)_c² = 1/size > 0` with the value nowhere in
sight, so no hypothesis on the value is needed at all. -/
theorem exists_mem_activeSubset_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    ∃ activeLabel ∈ activeSet, atomIndex ∈ activeSubset activeLabel := by
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  have hvanish : ∑ activeLabel ∈ activeSet,
      activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun activeLabel hmem => ?_
    rw [hdata.tightDir_support activeLabel hmem atomIndex (hnone activeLabel hmem)]
    ring
  have hdiagonal := hdata.assembly_diagonal atomIndex
  rw [chartMultiplierAssembly_diagonal, hvanish] at hdiagonal
  have hpositive : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
  exact absurd hdiagonal.symm (ne_of_gt hpositive)

/-- **The size is bounded by rank times the number of active indices**, with no
`value ≠ 0` hypothesis.  Coverage puts every atom in some active subset and each
has `rank` atoms.  Equivalently `|activeSet| ≥ size / rank`, which is the cheapest
filter the bundle supplies. -/
theorem size_le_rank_mul_card_activeSet_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    size ≤ rank * activeSet.card := by
  classical
  have hcovered : (Finset.univ : Finset (Fin size)) ⊆ activeSet.biUnion activeSubset := by
    intro atomIndex _
    obtain ⟨activeLabel, hmem, hmemSubset⟩ :=
      exists_mem_activeSubset_of_isChartStationaryData hdata atomIndex
    exact Finset.mem_biUnion.mpr ⟨activeLabel, hmem, hmemSubset⟩
  have hcardUniv : (Finset.univ : Finset (Fin size)).card
      ≤ (activeSet.biUnion activeSubset).card := Finset.card_le_card hcovered
  have hcardConst : ∑ activeLabel ∈ activeSet, (activeSubset activeLabel).card
      = activeSet.card * rank := by
    rw [Finset.sum_congr rfl hdata.activeSubset_card, Finset.sum_const, smul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin] at hcardUniv
  calc size ≤ (activeSet.biUnion activeSubset).card := hcardUniv
    _ ≤ ∑ activeLabel ∈ activeSet, (activeSubset activeLabel).card := Finset.card_biUnion_le
    _ = activeSet.card * rank := hcardConst
    _ = rank * activeSet.card := Nat.mul_comm _ _

/-! ## L2: the forced diagonal -/

/-- **Tightness, read for the projection.**  On its own subset a tight direction
is an eigenvector of the chart at the SHIFTED value `value + t_c`, coordinate by
coordinate: `(P u)_c = (value + t_c) u_c`. -/
theorem projection_mulVec_tightDir_of_mem
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    {atomIndex : Fin size} (hmemSubset : atomIndex ∈ activeSubset activeLabel) :
    (projection *ᵥ tightDir activeLabel) atomIndex
      = (value + weight atomIndex) * tightDir activeLabel atomIndex := by
  have hsplit : (projection *ᵥ tightDir activeLabel) atomIndex
      = (chartStationaryGap projection weight *ᵥ tightDir activeLabel) atomIndex
        + weight atomIndex * tightDir activeLabel atomIndex := by
    rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    ring
  rw [hsplit, hdata.tightDir_isTight activeLabel hmem atomIndex hmemSubset]
  ring

/-- The single rank-one block of the forced diagonal, valid at EVERY atom: inside
the subset by tightness, outside it because the tight direction vanishes there. -/
theorem diagonal_projection_mul_atomMatrix_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (atomIndex : Fin size) :
    (projection * atomMatrix (tightDir activeLabel)) atomIndex atomIndex
      = (value + weight atomIndex) * tightDir activeLabel atomIndex ^ 2 := by
  have hentry : (projection * atomMatrix (tightDir activeLabel)) atomIndex atomIndex
      = (projection *ᵥ tightDir activeLabel) atomIndex * tightDir activeLabel atomIndex := by
    simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hentry]
  by_cases hmemSubset : atomIndex ∈ activeSubset activeLabel
  · rw [projection_mulVec_tightDir_of_mem hdata hmem hmemSubset]
    ring
  · rw [hdata.tightDir_support activeLabel hmem atomIndex hmemSubset]
    ring

/-- **THE FORCED DIAGONAL (E4).**  At every atom,

    `(P Xi)_cc = (value + t_c) / size` .

Tightness turns the gap eigen-equation into `P[C] Theta_C = (value + D[C]) Theta_C`,
the support kills the off-subset terms, and the constant diagonal collapses the
weighted sum of squared overlaps into `1/size`.

Note what this does NOT need: the commutation field.  The forced diagonal is a
consequence of simplex stationarity and tightness alone. -/
theorem diagonal_projection_mul_multiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir) atomIndex atomIndex
      = (value + weight atomIndex) * ((size : ℝ))⁻¹ := by
  have hexpand : (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
      atomIndex atomIndex
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ((projection * atomMatrix (tightDir activeLabel)) atomIndex atomIndex) := by
    rw [chartMultiplierAssembly, Matrix.mul_sum]
    simp only [Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hterms : ∀ activeLabel ∈ activeSet,
      activeWeight activeLabel
          * ((projection * atomMatrix (tightDir activeLabel)) atomIndex atomIndex)
        = (value + weight atomIndex)
          * (activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2) := by
    intro activeLabel hmem
    rw [diagonal_projection_mul_atomMatrix_of_isChartStationaryData hdata hmem atomIndex]
    ring
  rw [hexpand, Finset.sum_congr rfl hterms, ← Finset.mul_sum, ← chartMultiplierAssembly_diagonal,
    hdata.assembly_diagonal atomIndex]

/-- **The trace form of the forced diagonal**: `tr(P Xi) = value + 1/size`.  The
weights sum to one, so summing the forced diagonal over the atoms turns
`size * value + 1` into the stated shape. -/
theorem trace_projection_mul_multiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
      = value + ((size : ℝ))⁻¹ := by
  have hsizeNe : ((size : ℝ)) ≠ 0 := ne_of_gt (size_cast_pos_of_isChartStationaryData hdata)
  have hdiagSum :
      Matrix.trace (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
        = ∑ atomIndex : Fin size, (value + weight atomIndex) * ((size : ℝ))⁻¹ :=
    Finset.sum_congr rfl fun atomIndex _ =>
      diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex
  rw [hdiagSum, ← Finset.sum_mul, Finset.sum_add_distrib, hdata.weight_sum_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ## L3: the weight floor -/

/-- `P Xi` is a CONGRUENCE of `Xi`.  Commutation plus idempotence turn the
one-sided product into the two-sided `P Xi Pᵀ`, which is where positivity comes
from. -/
theorem projection_mul_multiplier_eq_sandwich_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    projection * chartMultiplierAssembly activeSet activeWeight tightDir
      = projection * chartMultiplierAssembly activeSet activeWeight tightDir * projection := by
  rw [Matrix.mul_assoc, ← hdata.assembly_commutes, ← Matrix.mul_assoc, hdata.isIdempotent]

/-- `P Xi` is positive semidefinite. -/
theorem posSemidef_projection_mul_multiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (projection * chartMultiplierAssembly activeSet activeWeight tightDir).PosSemidef := by
  have hconj : (projection)ᴴ = projection := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hdata.isSymmetric
  have hsandwich :=
    (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata).mul_mul_conjTranspose_same
      projection
  rw [hconj] at hsandwich
  rw [projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata]
  exact hsandwich

/-- **THE WEIGHT FLOOR (E5)**: `-value ≤ t_c` at every atom.

`P Xi = P Xi Pᵀ` is positive semidefinite, so its diagonal is nonnegative, and
the forced diagonal identifies that diagonal as `(value + t_c)/size`.

DISCLOSURE, so the reach is not overstated: this is a structural identity, not an
exclusion.  It is implied unconditionally by `0 ≤ value`, and in ~7000 sampled
data it was never the binding condition. -/
theorem weight_ge_neg_value_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    -value ≤ weight atomIndex := by
  have hdiagonal :=
    (posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata).diag_nonneg
      (i := atomIndex)
  rw [diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex] at hdiagonal
  have hinvPos : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
  nlinarith [hdiagonal, hinvPos]

/-- **The ONE-SIDED value bound**: `-1/size ≤ value`.  Summing the weight floor
against `sum_c t_c = 1` gives `size * (-value) ≤ 1`.

The two-sided bound `|value| ≤ 1/size` is FALSE and is deliberately not stated —
`not_forall_value_le_inv_size_of_isChartStationaryData` refutes the positive side
with an exact `(6,3)` witness at `value = 1/3 = 2/size`. -/
theorem neg_inv_size_le_value_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    -((size : ℝ))⁻¹ ≤ value := by
  have hsizePos := size_cast_pos_of_isChartStationaryData hdata
  have hsum : ∑ _atomIndex : Fin size, (-value) ≤ ∑ atomIndex : Fin size, weight atomIndex :=
    Finset.sum_le_sum fun atomIndex _ =>
      weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    hdata.weight_sum_one] at hsum
  have hinvPos : (0 : ℝ) < ((size : ℝ))⁻¹ := inv_pos.mpr hsizePos
  have hscaled := mul_le_mul_of_nonneg_left hsum hinvPos.le
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsizePos), one_mul, mul_one] at hscaled
  linarith

/-- **THE DUAL WEIGHT BOUND**: `value ≤ 1 - t_c` at every atom — the Naimark
mirror of the weight floor.

The COMPLEMENTARY projection `1 - P` is again a symmetric idempotent commuting
with the assembly, so `(1 - P) Xi` is again a congruence of `Xi` and again
positive semidefinite; its diagonal is `Xi_cc - (P Xi)_cc = (1 - value - t_c)/size`.

This is the strongest upper bound the bundle alone supplies, and unlike the
refuted `value ≤ 1/size` it is a theorem: the octahedron witness has
`value = 1/3 ≤ 1 - 1/6`, with slack. -/
theorem value_le_one_sub_weight_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    value ≤ 1 - weight atomIndex := by
  have hcomplementTranspose :
      (1 - projection : Matrix (Fin size) (Fin size) ℝ)ᴴ = 1 - projection := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub, Matrix.transpose_one,
      hdata.isSymmetric]
  have hcomplementIdempotent :
      (1 - projection) * (1 - projection) = (1 - projection : Matrix (Fin size) (Fin size) ℝ) := by
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hdata.isIdempotent, sub_self, sub_zero]
  have hcomplementCommutes :
      (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir
        = chartMultiplierAssembly activeSet activeWeight tightDir * (1 - projection) := by
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hdata.assembly_commutes]
  have hsandwich :
      (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir
        = (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir
          * (1 - projection) := by
    rw [Matrix.mul_assoc, ← hcomplementCommutes, ← Matrix.mul_assoc, hcomplementIdempotent]
  have hposSemidef :
      ((1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir).PosSemidef := by
    have hcongruence :=
      (posSemidef_chartMultiplierAssembly_of_isChartStationaryData
        hdata).mul_mul_conjTranspose_same (1 - projection)
    rw [hcomplementTranspose] at hcongruence
    rw [hsandwich]
    exact hcongruence
  have hdiagonal := hposSemidef.diag_nonneg (i := atomIndex)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hdata.assembly_diagonal atomIndex,
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex] at hdiagonal
  have hinvPos : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
  nlinarith [hdiagonal, hinvPos]

/-- **The value is strictly below one**, because the weights are strictly positive.

READ THE THRESHOLD CORRECTLY.  This is NOT a GTZ statement and must never be
advertised as one.  The chart objective's domination threshold is `0 ≤ value`
(`Gtz.ChartDominates` is `W[C] ⪰ 0`), not `1 ≤ value` — the level one belongs to
the DESIGN objective `F = max lambda_min(S_C)`.  So `value < 1` is a structural
ceiling that every interior datum satisfies, including a hypothetical
counterexample at `value < 0`.  It is stated because it is the one place the
strict positivity of the weights is load-bearing. -/
theorem value_lt_one_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    value < 1 := by
  haveI : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp (size_pos_of_isChartStationaryData hdata)
  obtain ⟨someAtom⟩ := ‹Nonempty (Fin size)›
  have hceiling := value_le_one_sub_weight_of_isChartStationaryData hdata someAtom
  linarith [hdata.weight_pos someAtom]

/-! ## L4: strictness, with the two hypotheses it genuinely needs -/

/-- **The chart-side ARGMAX field the bundle omits.**  No `rank`-subset beats
`value`: every `rank`-subset carries a unit probe supported inside it whose
Rayleigh quotient against the chart gap is at most `value`, i.e.
`lambda_min(W[C]) ≤ value` at EVERY subset and not only at the active ones.

Named and defined SEPARATELY rather than baked into the bundle, exactly as
`Gtz.IsArgmaxDominated` is on the design side, so that the hole is citable.  It is
expressible in the shipped vocabulary — a probe, a dot product — but it is not an
EQUATION: it is an existential, disjunctive once expanded, which is why no
multiplier algebra can consume it. -/
def IsChartArgmaxValue (rank : ℕ) (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) : Prop :=
  ∀ chosenSubset : Finset (Fin size), chosenSubset.card = rank →
    ∃ probe : Fin size → ℝ, probe ⬝ᵥ probe = 1 ∧
      (∀ atomIndex : Fin size, atomIndex ∉ chosenSubset → probe atomIndex = 0) ∧
      probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe) ≤ value

/-- **At the floor the weights are uniform.**  `-value ≤ t_c` with
`value = -1/size` forces `1/size ≤ t_c` at every atom, and the weights sum to one,
so no slack is available anywhere. -/
theorem weight_eq_inv_size_of_value_eq_neg_inv_size
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hfloor : value = -((size : ℝ))⁻¹) (atomIndex : Fin size) :
    weight atomIndex = ((size : ℝ))⁻¹ := by
  have hsizeNe : ((size : ℝ)) ≠ 0 := ne_of_gt (size_cast_pos_of_isChartStationaryData hdata)
  have hlower : ∀ otherIndex : Fin size, ((size : ℝ))⁻¹ ≤ weight otherIndex := by
    intro otherIndex
    have hbound := weight_ge_neg_value_of_isChartStationaryData hdata otherIndex
    rwa [hfloor, neg_neg] at hbound
  have hconstSum : ∑ _otherIndex : Fin size, ((size : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsumEq : ∑ otherIndex : Fin size, ((size : ℝ))⁻¹
      = ∑ otherIndex : Fin size, weight otherIndex := by
    rw [hconstSum, hdata.weight_sum_one]
  exact ((Finset.sum_eq_sum_iff_of_le fun otherIndex _ => hlower otherIndex).mp hsumEq atomIndex
    (Finset.mem_univ atomIndex)).symm

/-- **STRICTNESS (E7), with both hypotheses.**  There is no admissible chart
stationarity datum at `value = -1/size` whose projection is a design's chart.

Proof.  The weight floor forces `t` uniform at `1/size`.  Admissibility then
supplies, at EVERY `rank`-subset, a unit probe supported there with
`⟨u, W u⟩ ≤ -1/size`, so `⟨u, P u⟩ ≤ 0`; but `⟨u, P u⟩ = |P u|² ≥ 0`, hence
`P u = 0` with `u ≠ 0`, hence `det P[C] = 0`.  Every `rank`-subset therefore has a
vanishing shadow determinant, contradicting `Gtz.sum_shadowDeterminant_eq_one`.

BOTH hypotheses are load-bearing and neither can be dropped.

* `IsChartArgmaxValue` — WITHOUT it the statement is FALSE.  There is a `(6,3)`
  chart point over `Q(sqrt 2)` carrying a datum at exactly `value = -1/6`, with all
  four conditions holding on the nose and only three of its twenty blocks singular
  [EXACT, outside Lean, not mechanized].  The brief's unconditional version of
  this theorem is therefore not a theorem.
* the DESIGN — because Cauchy–Binet is imported, not re-derived.  An abstract
  chart-point version of `sum_shadowDeterminant_eq_one` would need the
  factorisation `P = V Vᵀ`, which is precisely `Gtz.ChartPointHasDesign`, the leaf
  the chart route does not remove.

Note also the SIGN.  Only the negative branch is excluded; `value = +1/size` is
attained, and `value = 2/size` is attained too — see
`not_forall_value_le_inv_size_of_isChartStationaryData`. -/
theorem not_isChartStationaryData_of_value_eq_neg_inv_size
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hfloor : value = -((size : ℝ))⁻¹) :
    ¬ IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir := by
  classical
  intro hdata
  have huniform := weight_eq_inv_size_of_value_eq_neg_inv_size hdata hfloor
  -- every `rank`-subset has a vanishing shadow determinant
  have hvanish : ∀ chosenSubset ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
      shadowDeterminant design chosenSubset = 0 := by
    intro chosenSubset hmemFamily
    have hcard : chosenSubset.card = rank := (Finset.mem_powersetCard.mp hmemFamily).2
    obtain ⟨probe, hunit, hsupport, hquotient⟩ := hargmax chosenSubset hcard
    -- the weight part of the Rayleigh quotient is exactly `1/size`
    have hweightPart : probe ⬝ᵥ (Matrix.diagonal weight *ᵥ probe) = ((size : ℝ))⁻¹ := by
      have hentries : ∀ atomIndex : Fin size,
          probe atomIndex * (Matrix.diagonal weight *ᵥ probe) atomIndex
            = ((size : ℝ))⁻¹ * (probe atomIndex * probe atomIndex) := by
        intro atomIndex
        rw [Matrix.mulVec_diagonal, huniform atomIndex]
        ring
      rw [dotProduct, Finset.sum_congr rfl fun atomIndex _ => hentries atomIndex,
        ← Finset.mul_sum, ← dotProduct, hunit, mul_one]
    -- hence the chart part of the quotient is nonpositive
    have hchartPart : probe ⬝ᵥ (projection *ᵥ probe) ≤ 0 := by
      have hsplit : probe ⬝ᵥ (chartStationaryGap projection weight *ᵥ probe)
          = probe ⬝ᵥ (projection *ᵥ probe) - ((size : ℝ))⁻¹ := by
        rw [chartStationaryGap, Matrix.sub_mulVec, dotProduct_sub, hweightPart]
      rw [hsplit, hfloor] at hquotient
      linarith
    -- but it is a squared length, so the image vanishes
    have hsquare := dotProduct_mulVec_eq_image_dotProduct_self hdata.isSymmetric
      hdata.isIdempotent probe
    have himageZero : projection *ᵥ probe = 0 := by
      refine eq_zero_of_dotProduct_self_eq_zero (le_antisymm ?_ (dotProduct_self_nonneg _))
      rw [← hsquare]
      exact hchartPart
    -- a nonzero kernel vector supported on the subset kills the principal minor
    have hprobeNe : probe ≠ 0 := by
      intro hzero
      rw [hzero, zero_dotProduct] at hunit
      exact absurd hunit (by norm_num)
    obtain ⟨witnessIndex, hwitness⟩ := Function.ne_iff.mp hprobeNe
    have hwitnessMem : witnessIndex ∈ chosenSubset := by
      by_contra hnotMem
      exact hwitness (by simpa using hsupport witnessIndex hnotMem)
    have hrestrictNe : (fun selectedIndex : { c // c ∈ chosenSubset } => probe selectedIndex.val)
        ≠ 0 := by
      refine Function.ne_iff.mpr ⟨⟨witnessIndex, hwitnessMem⟩, ?_⟩
      simpa using hwitness
    have hrestrictKernel :
        (projection.submatrix (Subtype.val : { c // c ∈ chosenSubset } → Fin size)
            (Subtype.val : { c // c ∈ chosenSubset } → Fin size))
          *ᵥ (fun selectedIndex : { c // c ∈ chosenSubset } => probe selectedIndex.val) = 0 := by
      funext selectedIndex
      have hfullRow : ∑ otherIndex : Fin size,
          projection selectedIndex.val otherIndex * probe otherIndex = 0 := by
        have hrow := congrFun himageZero selectedIndex.val
        simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hrow
      have hsubsetRow : ∑ otherIndex ∈ chosenSubset,
          projection selectedIndex.val otherIndex * probe otherIndex = 0 := by
        rw [Finset.sum_subset (Finset.subset_univ chosenSubset)
          (fun otherIndex _ hnotMem => by rw [hsupport otherIndex hnotMem, mul_zero])]
        exact hfullRow
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
      rw [Finset.sum_coe_sort chosenSubset
        (fun otherIndex => projection selectedIndex.val otherIndex * probe otherIndex)]
      exact hsubsetRow
    have hdetZero : (projection.submatrix (Subtype.val : { c // c ∈ chosenSubset } → Fin size)
        (Subtype.val : { c // c ∈ chosenSubset } → Fin size)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hrestrictNe, hrestrictKernel⟩
    rw [shadowDeterminant, ← hchart]
    exact hdetZero
  have hsum := sum_shadowDeterminant_eq_one design
  rw [Finset.sum_congr rfl hvanish, Finset.sum_const_zero] at hsum
  exact absurd hsum (by norm_num)

/-- **(E7) IN ITS USABLE FORM**: an admissible chart stationarity datum whose
projection is a design's chart has `-1/size < value`, STRICTLY.

The weight floor gives `≤` and the strictness theorem removes the endpoint.  This
is the whole of (E7) that survives: the two-sided `|value| < 1/size` is refuted on
the positive side (`not_forall_value_le_inv_size_of_isChartStationaryData`), and
the negative bound needs both the argmax field and the design, for the reasons
recorded on the strictness theorem. -/
theorem neg_inv_size_lt_value_of_isChartStationaryData
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    -((size : ℝ))⁻¹ < value :=
  lt_of_le_of_ne (neg_inv_size_le_value_of_isChartStationaryData hdata) fun hendpoint =>
    not_isChartStationaryData_of_value_eq_neg_inv_size design hchart hargmax hendpoint.symm hdata

/-! ## The reference point — the tetrahedron at `(4,3)`, where the value is zero

Four atoms of leverage three at uniform weight `1/4`, so `P = 1 - J/4` with `J`
the all-ones matrix: `3/4` on the diagonal, `-1/4` off it.  The gap is `1/2` on
the diagonal and `-1/4` off it, so each of the four triples has
`W[C] = (3/4) I_3 - (1/4) J_3`, which annihilates the all-ones direction.  The
tetrahedron is therefore EXTREMAL — `value = 0` — and every triple is tight.

Taking the four normalised all-ones directions, each supported on the triple that
misses one atom and each with multiplier `1/4`, assembles

    `Xi = I_4/12 + J_4/6` ,

i.e. `1/4` on the diagonal — which is `1/size`, as (CS2) demands — and `1/6` off
it.  That is the hand-computed reference value for this chart point, reproduced
here on the nose by `chartTetraMultiplierAssembly_eq`.

Two things this witness supplies that the octahedron below does not.  Its `value`
is ZERO, so the bundle is inhabited on the EXTREMAL locus, where the chart system
restricts to the design-side quadric law.  And its assembly is NOT a scalar
matrix, so `assembly_commutes` is a genuine condition here rather than an
automatic one. -/

/-- The tetrahedron chart `P = 1 - J/4`: `3/4` on the diagonal, `-1/4` off it. -/
noncomputable def chartTetraProjection : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun rowIndex colIndex => if rowIndex = colIndex then 3 / 4 else -(1 / 4)

/-- The uniform tetrahedron weights. -/
noncomputable def chartTetraWeight : Fin 4 → ℝ := fun _ => (4 : ℝ)⁻¹

/-- The triple that misses one atom. -/
def chartTetraSubset (missingIndex : Fin 4) : Finset (Fin 4) := Finset.univ.erase missingIndex

/-- The uniform tetrahedron multipliers. -/
noncomputable def chartTetraMultiplierWeight : Fin 4 → ℝ := fun _ => (4 : ℝ)⁻¹

/-- The UNNORMALISED tight direction: the indicator of the triple.  Its squared
length is three, which is where the `1/sqrt 3` below comes from. -/
def chartTetraSupport (missingIndex : Fin 4) : Fin 4 → ℝ :=
  fun atomIndex => if atomIndex = missingIndex then 0 else 1

/-- The tight direction: the all-ones direction of the triple, normalised. -/
noncomputable def chartTetraTightDir (missingIndex : Fin 4) : Fin 4 → ℝ :=
  (Real.sqrt 3)⁻¹ • chartTetraSupport missingIndex

/-- The tetrahedron's assembled multiplier `Xi = I/12 + J/6`, written entrywise:
`1/12 + 1/6 = 1/4` on the diagonal and `1/6` off it. -/
noncomputable def chartTetraMultiplier : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun rowIndex colIndex => if rowIndex = colIndex then 1 / 4 else 1 / 6

theorem chartTetraProjection_transpose : chartTetraProjectionᵀ = chartTetraProjection := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, chartTetraProjection, Matrix.of_apply]
  by_cases hequal : rowIndex = colIndex
  · rw [hequal]
  · rw [if_neg (Ne.symm hequal), if_neg hequal]

theorem chartTetraProjection_mul_self :
    chartTetraProjection * chartTetraProjection = chartTetraProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [chartTetraProjection, Fin.ext_iff]

/-- The tetrahedron gap: `1/2` on the diagonal, `-1/4` off it. -/
theorem chartTetraGap_apply (rowIndex colIndex : Fin 4) :
    chartStationaryGap chartTetraProjection chartTetraWeight rowIndex colIndex
      = if rowIndex = colIndex then 1 / 2 else -(1 / 4) := by
  simp only [chartStationaryGap, Matrix.sub_apply, chartTetraProjection, Matrix.of_apply,
    Matrix.diagonal_apply, chartTetraWeight]
  by_cases hequal : rowIndex = colIndex
  · rw [if_pos hequal, if_pos hequal, if_pos hequal]; norm_num
  · rw [if_neg hequal, if_neg hequal, if_neg hequal]; norm_num

/-- The indicator of a triple has squared length three. -/
theorem chartTetraSupport_dotProduct_self (missingIndex : Fin 4) :
    chartTetraSupport missingIndex ⬝ᵥ chartTetraSupport missingIndex = 3 := by
  simp only [dotProduct, chartTetraSupport, Fin.sum_univ_four]
  fin_cases missingIndex <;> norm_num [Fin.ext_iff]

/-- **The tetrahedron is EXTREMAL**: the gap annihilates each triple's all-ones
direction, coordinatewise ON that triple.  Off the triple the same product is
`-3/4` times the normalisation, which is exactly why the tightness field of the
bundle is restricted to the subset. -/
theorem chartTetraGap_mulVec_support (missingIndex atomIndex : Fin 4)
    (hdistinct : atomIndex ≠ missingIndex) :
    (chartStationaryGap chartTetraProjection chartTetraWeight *ᵥ chartTetraSupport missingIndex)
      atomIndex = 0 := by
  simp only [Matrix.mulVec, dotProduct, chartTetraGap_apply, chartTetraSupport, Fin.sum_univ_four]
  fin_cases missingIndex <;> fin_cases atomIndex <;> simp_all [Fin.ext_iff] <;> norm_num

/-- **THE REFERENCE VALUE**: the tetrahedron's assembly is `I/12 + J/6`, i.e.
`1/4` on the diagonal and `1/6` off it.  Every atom lies in three of the four
triples and every pair in two, so the diagonal is `3/12` and the off-diagonal
`2/12`. -/
theorem chartTetraMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 4)) chartTetraMultiplierWeight
        chartTetraTightDir
      = chartTetraMultiplier := by
  have hscale : ∀ missingIndex : Fin 4,
      chartTetraMultiplierWeight missingIndex • atomMatrix (chartTetraTightDir missingIndex)
        = (12 : ℝ)⁻¹ • atomMatrix (chartTetraSupport missingIndex) := by
    intro missingIndex
    rw [chartTetraTightDir, atomMatrix_smul, inv_pow, sqrt_three_sq, smul_smul,
      chartTetraMultiplierWeight]
    norm_num
  rw [chartMultiplierAssembly, Finset.sum_congr rfl fun missingIndex _ => hscale missingIndex]
  ext rowIndex colIndex
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
    Matrix.vecMulVec_apply, chartTetraSupport, chartTetraMultiplier, Matrix.of_apply,
    Fin.sum_univ_four]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Fin.ext_iff]

/-- **THE TETRAHEDRON DATUM.**  Rank three, four atoms, `value = 0`, four active
triples, assembly `I/12 + J/6`. -/
theorem chartTetraProjection_isChartStationaryData :
    IsChartStationaryData 3 chartTetraProjection chartTetraWeight 0
      (Finset.univ : Finset (Fin 4)) chartTetraSubset chartTetraMultiplierWeight
      chartTetraTightDir where
  isSymmetric := chartTetraProjection_transpose
  isIdempotent := chartTetraProjection_mul_self
  hasTraceRank := by
    show ∑ atomIndex : Fin 4, chartTetraProjection atomIndex atomIndex = ((3 : ℕ) : ℝ)
    rw [Fin.sum_univ_four]
    norm_num [chartTetraProjection]
  weight_pos := by intro atomIndex; norm_num [chartTetraWeight]
  weight_sum_one := by norm_num [chartTetraWeight, Fin.sum_univ_four]
  activeWeight_nonneg := by intro missingIndex _; norm_num [chartTetraMultiplierWeight]
  activeWeight_sum_one := by norm_num [chartTetraMultiplierWeight, Fin.sum_univ_four]
  activeSubset_card := by intro missingIndex _; fin_cases missingIndex <;> decide
  tightDir_unit := by
    intro missingIndex _
    have hinvRoot : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (3 : ℝ)⁻¹ := by
      rw [← mul_inv, ← pow_two, sqrt_three_sq]
    rw [chartTetraTightDir, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hinvRoot, chartTetraSupport_dotProduct_self]
    norm_num
  tightDir_support := by
    intro missingIndex _ atomIndex hnotMem
    have hequal : atomIndex = missingIndex := by
      by_contra hdistinct
      exact hnotMem (Finset.mem_erase.mpr ⟨hdistinct, Finset.mem_univ atomIndex⟩)
    simp only [chartTetraTightDir, Pi.smul_apply, chartTetraSupport, if_pos hequal, smul_zero]
  tightDir_isTight := by
    intro missingIndex _ atomIndex hmem
    simp only [chartTetraSubset] at hmem
    have hdistinct : atomIndex ≠ missingIndex := Finset.ne_of_mem_erase hmem
    rw [chartTetraTightDir, Matrix.mulVec_smul, Pi.smul_apply,
      chartTetraGap_mulVec_support missingIndex atomIndex hdistinct, smul_zero, zero_mul]
  assembly_diagonal := by
    intro atomIndex
    rw [chartTetraMultiplierAssembly_eq, chartTetraMultiplier, Matrix.of_apply, if_pos rfl]
    norm_num
  assembly_commutes := by
    rw [chartTetraMultiplierAssembly_eq]
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [chartTetraProjection, chartTetraMultiplier, Fin.ext_iff]

/-- **The bundle is inhabited at value ZERO**, on the extremal locus.  So the
consequences above are not statements about data whose value is bounded away from
the threshold, and in particular `neg_inv_size_le_value_of_isChartStationaryData`
is not vacuous at its own boundary. -/
theorem exists_isChartStationaryData_value_eq_zero :
    ∃ (projection : Matrix (Fin 4) (Fin 4) ℝ) (weight : Fin 4 → ℝ)
      (activeSubset : Fin 4 → Finset (Fin 4)) (activeWeight : Fin 4 → ℝ)
      (tightDir : Fin 4 → (Fin 4 → ℝ)),
      IsChartStationaryData 3 projection weight 0 (Finset.univ : Finset (Fin 4))
        activeSubset activeWeight tightDir :=
  ⟨chartTetraProjection, chartTetraWeight, chartTetraSubset, chartTetraMultiplierWeight,
    chartTetraTightDir, chartTetraProjection_isChartStationaryData⟩

/-! ## The two-sided bound is REFUTED — the octahedron at `(6,3)`

Six atoms `±e_1, ±e_2, ±e_3` of leverage three at uniform weight `1/6`.  The chart
is the direct sum of three copies of `[[1/2, -1/2], [-1/2, 1/2]]`, one per axis,
so the gap has `1/3` on the diagonal, `-1/2` across each axis, and `0` between
axes.  A RAINBOW triple — one atom from each axis — therefore has
`W[C] = (1/3) I_3`, which makes EVERY unit vector supported on it tight at
`value = 1/3`.

Taking the six coordinate directions, each with multiplier `1/6` and each assigned
to the rainbow triple containing it, assembles `Xi = I_6 / 6`.  That has constant
diagonal `1/6 = 1/size` and commutes with everything, so all of (CS1)–(CS4) hold
on the nose with no solve and no free parameter.

The point of this witness is the VALUE: `1/3 = 2/size`, so the two-sided bound
`|value| ≤ 1/size` claimed for this system is FALSE, and only the one-sided
`neg_inv_size_le_value_of_isChartStationaryData` may be stated.  A second reading
is that the bundle is inhabited at an OPEN cell, not only at the decided `(4,3)`
corner above.

Two facts about this point are EXACT arithmetic outside Lean and are NOT
mechanized: (i) the datum is also ADMISSIBLE, `lambda_min(W[C]) ≤ 1/3` at all
twenty triples, so the refutation survives attaching `IsChartArgmaxValue`; and
(ii) the point is NOT a minimiser — an exact reweighting with the chart held fixed
drops the objective from `1/3` to `0.282638888…`.  Together those say the system
is satisfied at admissible non-minima, which is the honest ceiling of this lane.
-/

/-- The axis of an atom: indices `0,1` share axis `0`, indices `2,3` share axis
`1`, indices `4,5` share axis `2`.  Two atoms are ANTIPODAL exactly when they
share an axis and differ. -/
def chartOctaAxis (atomIndex : Fin 6) : ℕ := (atomIndex : ℕ) / 2

/-- The octahedron chart: `1/2` on the diagonal, `-1/2` between antipodal atoms,
`0` between axes — the direct sum of three copies of
`[[1/2, -1/2], [-1/2, 1/2]]`. -/
noncomputable def chartOctaProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun rowIndex colIndex =>
    if rowIndex = colIndex then 1 / 2
    else if chartOctaAxis rowIndex = chartOctaAxis colIndex then -(1 / 2) else 0

/-- The uniform octahedron weights. -/
noncomputable def chartOctaWeight : Fin 6 → ℝ := fun _ => (6 : ℝ)⁻¹

/-- The rainbow triple carrying each atom: the even atoms take `{0, 2, 4}`, the
odd ones `{1, 3, 5}`.  Both are rainbow — one atom per axis — so both have
`W[C] = (1/3) I_3`. -/
def chartOctaSubset (atomIndex : Fin 6) : Finset (Fin 6) :=
  if (atomIndex : ℕ) % 2 = 0 then {0, 2, 4} else {1, 3, 5}

/-- The uniform octahedron multipliers. -/
noncomputable def chartOctaMultiplierWeight : Fin 6 → ℝ := fun _ => (6 : ℝ)⁻¹

/-- The tight directions: the six coordinate unit vectors.  A rainbow block is a
scalar matrix, so every unit vector supported on it is tight. -/
noncomputable def chartOctaTightDir (atomLabel : Fin 6) : Fin 6 → ℝ := Pi.single atomLabel 1

theorem chartOctaProjection_transpose : chartOctaProjectionᵀ = chartOctaProjection := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, chartOctaProjection, Matrix.of_apply]
  by_cases hequal : rowIndex = colIndex
  · rw [hequal]
  · rw [if_neg (Ne.symm hequal), if_neg hequal]
    by_cases haxis : chartOctaAxis rowIndex = chartOctaAxis colIndex
    · rw [if_pos haxis.symm, if_pos haxis]
    · rw [if_neg fun hflip => haxis hflip.symm, if_neg haxis]

theorem chartOctaProjection_mul_self :
    chartOctaProjection * chartOctaProjection = chartOctaProjection := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [chartOctaProjection, chartOctaAxis, Fin.ext_iff]

/-- The six coordinate projectors resolve the identity, so the octahedron
assembly is the scalar matrix `I / 6`. -/
theorem chartOctaMultiplierAssembly_eq :
    chartMultiplierAssembly (Finset.univ : Finset (Fin 6)) chartOctaMultiplierWeight
        chartOctaTightDir
      = (6 : ℝ)⁻¹ • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  ext rowIndex colIndex
  rw [chartMultiplierAssembly_apply, Fin.sum_univ_six]
  simp only [chartOctaMultiplierWeight, chartOctaTightDir, Pi.single_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Fin.ext_iff]

/-- **THE OCTAHEDRON DATUM.**  Rank three, six atoms, `value = 1/3`, six active
indices carrying two rainbow triples, assembly `I_6 / 6`. -/
theorem chartOctaProjection_isChartStationaryData :
    IsChartStationaryData 3 chartOctaProjection chartOctaWeight (1 / 3)
      (Finset.univ : Finset (Fin 6)) chartOctaSubset chartOctaMultiplierWeight
      chartOctaTightDir where
  isSymmetric := chartOctaProjection_transpose
  isIdempotent := chartOctaProjection_mul_self
  hasTraceRank := by
    show ∑ atomIndex : Fin 6, chartOctaProjection atomIndex atomIndex = ((3 : ℕ) : ℝ)
    rw [Fin.sum_univ_six]
    norm_num [chartOctaProjection]
  weight_pos := by intro atomIndex; norm_num [chartOctaWeight]
  weight_sum_one := by norm_num [chartOctaWeight, Fin.sum_univ_six]
  activeWeight_nonneg := by intro activeLabel _; norm_num [chartOctaMultiplierWeight]
  activeWeight_sum_one := by norm_num [chartOctaMultiplierWeight, Fin.sum_univ_six]
  activeSubset_card := by intro activeLabel _; fin_cases activeLabel <;> decide
  tightDir_unit := by
    intro activeLabel _
    simp [chartOctaTightDir]
  tightDir_support := by
    intro activeLabel _ atomIndex hnotMem
    have hdistinct : atomIndex ≠ activeLabel := by
      intro hequal
      rw [hequal] at hnotMem
      revert hnotMem
      fin_cases activeLabel <;> decide
    rw [chartOctaTightDir, Pi.single_apply, if_neg hdistinct]
  tightDir_isTight := by
    intro activeLabel _ atomIndex hmem
    have hcolumn : (chartStationaryGap chartOctaProjection chartOctaWeight
        *ᵥ chartOctaTightDir activeLabel) atomIndex
        = chartStationaryGap chartOctaProjection chartOctaWeight atomIndex activeLabel := by
      rw [chartOctaTightDir, Matrix.mulVec_single_one]
      rfl
    rw [hcolumn, chartOctaTightDir, Pi.single_apply, chartStationaryGap]
    fin_cases activeLabel <;> fin_cases atomIndex <;>
      simp_all [chartOctaSubset, chartOctaProjection, chartOctaWeight, chartOctaAxis,
        Matrix.sub_apply] <;> norm_num
  assembly_diagonal := by
    intro atomIndex
    rw [chartOctaMultiplierAssembly_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
    norm_num
  assembly_commutes := by
    rw [chartOctaMultiplierAssembly_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]

/-- **The bundle is inhabited.**  Every theorem above is a statement about a
non-empty class — and the witness is at the OPEN cell `(6,3)`, not at a decided
one. -/
theorem exists_isChartStationaryData :
    ∃ (projection : Matrix (Fin 6) (Fin 6) ℝ) (weight : Fin 6 → ℝ) (value : ℝ)
      (activeSubset : Fin 6 → Finset (Fin 6)) (activeWeight : Fin 6 → ℝ)
      (tightDir : Fin 6 → (Fin 6 → ℝ)),
      IsChartStationaryData 3 projection weight value (Finset.univ : Finset (Fin 6))
        activeSubset activeWeight tightDir :=
  ⟨chartOctaProjection, chartOctaWeight, 1 / 3, chartOctaSubset, chartOctaMultiplierWeight,
    chartOctaTightDir, chartOctaProjection_isChartStationaryData⟩

/-- **THE TWO-SIDED BOUND IS FALSE.**  The brief this file was built from asserts
`|value| ≤ 1/size` as a consequence of the weight floor.  Only the negative half
survives: the octahedron datum has `value = 1/3 = 2/size`, twice the claimed
ceiling.

So `neg_inv_size_le_value_of_isChartStationaryData` is sharp in the only direction
it can be, and no later edit may silently upgrade it to the two-sided form without
tripping this theorem.  [The witness is also ADMISSIBLE and is NOT a minimiser —
both EXACT, outside Lean, not mechanized; see the section header.] -/
theorem not_forall_value_le_inv_size_of_isChartStationaryData :
    ¬ ∀ (size rank : ℕ) (projection : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
        (value : ℝ) (activeSubset : Fin size → Finset (Fin size)) (activeWeight : Fin size → ℝ)
        (tightDir : Fin size → (Fin size → ℝ)),
        IsChartStationaryData rank projection weight value (Finset.univ : Finset (Fin size))
          activeSubset activeWeight tightDir → value ≤ ((size : ℝ))⁻¹ := by
  intro hbound
  have hoctahedron := hbound 6 3 chartOctaProjection chartOctaWeight (1 / 3) chartOctaSubset
    chartOctaMultiplierWeight chartOctaTightDir chartOctaProjection_isChartStationaryData
  norm_num at hoctahedron

end Gtz
