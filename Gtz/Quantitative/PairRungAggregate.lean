/-
# The pair rung of the averaging ladder

`Gtz.Quantitative.ChartHadamard` proves the pair conservation law on the CHART:
the off-diagonal mass of the `2 x 2` gap minors `w_c w_d - P_cd²` is the
design-blind constant `(rank - 1)² - rank` plus the correction
`Σ_c t_c (2 P_cc - t_c)` (`Gtz.sum_offDiag_chartGapPairMinor`).  Nothing in the
tree carries that law back across the weight congruence into the ATOM
coordinates where `Gtz.GoodTripleGraph` states the compatibility predicates, so
the two layers speak past each other.  This file is that bridge and its two
rank-three consequences.

The bridge is entrywise and needs no hypothesis:

    `t_c t_d * pairMinor c d  =  chartGapPairMinor P t c d` ,

because `P_cc = t_c |g_c|²` (`Gtz.projectionOfDesign_diagonal`) makes
`P_cc - t_c = t_c * heavyExcess c`, and `P_cd² = t_c t_d ⟨g_c,g_d⟩²`
(`Gtz.sq_projectionOfDesign_apply`) makes the squared entry the weighted squared
atom pairing.  So the chart's `(I6)` layer is a statement about `Gtz.pairMinor`
that had simply never been read as one.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `weight_mul_weight_mul_pairMinor_eq_chartGapPairMinor` — the entrywise bridge.
* `sum_offDiag_weight_mul_pairMinor` — the pair conservation law in atom
  coordinates at rank three: the weighted off-diagonal total of the pair minors
  is `1 + Σ_c t_c² (2 l_c - 1)`.
* `one_le_sum_offDiag_weight_mul_pairMinor` — under `Gtz.AllHeavy` the
  correction is nonnegative, so the total is at least one.
* `exists_pos_pairMinor_of_allHeavy` — hence every all-heavy rank-three design
  owns a pair of distinct atoms at STRICTLY positive gap minor.

## NOT PROVED here

Nothing about triples.  The contrast is the point of the rung: at a uniform
weight the shipped `3`-subset aggregate is the design-independent NEGATIVE
constant (`Gtz.sum_det_subsetSum_sub_one_uniform`), so averaging over triples
provably cannot produce a dominating triple, while averaging over pairs
produces a strictly compatible pair.  The ladder climbs to `j = rank - 1` and
dies at `j = rank`.  A strictly positive pair minor is NECESSARY for the pair to
sit inside a dominating triple and nothing more; the tie leg is untouched.

The shipped `Gtz.exists_pos_chartGapPairMinorSum_of_allHeavy` is weaker in
exactly the way that matters here: it produces a three-element subset whose SUM
of three pair minors is positive, not a single strictly positive pair.

Provenance: scratch report 14 (`/tmp/gtz-wf/algebra-angle/final.lean`, Part I,
namespace `GtzPairLadder`).  Five of that file's eight Part-I declarations were
a re-derivation of the shipped ChartHadamard chain and are dropped; what
survives is stated against the shipped chain instead of re-proving it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.GoodTripleGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## The bridge between the chart minor and the atom minor -/

/-- **THE ENTRYWISE BRIDGE.**  The weight-weighted pair minor of the atoms IS the
chart's `2 x 2` gap minor, at every ordered pair and with no hypothesis: the
weight congruence carries one to the other exactly.  Both sides equal
`t_c t_d ((l_c - 1)(l_d - 1) - ⟨g_c,g_d⟩²)`. -/
theorem weight_mul_weight_mul_pairMinor_eq_chartGapPairMinor (design : WeightedDesign size 3)
    (firstIndex secondIndex : Fin size) :
    design.weight firstIndex * design.weight secondIndex
        * pairMinor design firstIndex secondIndex
      = chartGapPairMinor (projectionOfDesign design) design.weight firstIndex secondIndex := by
  simp only [pairMinor, heavyExcess, atomPairing, chartGapPairMinor]
  rw [projectionOfDesign_diagonal, projectionOfDesign_diagonal, sq_projectionOfDesign_apply]
  ring

/-! ## The pair conservation law, in atom coordinates -/

/-- **THE PAIR CONSERVATION LAW AT RANK THREE.**  The weight-weighted total of the
pair minors over ordered pairs of DISTINCT atoms is `1` plus the correction
`Σ_c t_c² (2 l_c - 1)`.  The constant is the rank-three reading of the shipped
general constant `(rank - 1)² - rank`, which is `1` at rank three and `-1` at rank
two — the campaign brief's `1` was the rank-three specialisation all along.

This is `Gtz.sum_offDiag_chartGapPairMinor` read through the bridge above; the
content is the shipped one's, the coordinates are the atoms'. -/
theorem sum_offDiag_weight_mul_pairMinor (design : WeightedDesign size 3) :
    ∑ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
        design.weight pair.1 * design.weight pair.2 * pairMinor design pair.1 pair.2
      = 1 + ∑ atomIndex : Fin size,
          design.weight atomIndex ^ 2 * (2 * leverageOf (design.atom atomIndex) - 1) := by
  have hentry : ∀ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
      design.weight pair.1 * design.weight pair.2 * pairMinor design pair.1 pair.2
        = chartGapPairMinor (projectionOfDesign design) design.weight pair.1 pair.2 :=
    fun pair _ => weight_mul_weight_mul_pairMinor_eq_chartGapPairMinor design pair.1 pair.2
  have hcorrection : ∀ atomIndex : Fin size,
      design.weight atomIndex
          * (2 * projectionOfDesign design atomIndex atomIndex - design.weight atomIndex)
        = design.weight atomIndex ^ 2 * (2 * leverageOf (design.atom atomIndex) - 1) := by
    intro atomIndex
    rw [projectionOfDesign_diagonal]
    ring
  rw [Finset.sum_congr rfl hentry,
    sum_offDiag_chartGapPairMinor (projectionOfDesign_transpose design)
      (projectionOfDesign_mul_self design) (trace_projectionOfDesign design)
      design.weight_sum_one,
    Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hcorrection atomIndex]
  norm_num

/-- **THE PAIR RUNG IS POSITIVE UNDER ALL-HEAVINESS.**  Every correction term is
nonnegative once no atom is light, so the whole off-diagonal mass is at least the
rank-three constant `1`. -/
theorem one_le_sum_offDiag_weight_mul_pairMinor {design : WeightedDesign size 3}
    (hheavy : AllHeavy design) :
    1 ≤ ∑ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
        design.weight pair.1 * design.weight pair.2 * pairMinor design pair.1 pair.2 := by
  have hcorrection : (0 : ℝ) ≤ ∑ atomIndex : Fin size,
      design.weight atomIndex ^ 2 * (2 * leverageOf (design.atom atomIndex) - 1) :=
    Finset.sum_nonneg fun atomIndex _ => by
      have hleverage := hheavy atomIndex
      nlinarith [sq_nonneg (design.weight atomIndex)]
  rw [sum_offDiag_weight_mul_pairMinor design]
  linarith

/-- **THE COMPATIBLE GRAPH IS NEVER EMPTY.**  Every all-heavy rank-three design
owns two distinct atoms whose `2 x 2` gap minor is STRICTLY positive — a pair
`{c,d}` at which `Gram - I` is positive definite, i.e. a two-element Riesz system
with lower bound one.  Positive weights turn a nonpositive minor at every
distinct pair into a nonpositive total, and the total is at least one. -/
theorem exists_pos_pairMinor_of_allHeavy {design : WeightedDesign size 3}
    (hheavy : AllHeavy design) :
    ∃ firstIndex secondIndex : Fin size,
      firstIndex ≠ secondIndex ∧ 0 < pairMinor design firstIndex secondIndex := by
  by_contra hnone
  have hnonpos : ∀ pair ∈ (Finset.univ : Finset (Fin size)).offDiag,
      design.weight pair.1 * design.weight pair.2 * pairMinor design pair.1 pair.2 ≤ 0 := by
    intro pair hmember
    have hdistinct := (Finset.mem_offDiag.mp hmember).2.2
    have hminor : pairMinor design pair.1 pair.2 ≤ 0 := by
      by_contra hpositive
      exact hnone ⟨pair.1, pair.2, hdistinct, not_le.mp hpositive⟩
    have hweights := mul_pos (design.weight_pos pair.1) (design.weight_pos pair.2)
    nlinarith [hweights, hminor]
  have hupper := Finset.sum_nonpos hnonpos
  have hlower := one_le_sum_offDiag_weight_mul_pairMinor hheavy
  linarith

end Gtz
