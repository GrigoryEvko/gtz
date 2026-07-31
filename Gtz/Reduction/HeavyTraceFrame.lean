import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LeverageBound
import Gtz.Reduction.Reductions
import Gtz.Reduction.ExchangeInvariant
import Gtz.Quantitative.ExpectedCharPolynomial

/-!
# The route correction: the all-heavy frame supersedes the weight-floor frame

Rank three has TWO independent reductions in this development, and they are not
of equal quality.

* `gtzWeightedAll_three_of_branches` (SplitTransfer) reduces `GtzWeightedAll 3`
  to FOUR obligations — a dust-drop and a spread-floor certificate at each of
  sizes six and seven — and carries a free `weightFloor` parameter whose live
  window is `(0, 1/size]` (WeightFloorWindow).
* `rank_three_of_heavy_residuals` (Reductions) reduces `GtzWeightedAll 3` to
  TWO obligations, `GtzWeightedHeavy 6 3` and `GtzWeightedHeavy 7 3`, with no
  free parameter, no parallel-pair branch, and no dust branch.

The second strictly dominates the first: fewer obligations, no parameter to
choose, and each obligation is a weakening of the plain statement at that size
(`gtzWeightedHeavy_of_gtzWeighted` below).  The reason is structural.  The
weight-floor route splits on WEIGHT, but the deflation tool that would discharge
a branch keys on LEVERAGE — `dominating_of_light_atom` needs
`leverageOf (atom d) <= 1`, and a small weight does not bound a leverage; the
only link between the two is `weighted_leverage_le_one`, which bounds their
PRODUCT.  So the weight-floor split does not line up with the tool that would
close a branch of it, whereas the all-heavy split is exactly the split that tool
induces.

Recorded because the author worked the weight-floor route at length before
checking whether the tree already had a cleaner one.  It did.

## CORRECTION, second layer: the trace observations were already here too

A first draft of this module also shipped `trace_subsetSum`, an all-heavy trace
vacuity statement, and helper lemmas for the nonnegativity of a
positive-semidefinite trace.  Every one of those already existed:

* `trace_subsetSum` — `Gtz/Quantitative/ExpectedCharPolynomial.lean`, with a
  character-identical proof.
* `rank_lt_trace_subsetSum_of_allHeavy` — `Gtz/Reduction/ExchangeInvariant.lean`,
  the same all-heavy vacuity statement in trace form.
* `Dominates design selected <-> clippedTrace design selected = rank` —
  `Gtz/Reduction/ExchangeInvariant.lean`, STRONGER than the one-directional
  trace test, since it is an equivalence.
* `trace_atomMatrix` — `Gtz/Core/Basic.lean`.
* trace nonnegativity of a PSD matrix — `Matrix.PosSemidef.trace_nonneg`, Mathlib.

The duplicates are gone; what remains below is stated ON TOP of the shipped
declarations.  Two of them were caught only because a duplicate `Gtz`-level name
does not reliably hard-error at the umbrella, so the redundancy was found by
reading the pin list rather than by the build.  That is the umbrella
duplicate-global trap doing exactly what it is known for.

## What actually remains new here

The leverage-sum reading of the trace test (the shipped forms are stated in
`Matrix.trace` and `clippedTrace`), its pruning contrapositive, and the two
comparison statements that make the route claim above machine-checked rather
than asserted.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The trace test, in leverage-sum form -/

/-- **THE TRACE TEST.**  A dominating subset's raw leverages sum to at least the
rank.  Necessary, not sufficient — but it is a scalar test, so it refutes a
candidate subset without touching an eigenvalue.  The shipped equivalence
`dominates_iff_clippedTrace_eq_rank` is sharper; this is the form that reads
directly off the leverage vector. -/
theorem rank_le_sum_leverage_of_dominates (D : WeightedDesign m k)
    (selected : Finset (Fin m)) (hdominates : Dominates D selected) :
    (k : ℝ) ≤ ∑ atomLabel ∈ selected, leverageOf (D.atom atomLabel) := by
  have htrace := hdominates.trace_nonneg
  rw [Matrix.trace_sub, trace_subsetSum, Matrix.trace_one, Fintype.card_fin] at htrace
  linarith

/-- **The pruning form.**  A subset whose leverages sum below the rank cannot
dominate, whatever its geometry. -/
theorem not_dominates_of_sum_leverage_lt_rank (D : WeightedDesign m k)
    (selected : Finset (Fin m))
    (hdeficient : ∑ atomLabel ∈ selected, leverageOf (D.atom atomLabel) < (k : ℝ)) :
    ¬ Dominates D selected := fun hdominates =>
  absurd (rank_le_sum_leverage_of_dominates D selected hdominates) (not_le.mpr hdeficient)

/-- **Every candidate subset of an all-heavy design passes the trace test.**  The
leverage-sum reading of the shipped `rank_lt_trace_subsetSum_of_allHeavy`.  Its
content is negative and it is the structural point of this module: inside the
all-heavy frame the trace test refutes nothing, so the two remaining rank-three
residuals cannot be attacked through traces at all.  Whatever closes them must
read the eigenvalue structure of the subset Gram. -/
theorem rank_lt_sum_leverage_of_allHeavy {D : WeightedDesign m k} (hheavy : AllHeavy D)
    {selected : Finset (Fin m)} (hcard : selected.card = k) (hrankPos : 0 < k) :
    (k : ℝ) < ∑ atomLabel ∈ selected, leverageOf (D.atom atomLabel) := by
  have hshipped := rank_lt_trace_subsetSum_of_allHeavy hheavy hcard hrankPos
  rwa [trace_subsetSum] at hshipped

/-! ## The route comparison, machine-checked -/

/-- **The all-heavy residual is a weakening of the plain statement**, so the
two-obligation route asks strictly less at each size than the plain conjecture
does.  Stated so the comparison in this module's header is checked rather than
asserted. -/
theorem gtzWeightedHeavy_of_gtzWeighted (hplain : GtzWeighted m k) :
    GtzWeightedHeavy m k := fun D _ => hplain D

/-- **The two-obligation frontier.**  Nothing new is proved here; this names the
two residuals that the vacuity statement above has just been shown to be blind
to, so an obstruction census can cite one entry point. -/
theorem gtzWeightedAll_three_of_heavy_frontier
    (hsixThree : GtzWeightedHeavy 6 3) (hsevenThree : GtzWeightedHeavy 7 3) :
    GtzWeightedAll 3 :=
  rank_three_of_heavy_residuals hsixThree hsevenThree

end Gtz
