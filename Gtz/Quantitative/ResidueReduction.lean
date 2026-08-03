/-
# The residue reduction: rank-three GTZ as one named proposition

This module joins two things that were landed in the same campaign but never
connected: the vertex-exclusion payoff of `Gtz/Quantitative/VertexExclusion.lean`
and the shipped all-heavy collapse of `Gtz/Quantitative/SevenThreeCollapse.lean`.
The join is short, and its conclusion is the sharpest statement of the frontier
the tree carries:

    (∀ n, 0 < n → GtzOriginal n 3)  ↔  ExceptionalDesignsDominate 6

The left side is the 1997 Goreinov-Tyrtyshnikov-Zamarashkin conjecture at rank
three, for every ambient size.  The right side quantifies over all-heavy `(6,3)`
designs whose phase-free image lies in `Gtz.PhaseFreeData.IsExceptional` — the
explicit residue left after the two moduli mechanisms of that file, the
sign-blind certificate and the light-edge obstruction, have both been applied.

## Why this is a reduction and not a restatement

Every faithful reduction target is logically equivalent to its source, so
equivalence is not by itself evidence of progress; what matters is that the
quantifier range strictly shrinks and that the discarded part is discharged by a
theorem rather than by assumption.  Both hold here.

* The discarded part is discharged by `Gtz.exists_dominates_of_not_isExceptional`,
  which is unconditional.
* The shrink is strict: `Gtz.exists_allHeavy_not_isExceptional_six` names an
  all-heavy `(6,3)` design outside the new quantifier, namely the icosahedron.

## What is NOT claimed

The residue is not empty, so this reduction does not prove anything.  Emptiness
of the residue at the design level — the statement

    ∀ D : WeightedDesign 6 3, AllHeavy D → ¬ (phaseFreeOfDesign D).IsExceptional

— would imply the conjecture through
`Gtz.exceptionalDesignsDominate_of_forall_not_isExceptional` below, and it is
FALSE.  Six exact rational data produced independently during this campaign are
admissible, all-heavy, satisfy `triangleCap` with equality (so each is the
phase-free image of a genuine real weighted design, obtained by factoring the
Parseval projection), and satisfy both clauses of the residue predicate; every
one of them nonetheless carries between three and seven dominating triples.
That computation is exact rational arithmetic but is NOT kernel-checked here,
because the designs realising those data have irrational atoms.  Supplying one
in Lean is the outstanding obligation this module leaves behind, and until it is
supplied the emptiness route is refuted only outside the kernel.

## Generality

`Gtz.gtzWeightedHeavy_iff_exceptionalDesignsDominate` is stated at general size
with only `3 ≤ size`, since `Gtz.exists_dominates_of_not_isExceptional` is.  The
rank is pinned at three by the substrate, not by this file:
`Gtz.IsPhaseFreeAdmissible` hardcodes `traceEqRank` at three and
`Gtz.phaseFreeOfDesign` consumes a `Gtz.WeightedDesign size 3`.  Only the descent
to the two named cells is per-size, and it is per-size because the shipped
collapses `Gtz.gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three` and
`Gtz.gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three` are.
-/
import Mathlib
import Gtz.Quantitative.VertexExclusion
import Gtz.Quantitative.VertexInstances
import Gtz.Quantitative.SevenThreeCollapse
import Gtz.Reduction.ConverseBridge
import Gtz.Reduction.StressWalk

namespace Gtz

/-! ## The named proposition -/

/-- **THE RESIDUE.**  Every all-heavy design whose phase-free image is
exceptional has a dominating triple.

The hypothesis `(phaseFreeOfDesign D).IsExceptional` is what the two mechanisms
of `Gtz/Quantitative/VertexExclusion.lean` cannot see: no triple in the
nonnegative-trace class is sign-blind good, and every light edge carries a star
triple that leaves that class or breaks the band.  Outside it,
`Gtz.exists_dominates_of_not_isExceptional` already produces the triple. -/
def ExceptionalDesignsDominate (size : ℕ) : Prop :=
  ∀ D : WeightedDesign size 3, AllHeavy D → (phaseFreeOfDesign D).IsExceptional →
    ∃ selected : Finset (Fin size), selected.card = 3 ∧ Dominates D selected

/-! ## The reduction, at general size -/

/-- **THE REDUCTION.**  All-heavy GTZ at rank three is exactly the residue
statement, at every size from three up.

Forward is weakening: a hypothesis is dropped.  Backward is the case split that
gives the file its point — on the residue the hypothesis is available, and off it
`Gtz.exists_dominates_of_not_isExceptional` closes the goal unconditionally. -/
theorem gtzWeightedHeavy_iff_exceptionalDesignsDominate {size : ℕ} (hsize : 3 ≤ size) :
    GtzWeightedHeavy size 3 ↔ ExceptionalDesignsDominate size := by
  constructor
  · intro hheavy D hallHeavy _
    exact hheavy D hallHeavy
  · intro hresidue D hallHeavy
    by_cases hexceptional : (phaseFreeOfDesign D).IsExceptional
    · exact hresidue D hallHeavy hexceptional
    · exact exists_dominates_of_not_isExceptional D hallHeavy hsize hexceptional

/-! ## Descent to the named cells -/

/-- **THE CELL.**  Heaviness is not a restriction at `(6,3)` — that is the
shipped `Gtz.gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three` — so the
residue statement at size six IS the campaign's single open cell. -/
theorem gtzWeighted_six_three_iff_exceptionalDesignsDominate :
    GtzWeighted 6 3 ↔ ExceptionalDesignsDominate 6 :=
  gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three.symm.trans
    (gtzWeightedHeavy_iff_exceptionalDesignsDominate (by norm_num))

/-- The size-seven residue is the same proposition, through the shipped
`Gtz.gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three`.  So the reduction
does not have to be re-run at the `(7,3)` window. -/
theorem exceptionalDesignsDominate_seven_iff_gtzWeighted_six_three :
    ExceptionalDesignsDominate 7 ↔ GtzWeighted 6 3 :=
  (gtzWeightedHeavy_iff_exceptionalDesignsDominate (size := 7) (by norm_num)).symm.trans
    gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three

/-- Rank three at every size, through `Gtz.rank_three_iff_six_three`. -/
theorem gtzWeightedAll_three_iff_exceptionalDesignsDominate :
    GtzWeightedAll 3 ↔ ExceptionalDesignsDominate 6 :=
  rank_three_iff_six_three.trans gtzWeighted_six_three_iff_exceptionalDesignsDominate

/-- **THE HEADLINE.**  The original 1997 conjecture at rank three, for every
ambient size, is one named proposition about the residue of a single `(6,3)`
mechanism.  Every arrow in the chain is a kernel theorem: the weighted-to-original
bridge `Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three`, the
all-heavy collapse, and the residue reduction above. -/
theorem forall_gtzOriginal_rank_three_iff_exceptionalDesignsDominate :
    (∀ n : ℕ, 0 < n → GtzOriginal n 3) ↔ ExceptionalDesignsDominate 6 :=
  gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three.symm.trans
    gtzWeighted_six_three_iff_exceptionalDesignsDominate

/-! ## The crux route

An independent path to the same conclusion, through the cage rather than through
the all-heavy collapse.  It is worth recording because it is the route that
consumes `Gtz.SixThreeCrux.isExceptional_phaseFree`, and because it shows the
reduction does not depend on the heavy-collapse machinery. -/

/-- **THE CAGE ROUTE.**  A counterexample carrier is all-heavy and has no
dominating triple, and by the cage its phase-free image is exceptional — so the
residue statement contradicts it directly.  Composed with the shipped
`Gtz.gtzWeighted_six_three_of_isEmpty_sixThreeCrux` this re-derives
`Gtz.gtzWeighted_six_three_iff_exceptionalDesignsDominate` without the collapse. -/
theorem isEmpty_sixThreeCrux_of_exceptionalDesignsDominate
    (hresidue : ExceptionalDesignsDominate 6) : IsEmpty SixThreeCrux := by
  refine ⟨fun crux => ?_⟩
  obtain ⟨selected, hcard, hdominates⟩ :=
    hresidue crux.design crux.isAllHeavy crux.isExceptional_phaseFree
  exact crux.hasNoDominatingTriple selected hcard hdominates

/-! ## Where the reduction stands

Two facts about the new quantifier, on opposite sides.  The first says the shrink
is real; the second says the residue is the whole remaining problem, because
emptying it is sufficient — and, per the header, that sufficient condition is
measurably false. -/

/-- **THE SHRINK IS STRICT.**  The icosahedron is all-heavy and outside the
residue, so `Gtz.ExceptionalDesignsDominate 6` quantifies over strictly fewer
designs than `Gtz.GtzWeightedHeavy 6 3` does.  The exclusion is by the light-edge
mechanism alone: clause one of the residue HOLDS at the icosahedron, since every
excess gap there is `-14/5`. -/
theorem exists_allHeavy_not_isExceptional_six :
    ∃ D : WeightedDesign 6 3, AllHeavy D ∧ ¬ (phaseFreeOfDesign D).IsExceptional :=
  ⟨icosaDesign, icosaDesign_allHeavy, not_isExceptional_phaseFreeOfDesign_icosaDesign⟩

/-- **THE EMPTINESS ROUTE, RECORDED.**  If no all-heavy design had an exceptional
image the residue statement would hold vacuously, hence the conjecture.  This is
the route a reader will reach for first, and it is a dead end: see the header —
six exact rational data of this campaign are admissible, all-heavy, saturated and
exceptional, so the hypothesis below is false at size six.  The implication is
landed anyway, so that the dead end is on the record rather than rediscovered. -/
theorem exceptionalDesignsDominate_of_forall_not_isExceptional {size : ℕ}
    (hnone : ∀ D : WeightedDesign size 3, AllHeavy D →
      ¬ (phaseFreeOfDesign D).IsExceptional) :
    ExceptionalDesignsDominate size :=
  fun D hallHeavy hexceptional => absurd hexceptional (hnone D hallHeavy)

end Gtz
