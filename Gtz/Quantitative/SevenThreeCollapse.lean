/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Quantitative.SixThreeCruxPropagation
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.HeavyTraceFrame

/-!
# The `(7,3)` lane collapses onto `(6,3)`, and its production theorems are VACUOUS

`Gtz.Reduction.StressWalk` landed the arrow `Gtz.gtzWeighted_seven_three_of_six_three`.
Size monotonicity had always supplied the other direction.  Together with the shipped
all-heavy monotonicity `Gtz.gtzWeightedHeavy_of_succ` and the all-heavy top object
`Gtz.rank_three_of_heavy_top`, that closes a cycle: FIVE propositions the campaign
tracks as separate targets are ONE proposition.

The cycle has a consequence nobody recorded.  Several `(7,3)` theorems predate the
walk and carry BOTH `Gtz.GtzWeighted 6 3` AND a `(7,3)` failure hypothesis.  Once the
cycle closed, those two hypotheses became CONTRADICTORY, so the theorems became
vacuously true and stopped carrying information.  They are still theorems; they are no
longer statements about anything.

## WHAT LANDS

* `Gtz.gtzWeightedHeavy_of_gtzWeighted` — the trivial arrow, stated once.
* `Gtz.gtzWeighted_six_three_iff_gtzWeightedHeavy_seven_three` and siblings — the
  collapse, as iffs.
* `Gtz.false_of_gtzWeighted_six_three_of_not_gtzWeighted_seven_three`,
  `Gtz.false_of_gtzWeighted_six_three_of_not_gtzWeightedHeavy_seven_three`,
  `Gtz.false_of_gtzWeighted_six_three_of_forall_not_dominates_sevenThree` — the three
  VACUITY CERTIFICATES.  Each says, in the kernel, that a hypothesis pair used by a
  shipped `(7,3)` theorem is empty.  The affected theorems are, verbatim:
  `Gtz.nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three`,
  `Gtz.exists_allHeavy_minimiser_sevenThree`,
  `Gtz.exists_collared_allHeavy_minimiser_sevenThree`,
  `Gtz.allHeavy_and_two_thirds_seven_three`,
  `Gtz.deflationLevel_lt_one_seven_three`.
* `Gtz.nonempty_sixThreeCrux_iff_not_gtzWeighted_seven_three` and siblings — the
  HONEST `(7,3)` normal form.  `Gtz.SevenThreeCrux` has no production theorem left, so
  a `(7,3)` counterexample is not known to be realised in that shape; but a `(7,3)`
  failure IS realised, unconditionally, at a `Gtz.SixThreeCrux`.

## WHAT THIS DOES NOT DO

NOTHING HERE APPROACHES `Gtz.GtzWeighted 6 3`.  Every arrow below is a composition of
shipped theorems; the mathematics is in `Gtz/Reduction/StressWalk.lean` and
`Gtz/Reduction/RankFourWindow.lean`.  This file records a bookkeeping fact about the
`(7,3)` lane and repairs the statements that the fact hollowed out.  It does not refute
`Gtz.SevenThreeCrux` either: whether that structure is inhabited when the cell fails is
now simply UNKNOWN, where before it looked settled.
-/

namespace Gtz

/-! ## 1. The trivial arrow: SHIPPED, consumed rather than rebuilt

The prototype this module was harvested from opened with its own

    theorem gtzWeightedHeavy_of_gtzWeighted (hgtz : GtzWeighted size rank) :
        GtzWeightedHeavy size rank := fun design _ => hgtz design

and reported that none of its names collided anywhere in the tree.  That name is
`Gtz.gtzWeightedHeavy_of_gtzWeighted`, and it has been in the TRACKED, pre-existing
`Gtz/Reduction/HeavyTraceFrame.lean` since before this campaign, with a
character-identical statement and a character-identical proof.  Nothing hard-errored,
because a duplicate `Gtz`-level name in a DIFFERENT module is kept silently.  The
declaration is gone from this module and `Gtz.Reduction.HeavyTraceFrame` is imported
instead, so every use below resolves to the shipped theorem under the same name.

That the module which already owned the theorem is itself a written record of this
exact hazard -- its header says "the author worked the weight-floor route at length
before checking whether the tree already had a cleaner one.  It did." -- is worth
the reader's attention. -/

/-! ## 2. The collapse

`Gtz.GtzWeighted 6 3`, `Gtz.GtzWeighted 7 3`, `Gtz.GtzWeightedHeavy 6 3`,
`Gtz.GtzWeightedHeavy 7 3` and `Gtz.GtzWeightedAll 3` are one proposition.  The cycle
is `(6,3) → (7,3)` by the stress walk, `(7,3) → heavy (7,3)` trivially, `heavy (7,3) →
rank three` by `Gtz.rank_three_of_heavy_top`, and `rank three → (6,3)` by instantiation. -/

/-- The all-heavy `(7,3)` window is the frontier cell. -/
theorem gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three :
    GtzWeightedHeavy 7 3 ↔ GtzWeighted 6 3 :=
  ⟨fun hheavy => rank_three_of_heavy_top hheavy 6,
    fun hcell => gtzWeightedHeavy_of_gtzWeighted
      (gtzWeighted_six_three_iff_seven_three.mp hcell)⟩

/-- The all-heavy `(6,3)` window is the frontier cell: heaviness is not a restriction. -/
theorem gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three :
    GtzWeightedHeavy 6 3 ↔ GtzWeighted 6 3 :=
  ⟨fun hheavy => rank_three_of_heavy_six_three hheavy 6, gtzWeightedHeavy_of_gtzWeighted⟩

/-- The two all-heavy windows agree. -/
theorem gtzWeightedHeavy_seven_three_iff_six_three :
    GtzWeightedHeavy 7 3 ↔ GtzWeightedHeavy 6 3 :=
  gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three.trans
    gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three.symm

/-- The all-heavy `(7,3)` window is the whole of rank three. -/
theorem gtzWeightedHeavy_seven_three_iff_rank_three :
    GtzWeightedHeavy 7 3 ↔ GtzWeightedAll 3 :=
  gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three.trans rank_three_iff_six_three.symm

/-! ## 3. The vacuity certificates

Each item below exhibits a hypothesis pair, used verbatim by a shipped `(7,3)`
result, as CONTRADICTORY.  A reader who meets one of those results should read it as
carrying no information. -/

/-- **VACUITY, the plain form.**  The hypothesis pair of
`Gtz.nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three` and of
`Gtz.exists_allHeavy_minimiser_sevenThree` is contradictory: the frontier cell already
implies `Gtz.GtzWeighted 7 3`.  Both theorems are therefore vacuously true, and
`Gtz.SevenThreeCrux` is left with NO production theorem. -/
theorem false_of_gtzWeighted_six_three_of_not_gtzWeighted_seven_three
    (hsixThree : GtzWeighted 6 3) (hfail : ¬ GtzWeighted 7 3) : False :=
  hfail (gtzWeighted_six_three_iff_seven_three.mp hsixThree)

/-- **VACUITY, the all-heavy form.**  The hypothesis pair of
`Gtz.exists_collared_allHeavy_minimiser_sevenThree` is contradictory.  That theorem
sits in `Gtz.Reduction.ChartAttainmentWeld`, whose header marks the surrounding
material load-bearing; the collared `(7,3)` minimiser it produces is not. -/
theorem false_of_gtzWeighted_six_three_of_not_gtzWeightedHeavy_seven_three
    (hsixThree : GtzWeighted 6 3) (hfail : ¬ GtzWeightedHeavy 7 3) : False :=
  hfail (gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three.mpr hsixThree)

/-- **VACUITY, the per-design form.**  The hypothesis pair of
`Gtz.allHeavy_and_two_thirds_seven_three` and of
`Gtz.deflationLevel_lt_one_seven_three` is contradictory: under the frontier cell
every `(7,3)` design has a dominating triple, so no `(7,3)` design can be assumed
undominated alongside it. -/
theorem false_of_gtzWeighted_six_three_of_forall_not_dominates_sevenThree
    (hsixThree : GtzWeighted 6 3) (design : WeightedDesign 7 3)
    (hfail : ∀ selected : Finset (Fin 7), selected.card = 3 → ¬ Dominates design selected) :
    False := by
  obtain ⟨selected, hcard, hdominates⟩ :=
    gtzWeighted_six_three_iff_seven_three.mp hsixThree design
  exact hfail selected hcard hdominates

/-! ## 4. The honest `(7,3)` normal form

`Gtz.SixThreeCrux` needs no hypothesis to be produced, and it covers `(7,3)`. -/

/-- **THE UNCONDITIONAL `(7,3)` PRODUCTION.**  A `(7,3)` failure is realised at a
`(6,3)` crux, with no antecedent.  This is what
`Gtz.nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three` was meant to provide and,
being vacuous, does not. -/
theorem nonempty_sixThreeCrux_of_not_gtzWeighted_seven_three (hfail : ¬ GtzWeighted 7 3) :
    Nonempty SixThreeCrux :=
  nonempty_sixThreeCrux_of_not_gtzWeighted_six_three fun hcell =>
    false_of_gtzWeighted_six_three_of_not_gtzWeighted_seven_three hcell hfail

/-- **THE `(7,3)` NORMAL FORM, hypothesis-free.**  The `(6,3)` crux is a complete
normal form for `(7,3)` failure as well as for `(6,3)` failure. -/
theorem nonempty_sixThreeCrux_iff_not_gtzWeighted_seven_three :
    Nonempty SixThreeCrux ↔ ¬ GtzWeighted 7 3 :=
  ⟨fun hcrux hgtz =>
      not_gtzWeighted_six_three_of_sixThreeCrux hcrux.some
        (gtzWeighted_six_three_iff_seven_three.mpr hgtz),
    nonempty_sixThreeCrux_of_not_gtzWeighted_seven_three⟩

/-- The contrapositive reading. -/
theorem isEmpty_sixThreeCrux_iff_gtzWeighted_seven_three :
    IsEmpty SixThreeCrux ↔ GtzWeighted 7 3 := by
  rw [← not_nonempty_iff, nonempty_sixThreeCrux_iff_not_gtzWeighted_seven_three, not_not]

/-- Emptying the `(6,3)` box settles `(7,3)` directly. -/
theorem gtzWeighted_seven_three_of_isEmpty_sixThreeCrux (hempty : IsEmpty SixThreeCrux) :
    GtzWeighted 7 3 :=
  isEmpty_sixThreeCrux_iff_gtzWeighted_seven_three.mp hempty

/-- Emptying the `(6,3)` box settles the all-heavy `(7,3)` window too. -/
theorem isEmpty_sixThreeCrux_iff_gtzWeightedHeavy_seven_three :
    IsEmpty SixThreeCrux ↔ GtzWeightedHeavy 7 3 :=
  isEmpty_sixThreeCrux_iff_gtzWeighted_seven_three.trans
    (gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three.trans
      gtzWeighted_six_three_iff_seven_three).symm

end Gtz
