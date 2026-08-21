/-
# The row, not two partners: what actually refutes excess dominance at the band

`Gtz.not_excessDominates_of_two_heavy_partners` refutes excess dominance from two selected
partners of pairing magnitude at least `level` when the slot's excess is at most
`2 * level`.  On the complete-graph profile that is exactly right, and
`Gtz.not_exists_excessDominates_of_edgeLabelling` now carries it to every rank.

**It does not extend to the band.**  The registry names the successor shape as "bounded
free excess together with a meeting-pair floor".  Measured in exact rationals, no such pair
of constants exists at any band cell, and even the sharper per-slot form fails at one of
them.  This module lands the instrument that does work — the whole row — and records the
refutation of the two-partner shape so the successor is not attempted a second time.

## The three strengths, in order

* `Gtz.not_excessDominates_of_row_le` — one slot whose excess is at most its own row of
  absolute pairings refutes the block.  This is the direct negation of
  `Gtz.ExcessDominatesBlock` at that slot, and it is the weakest possible hypothesis.
* `Gtz.not_excessDominates_of_two_partners_sum` — two selected partners whose two pairings
  TOGETHER cover the excess.  Strictly weaker than the landed hypothesis, by
  `Gtz.two_partners_sum_of_level`.
* `Gtz.not_excessDominates_of_two_heavy_partners` (landed) — two partners each of magnitude
  `level` with excess at most `2 * level`.

[MEASURED in exact rationals over the graphic designs of the complete graph on five and six
vertices and their edge deletions, calibrated against the landed `K4` values (free excess
`1 / 3`, meeting pairing `1 / 4`, deficit `1 / 6`).  Every selection of every one of these
designs has EVERY slot's excess strictly below its row sum, so the row instrument refutes
dominance everywhere.  The landed `2 * level` form holds at the threshold cells `K4`, `K5`,
`K6` and FAILS at all four band cells tested — `K5` less one edge, `K5` less two adjacent,
`K5` less two disjoint, `K6` less one edge, `K6` less three edges.  The intermediate SUM
form holds at all of those except `K5` less two disjoint edges, size eight at rank four.
The numbers are in `scratchpad/NOTES-rankfour.txt`.]
-/
import Mathlib
import Gtz.Wave.ThresholdCellDominance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Finset

variable {size rank : ℕ}

/-! ## 1. The weakest hypothesis: one row -/

/-- **A SLOT COVERED BY ITS OWN ROW REFUTES EXCESS DOMINANCE.**  Excess dominance asks every
slot's excess to exceed the sum of the absolute pairings in its row, so a single slot where
that fails kills the block.  This is the direct negation, and no hypothesis weaker than it
can refute the criterion. -/
theorem not_excessDominates_of_row_le (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank) (slot : Fin rank)
    (hrow : projectionOfDesign design (selected.orderEmbOfFin hcard slot)
              (selected.orderEmbOfFin hcard slot)
            - design.weight (selected.orderEmbOfFin hcard slot)
          ≤ ∑ other ∈ Finset.univ.erase slot,
              |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
                (selected.orderEmbOfFin hcard other)|) :
    ¬ ExcessDominatesBlock design selected hcard := fun hdom =>
  absurd (hdom slot) (not_lt.mpr hrow)

/-! ## 2. Two partners, added rather than levelled -/

/-- **TWO PARTNERS WHOSE PAIRINGS TOGETHER COVER THE EXCESS.**  No common level and no
symmetry between the two magnitudes: their SUM is what the row needs. -/
theorem not_excessDominates_of_two_partners_sum (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (hcard : selected.card = rank)
    {slot first second : Fin rank} (hfirst : first ≠ slot) (hsecond : second ≠ slot)
    (hne : first ≠ second)
    (hcover : projectionOfDesign design (selected.orderEmbOfFin hcard slot)
                (selected.orderEmbOfFin hcard slot)
              - design.weight (selected.orderEmbOfFin hcard slot)
            ≤ |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
                 (selected.orderEmbOfFin hcard first)|
              + |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
                   (selected.orderEmbOfFin hcard second)|) :
    ¬ ExcessDominatesBlock design selected hcard := by
  refine not_excessDominates_of_row_le design selected hcard slot (le_trans hcover ?_)
  exact two_le_sum_of_two_members
    (fun other => |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard other)|)
    (fun _ => abs_nonneg _) hfirst hsecond hne

/-- **THE SUM FORM IS WEAKER THAN THE LEVEL FORM.**  A common level with excess at most
twice it gives the sum, so the landed hypothesis implies this one and not conversely. -/
theorem two_partners_sum_of_level {level first second excess : ℝ}
    (hfirst : level ≤ first) (hsecond : level ≤ second) (hexcess : excess ≤ 2 * level) :
    excess ≤ first + second := by linarith

/-! ## 3. The band verdict

The two-partner shape the registry names as the successor is refuted by measurement, and
the row is what survives.  The theorem below is the shape a band producer must supply: not
a pair of constants, but a covered slot at every selection. -/

/-- **THE HYPOTHESIS A BAND PRODUCER MUST SUPPLY.**  At every selection, some slot's excess
is at most its own row of absolute pairings.  Measured true at every band cell tested, and
strictly weaker than any constant-level profile. -/
def RowCoveredAtEverySelection (design : WeightedDesign size rank) : Prop :=
  ∀ selected : Finset (Fin size), ∀ hcard : selected.card = rank, ∃ slot : Fin rank,
    projectionOfDesign design (selected.orderEmbOfFin hcard slot)
        (selected.orderEmbOfFin hcard slot)
      - design.weight (selected.orderEmbOfFin hcard slot)
    ≤ ∑ other ∈ Finset.univ.erase slot,
        |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
          (selected.orderEmbOfFin hcard other)|

/-- **A ROW-COVERED DESIGN ADMITS NO EXCESS DOMINATED SELECTION.** -/
theorem not_exists_excessDominates_of_rowCovered {design : WeightedDesign size rank}
    (hcovered : RowCoveredAtEverySelection design) :
    ¬ ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
        ExcessDominatesBlock design selected hcard := by
  rintro ⟨selected, hcard, hdom⟩
  obtain ⟨slot, hslot⟩ := hcovered selected hcard
  exact not_excessDominates_of_row_le design selected hcard slot hslot hdom

/-- **AND IT REFUTES THE FRONTIER PRODUCER'S HYPOTHESIS.**  One row-covered design of a cell
is enough. -/
theorem not_forall_excessDominates_of_rowCovered {design : WeightedDesign size rank}
    (hcovered : RowCoveredAtEverySelection design) :
    ¬ ∀ other : WeightedDesign size rank,
        ∃ selected : Finset (Fin size), ∃ hcard : selected.card = rank,
          ExcessDominatesBlock other selected hcard := fun hall =>
  not_exists_excessDominates_of_rowCovered hcovered (hall design)

/-- **THE COMPLETE-GRAPH PROFILE IS ROW COVERED, AT EVERY RANK.**  So the row instrument
subsumes the profile route of `Gtz.not_exists_excessDominates_of_edgeLabelling` and extends
past it. -/
theorem rowCovered_of_crowded_profile {design : WeightedDesign size rank}
    {meets : Fin size → Fin size → Prop} (hprofile : CompleteGraphProfile design meets)
    (hrank : 0 < rank)
    (hcrowded : ∀ selected : Finset (Fin size), ∀ hcard : selected.card = rank,
      ∃ slot first second : Fin rank, first ≠ slot ∧ second ≠ slot ∧ first ≠ second ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard first) ∧
        meets (selected.orderEmbOfFin hcard slot) (selected.orderEmbOfFin hcard second)) :
    RowCoveredAtEverySelection design := by
  intro selected hcard
  obtain ⟨slot, first, second, hfirst, hsecond, hne, hmeetFirst, hmeetSecond⟩ :=
    hcrowded selected hcard
  refine ⟨slot, ?_⟩
  have hemb : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  have hexcLe : projectionOfDesign design (selected.orderEmbOfFin hcard slot)
        (selected.orderEmbOfFin hcard slot)
      - design.weight (selected.orderEmbOfFin hcard slot)
      ≤ 2 * (1 / ((rank : ℝ) + 1)) := by
    rw [excess_completeGraphProfile hprofile hrank]
    exact le_of_lt (excess_lt_two_heavy_completeGraphProfile hrank)
  have hcover := two_partners_sum_of_level
    (hprofile.heavy _ _ (fun h => hfirst (hemb h.symm)) hmeetFirst)
    (hprofile.heavy _ _ (fun h => hsecond (hemb h.symm)) hmeetSecond)
    hexcLe
  refine le_trans hcover ?_
  exact two_le_sum_of_two_members
    (fun other => |projectionOfDesign design (selected.orderEmbOfFin hcard slot)
      (selected.orderEmbOfFin hcard other)|)
    (fun _ => abs_nonneg _) hfirst hsecond hne

end Gtz
