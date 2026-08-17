/-
# The leverage floor of a tie, spent on the two off-path registry axioms

## What this file does NOT do

It does not prove the leverage floor.  That is landed, and this file consumes it:

* `Gtz.exists_deflatedGapBound` (Gtz/Design/StratumEmptinessLedger.lean:399) —
  the deflation gap floor, division free, in exactly the form
  `((1 - t_d) * (S_C - 1) - t_d * (1 - A_d)).PosSemidef`;
* `Gtz.exists_posDef_of_lightAtom` (:509) — the STRICT dominator from a strictly
  light atom, which also returns `dropLabel ∉ selected`;
* `Gtz.not_isTie_of_lightAtom` (:544);
* `Gtz.leverage_one_le_of_isTie` (:557) — every atom of a tie is heavy, granted
  weighted GTZ one size down;
* `Gtz.leverage_one_le_of_isTie_sixThree` (:574) — the same at `(6,3)` with NO
  hypothesis, because `Gtz.gtzWeighted_of_le_five` supplies the predecessor.

An earlier draft of this file re-proved all five under different names.  The
names did not collide, which is exactly why a name scan does not catch a
re-derivation.  Only the STATEMENTS collide.  They are deleted.

## What this file does

The two off-path registry axioms both conclude `IsTie design -> HasParallelPair
design`, and both hand over `Gtz.GtzWeighted (size - 1) rank` as a hypothesis.
The four producers landed for them before this file — two in
`Gtz/Wave/OffsetUpperBound.lean` and two in `Gtz/Wave/ThresholdCellDominance.lean`
— all ask for excess dominance, and all four hypotheses are refuted: at `(6,3)`
by `Gtz.not_forall_excessDominates_sixThree_unconditional`, and at rank four on
the complete graph less an edge.  So both axioms have no live producer.

Nobody spent the predecessor.  The leverage floor is exactly what it buys, and
these three theorems spend it:

* `Gtz.obligationThresholdCellHingeRankFourAndUp_of_heavyTie`
* `Gtz.obligationSubThresholdBandHinge_of_heavyTie`
* `Gtz.hingeConclusion_sixThree_of_heavyTie`

Each asks only that a tie whose every label is heavy carries a parallel pair.
The registry's own predecessor hypothesis discharges the heaviness, so nothing at
all is assumed about a design carrying a light label.  At `(6,3)` the predecessor
is landed, so the third theorem carries no hypothesis beyond the all-heavy
decision itself.

That is strictly weaker than excess dominance, and unlike excess dominance it
does not prove the implication by refuting its own antecedent: a heavy tie is
exactly the object the axiom is about.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.StratumEmptinessLedger

namespace Gtz

open Matrix

/-! ### 1.  The landed floor at a general size

`Gtz.leverage_one_le_of_isTie` is stated at `WeightedDesign (m + 1) k`.  Both
registry axioms quantify a bare `size`, so the floor needs one transport before
it can be spent.  This is the only lemma in the file. -/

/-- The landed leverage floor, transported from the successor shape to a bare
size.  `Gtz.leverage_one_le_of_isTie` does the work. -/
theorem forall_leverage_one_le_of_isTie {size rank : ℕ} (hsize : 2 ≤ size)
    (hrec : GtzWeighted (size - 1) rank)
    (D : WeightedDesign size rank) (htie : IsTie D) :
    ∀ label : Fin size, 1 ≤ leverageOf (D.atom label) := by
  obtain ⟨n, rfl⟩ : ∃ n, size = n + 1 := ⟨size - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hrec
  exact fun label => leverage_one_le_of_isTie D (by omega) hrec htie label

/-! ### 2.  The two off-path producers -/

/-- **A PRODUCER FOR THE THRESHOLD-CELL HINGE, SPENDING THE PREDECESSOR.**  Its
hypothesis asks only that a tie whose every label is heavy carries a parallel
pair.  The registry's own predecessor hypothesis discharges the heaviness
through the landed leverage floor, so nothing is assumed about a design carrying
a light label.

Contrast with the four landed producers, which ask for an excess-dominated
selection at EVERY design of the cell.  That hypothesis refutes `Gtz.IsTie`
outright, so it is strictly stronger than the axiom, and it is false. -/
theorem obligationThresholdCellHingeRankFourAndUp_of_heavyTie
    (hheavy : ∀ rank : ℕ, 4 ≤ rank →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) →
          IsTie design → HasParallelPair design) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hrec design htie
  have hsize : 2 ≤ rank * (rank + 1) / 2 := by
    have hmono : 4 * 5 / 2 ≤ rank * (rank + 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul hrank (by omega))
    omega
  exact hheavy rank hrank design
    (forall_leverage_one_le_of_isTie hsize hrec design htie) htie

/-- **A PRODUCER FOR THE SUB-THRESHOLD BAND HINGE, SPENDING THE PREDECESSOR.**
Same shape on the band's cells.  The band's own lower bound `2 * rank <= size`
supplies the two labels the floor needs. -/
theorem obligationSubThresholdBandHinge_of_heavyTie
    (hheavy : ∀ rank : ℕ, 3 ≤ rank → ∀ size : ℕ, 2 * rank ≤ size →
      size < rank * (rank + 1) / 2 → ∀ design : WeightedDesign size rank,
        (∀ label, 1 ≤ leverageOf (design.atom label)) →
          IsTie design → HasParallelPair design) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank size hlow hhigh hrec design htie
  have hsize : 2 ≤ size := by omega
  exact hheavy rank hrank size hlow hhigh design
    (forall_leverage_one_le_of_isTie hsize hrec design htie) htie

/-- **AT `(6,3)` A DECISION ON THE ALL-HEAVY STRATUM CLOSES THE HINGE
OUTRIGHT.**  No predecessor hypothesis appears, because the landed
`Gtz.leverage_one_le_of_isTie_sixThree` already supplies it from
`Gtz.gtzWeighted_of_le_five`.

**#VACUITY — THIS RECORDS NO PROGRESS.**  The heaviness is FREE at `(6,3)`, by
the very theorem this docstring names.  So the hypothesis is equivalent to the
conclusion, and `Gtz.heavyTie_hingeConclusion_iff_hingeHoldsAtSize_six_three`
(Gtz/Wave/WiringResidualEquivalence.lean) proves the equivalence.  The theorem
is a convenience for a prover, not a reduction. -/
theorem hingeConclusion_sixThree_of_heavyTie
    (hheavy : ∀ design : WeightedDesign 6 3,
      (∀ label, 1 ≤ leverageOf (design.atom label)) →
        IsTie design → HasParallelPair design) :
    ∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design :=
  fun design htie =>
    hheavy design
      (fun label => leverage_one_le_of_isTie_sixThree design htie label) htie

end Gtz
