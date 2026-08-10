import Gtz.Design.LineBranchFreePairAggregateBridge
import Gtz.Design.TightLineBranchLivePairBridge
import Gtz.Design.PlaneBranchNormalForm
import Gtz.Quantitative.PairRungRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The free-pair row aggregate: its algebra, its exact balance, and its consumer

Three layers over `Gtz.freePairRowAggregate`, all downstream of the sign step in
`Gtz.Design.LineBranchFreePairAggregateBridge` and independent of whatever
coordinates a proof of the aggregate sign eventually uses.

* **Algebra.**  The row aggregate collapses to one term per *unordered* free
  pair, `(u_c + u_d) * P_cd`, and at rank three the general-rank minor
  `Gtz.pairGapExcessOf` is definitionally the rank-three `Gtz.pairMinor`.
* **Balance.**  Summing the three free-centred pair-row laws splits the six-label
  row exactly into the free-free aggregate and the base-weighted cross
  aggregate, and after the global leverage trace `sum w * leverage = rank` is
  spent the weighted free-leverage terms cancel outright.  This is an exact
  identity, not a bound: no uniform positive lower bound on the aggregate
  exists, since exact positive values decay toward zero as weights do.
* **Consumer.**  With the aggregate positive and every card-three subset
  failing, the bridge hands back a live free pair and the landed refusal
  equivalence upgrades it to *every* completion of that pair refusing.  That
  conjunction is the exact downstream residual.

The consumer's hypothesis `hnoStrict` is the negation of the branch, so its
conclusion is asserted only where the branch fails -- it is contradictable in
the intended sense, and it is not a statement that happens to hold where the
branch is true.
-/

namespace Gtz


open Finset

/-- Symmetry of the two-by-two gap minor. -/
theorem pairGapExcessOf_comm {size rank : ℕ} (design : WeightedDesign size rank)
    (first second : Fin size) :
    pairGapExcessOf design first second = pairGapExcessOf design second first := by
  rw [pairGapExcessOf, pairGapExcessOf, gapPairingOf_comm design first second]
  ring

/-- The free-row aggregate written once per unordered free pair. -/
theorem freePairRowAggregate_eq_threePairs (design : WeightedDesign 6 3) :
    freePairRowAggregate design
      = (design.weight 3 + design.weight 4) * pairGapExcessOf design 3 4
        + (design.weight 3 + design.weight 5) * pairGapExcessOf design 3 5
        + (design.weight 4 + design.weight 5) * pairGapExcessOf design 4 5 := by
  simp [freePairRowAggregate, pairRowAggregateOn, freeThreeLabel,
    Fin.sum_univ_three, pairGapExcessOf_comm]
  ring

/-- At rank three the general-rank pair gap minor is the existing pair minor. -/
theorem pairGapExcessOf_eq_pairMinor {size : ℕ} (design : WeightedDesign size 3)
    (first second : Fin size) :
    pairGapExcessOf design first second = pairMinor design first second := rfl



open Finset

/-! ## Exact balance for the free-pair aggregate

The pair-row law controls the whole six-label row.  This file splits the three
rows centred at the free labels into their free-free and free-base parts.  The
result isolates exactly what the one-slot refusals still have to control.
-/

/-- The base-weighted cross contribution to the three free pair-minor rows. -/
noncomputable def freeBaseCrossPairRowAggregate
    (design : WeightedDesign 6 3) : ℝ :=
  ∑ freeIndex : Fin 3, ∑ baseIndex : Fin 3,
    design.weight (baseThreeLabel baseIndex) *
      pairMinor design (baseThreeLabel baseIndex) (freeThreeLabel freeIndex)

/-- The cross aggregate expanded in the fixed six-label coordinates. -/
theorem freeBaseCrossPairRowAggregate_eq_ninePairs
    (design : WeightedDesign 6 3) :
    freeBaseCrossPairRowAggregate design =
        design.weight 0 * pairMinor design 0 3
      + design.weight 1 * pairMinor design 1 3
      + design.weight 2 * pairMinor design 2 3
      + design.weight 0 * pairMinor design 0 4
      + design.weight 1 * pairMinor design 1 4
      + design.weight 2 * pairMinor design 2 4
      + design.weight 0 * pairMinor design 0 5
      + design.weight 1 * pairMinor design 1 5
      + design.weight 2 * pairMinor design 2 5 := by
  simp [freeBaseCrossPairRowAggregate, freeThreeLabel, baseThreeLabel,
    Fin.sum_univ_three]
  ring

/-- Summing the three free-centred off-diagonal row laws gives an exact split
into the free-free aggregate and the base-weighted cross aggregate. -/
theorem freePairRowAggregate_add_cross_eq_freeRowScalars
    (design : WeightedDesign 6 3) :
    freePairRowAggregate design + freeBaseCrossPairRowAggregate design =
        (leverageOf (design.atom 3) - 2
          + design.weight 3 * (2 * leverageOf (design.atom 3) - 1))
      + (leverageOf (design.atom 4) - 2
          + design.weight 4 * (2 * leverageOf (design.atom 4) - 1))
      + (leverageOf (design.atom 5) - 2
          + design.weight 5 * (2 * leverageOf (design.atom 5) - 1)) := by
  have hthree := sum_erase_weight_mul_pairMinor_row design (3 : Fin 6)
  have hfour := sum_erase_weight_mul_pairMinor_row design (4 : Fin 6)
  have hfive := sum_erase_weight_mul_pairMinor_row design (5 : Fin 6)
  rw [freePairRowAggregate_eq_threePairs,
    freeBaseCrossPairRowAggregate_eq_ninePairs]
  simp only [pairGapExcessOf_eq_pairMinor]
  simp [Fin.sum_univ_six, pairMinor_comm] at hthree hfour hfive
  linarith

/-- After the global leverage trace is spent, the same balance has no weighted
free-leverage term. -/
theorem freePairRowAggregate_add_cross_eq_leverageBalance
    (design : WeightedDesign 6 3) :
    freePairRowAggregate design + freeBaseCrossPairRowAggregate design =
        leverageOf (design.atom 3) + leverageOf (design.atom 4)
          + leverageOf (design.atom 5)
      - 2 * (design.weight 0 * leverageOf (design.atom 0)
          + design.weight 1 * leverageOf (design.atom 1)
          + design.weight 2 * leverageOf (design.atom 2))
      - (design.weight 3 + design.weight 4 + design.weight 5) := by
  have hrows := freePairRowAggregate_add_cross_eq_freeRowScalars design
  have htrace := sum_weight_mul_leverage design
  rw [Fin.sum_univ_six] at htrace
  linear_combination hrows + 2 * htrace



/-! ## The aggregate-to-refusal frontier

Once the free-pair aggregate is positive, full card-three failure supplies a
live free pair.  The exact failure IFF then says every other label refuses to
complete that pair.  This is the common downstream residual, independent of the
unit-axis coordinates used to prove the aggregate sign.
-/

/-- Full card-three failure as the existential negation expected by the landed
refusal equivalence. -/
theorem not_exists_cardThree_posDef_of_forall_not_posDef
    (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ¬ ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef := by
  rintro ⟨selected, hcard, hposDef⟩
  exact hnoStrict selected hcard hposDef

/-- The exact residual obtained after the conditional free-pair aggregate is
signed: a live pair among labels `3,4,5`, with every distinct completion tie
nonpositive. -/
theorem exists_live_freePair_all_discriminantTie_nonpos_of_rowAggregate_pos
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef)
    (haggregate : 0 < freePairRowAggregate design) :
    ∃ first second : Fin 3, first ≠ second
      ∧ IsLivePair design (freeThreeLabel first) (freeThreeLabel second)
      ∧ ∀ third : Fin 6,
          freeThreeLabel first ≠ third → freeThreeLabel second ≠ third →
            discriminantTie design (freeThreeLabel first)
              (freeThreeLabel second) third ≤ 0 := by
  obtain ⟨first, second, hdistinct, hlive⟩ :=
    exists_live_freePair_of_no_cardThree_posDef_of_rowAggregate_pos design
      hdominates hnoStrict haggregate
  have hrefusal : LivePairTieRefusal design :=
    (not_exists_posDef_cardThree_iff_livePairTieRefusal design).mp
      (not_exists_cardThree_posDef_of_forall_not_posDef design hnoStrict)
  refine ⟨first, second, hdistinct, hlive, ?_⟩
  intro third hfirstThird hsecondThird
  have hfreeDistinct : freeThreeLabel first ≠ freeThreeLabel second := by
    exact fun hequal => hdistinct (freeThreeLabel_injective hequal)
  rcases hrefusal (freeThreeLabel first) (freeThreeLabel second) third
      hfreeDistinct hfirstThird hsecondThird with hnotLive | hnonpos
  · exact absurd hlive hnotLive
  · exact hnonpos

end Gtz
