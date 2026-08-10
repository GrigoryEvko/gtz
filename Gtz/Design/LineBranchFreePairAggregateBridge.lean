import Gtz.Design.GeneralRankAveraging
import Gtz.Design.DepthCapAxisParseval
import Gtz.Design.FreePairPlane
import Gtz.Design.StratumEmptinessLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset

variable {size indexSize : ℕ}

/-! ## A symmetric route from free-row positivity to a live pair

The hard line-branch inequalities can be kept separate from the finite sign
argument.  If every pair in an indexed family has at least one heavy endpoint,
then a positive weighted off-diagonal pair-minor row forces a live pair.
-/

/-- A positive pair minor with at least one heavy endpoint is a live pair. -/
theorem isLivePair_of_pairGapExcessOf_pos_of_excess_or
    (design : WeightedDesign size 3) (first second : Fin size)
    (hpair : 0 < pairGapExcessOf design first second)
    (hendpoint : 0 < gapExcessOf design first ∨ 0 < gapExcessOf design second) :
    IsLivePair design first second := by
  have hsquare : 0 ≤ gapPairingOf design first second ^ 2 := sq_nonneg _
  rcases hendpoint with hfirst | hsecond
  · have hsecond : 0 < gapExcessOf design second := by
      rw [pairGapExcessOf] at hpair
      nlinarith
    exact ⟨hfirst, hsecond, hpair⟩
  · have hfirst : 0 < gapExcessOf design first := by
      rw [pairGapExcessOf] at hpair
      nlinarith
    exact ⟨hfirst, hsecond, hpair⟩

/-- The sum of the weighted off-diagonal pair-minor rows on an indexed family.
For three labels it is
`(u₀+u₁) P₀₁ + (u₀+u₂) P₀₂ + (u₁+u₂) P₁₂`. -/
noncomputable def pairRowAggregateOn (design : WeightedDesign size 3)
    (label : Fin indexSize → Fin size) : ℝ :=
  ∑ first, ∑ second ∈ (Finset.univ : Finset (Fin indexSize)).erase first,
    design.weight (label second) *
      pairGapExcessOf design (label first) (label second)

/-- If at most one indexed atom is nonheavy, positivity of the symmetric row
aggregate produces a live pair inside the family. -/
theorem exists_livePair_of_pairRowAggregateOn_pos
    (design : WeightedDesign size 3) (label : Fin indexSize → Fin size)
    (hatMostOneNonheavy : ∀ first second, first ≠ second →
      0 < gapExcessOf design (label first) ∨
        0 < gapExcessOf design (label second))
    (haggregate : 0 < pairRowAggregateOn design label) :
    ∃ first second, first ≠ second ∧
      IsLivePair design (label first) (label second) := by
  by_contra hnone
  have hterm : ∀ first,
      ∀ second ∈ (Finset.univ : Finset (Fin indexSize)).erase first,
        design.weight (label second) *
            pairGapExcessOf design (label first) (label second) ≤ 0 := by
    intro first second hsecond
    have hne : first ≠ second := (Finset.ne_of_mem_erase hsecond).symm
    have hminor : pairGapExcessOf design (label first) (label second) ≤ 0 := by
      by_contra hnot
      have hpos : 0 < pairGapExcessOf design (label first) (label second) :=
        lt_of_not_ge hnot
      have hlive := isLivePair_of_pairGapExcessOf_pos_of_excess_or design
        (label first) (label second) hpos (hatMostOneNonheavy first second hne)
      exact hnone ⟨first, second, hne, hlive⟩
    exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos _).le hminor
  have hnonpos : pairRowAggregateOn design label ≤ 0 := by
    unfold pairRowAggregateOn
    exact Finset.sum_nonpos fun first _ => Finset.sum_nonpos (hterm first)
  exact (not_lt_of_ge hnonpos) haggregate

/-- The symmetric free-pair row aggregate in the transported `(6,3)` split. -/
noncomputable def freePairRowAggregate (design : WeightedDesign 6 3) : ℝ :=
  pairRowAggregateOn design freeThreeLabel

/-- The exact final sign step for the conditional tight-line hinge.  The two
remaining inputs are scalar inequalities in the transported normal form. -/
theorem exists_live_freePair_of_atMostOneNonheavy_of_rowAggregate_pos
    (design : WeightedDesign 6 3)
    (hatMostOneNonheavy : ∀ first second : Fin 3, first ≠ second →
      0 < gapExcessOf design (freeThreeLabel first) ∨
        0 < gapExcessOf design (freeThreeLabel second))
    (haggregate : 0 < freePairRowAggregate design) :
    ∃ first second : Fin 3, first ≠ second ∧
      IsLivePair design (freeThreeLabel first) (freeThreeLabel second) := by
  exact exists_livePair_of_pairRowAggregateOn_pos design freeThreeLabel
    hatMostOneNonheavy haggregate

/-! ## The version needed on the actual failure locus

Failure of every three-element candidate, together with the weak base triple,
makes the design an `IsTie`.  The already-landed `(5,3)` result then puts every
leverage at least one.  Thus a positive pair minor automatically has both
endpoint excesses strictly positive; no separate leverage selector is needed.
-/

/-- A positive pair minor is live when both endpoint leverages are at least
one.  Strict endpoint heaviness follows from the positive determinant itself. -/
theorem isLivePair_of_pairGapExcessOf_pos_of_leverage_one_le
    (design : WeightedDesign 6 3) (first second : Fin 6)
    (hpair : 0 < pairGapExcessOf design first second)
    (hfirst : 1 ≤ leverageOf (design.atom first))
    (hsecond : 1 ≤ leverageOf (design.atom second)) :
    IsLivePair design first second := by
  have hsquare : 0 ≤ gapPairingOf design first second ^ 2 := sq_nonneg _
  have hfirstExcess : 0 ≤ gapExcessOf design first := by
    simp only [gapExcessOf]
    linarith
  have hsecondExcess : 0 ≤ gapExcessOf design second := by
    simp only [gapExcessOf]
    linarith
  have hfirstStrict : 0 < gapExcessOf design first := by
    rw [pairGapExcessOf] at hpair
    nlinarith
  have hsecondStrict : 0 < gapExcessOf design second := by
    rw [pairGapExcessOf] at hpair
    nlinarith
  exact ⟨hfirstStrict, hsecondStrict, hpair⟩

/-- On a `(6,3)` tie, positivity of an indexed pair-row aggregate produces a
live pair in that indexed family. -/
theorem exists_livePair_of_pairRowAggregateOn_pos_of_isTie
    (design : WeightedDesign 6 3) (label : Fin indexSize → Fin 6)
    (htie : IsTie design) (haggregate : 0 < pairRowAggregateOn design label) :
    ∃ first second, first ≠ second ∧
      IsLivePair design (label first) (label second) := by
  by_contra hnone
  have hterm : ∀ first,
      ∀ second ∈ (Finset.univ : Finset (Fin indexSize)).erase first,
        design.weight (label second) *
            pairGapExcessOf design (label first) (label second) ≤ 0 := by
    intro first second hsecond
    have hne : first ≠ second := (Finset.ne_of_mem_erase hsecond).symm
    have hminor : pairGapExcessOf design (label first) (label second) ≤ 0 := by
      by_contra hnot
      have hpos : 0 < pairGapExcessOf design (label first) (label second) :=
        lt_of_not_ge hnot
      have hlive := isLivePair_of_pairGapExcessOf_pos_of_leverage_one_le design
        (label first) (label second) hpos
        (leverage_one_le_of_isTie_sixThree design htie (label first))
        (leverage_one_le_of_isTie_sixThree design htie (label second))
      exact hnone ⟨first, second, hne, hlive⟩
    exact mul_nonpos_of_nonneg_of_nonpos (design.weight_pos _).le hminor
  have hnonpos : pairRowAggregateOn design label ≤ 0 := by
    unfold pairRowAggregateOn
    exact Finset.sum_nonpos fun first _ => Finset.sum_nonpos (hterm first)
  exact (not_lt_of_ge hnonpos) haggregate

/-- The weak base triple and failure of every card-three strict candidate are
exactly the two fields needed to manufacture an `IsTie`. -/
theorem isTie_of_dominates_base_of_no_cardThree_posDef
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    IsTie design :=
  ⟨⟨{0, 1, 2}, by decide, hdominates⟩, hnoStrict⟩

/-- The exact aggregate-to-live-free-pair bridge used in a contradiction proof
of the tight-line branch. -/
theorem exists_live_freePair_of_no_cardThree_posDef_of_rowAggregate_pos
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef)
    (haggregate : 0 < freePairRowAggregate design) :
    ∃ first second : Fin 3, first ≠ second ∧
      IsLivePair design (freeThreeLabel first) (freeThreeLabel second) := by
  exact exists_livePair_of_pairRowAggregateOn_pos_of_isTie design freeThreeLabel
    (isTie_of_dominates_base_of_no_cardThree_posDef design hdominates hnoStrict)
    haggregate

end Gtz
