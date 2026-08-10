import Gtz.Design.TightLineBranchLivePairBridge
import Gtz.Design.LineBranchFreePairAggregateBridge
import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.TightLineRefutationFixtures
import Gtz.Design.FreePairPlane
import Gtz.Reduction.TrichotomyLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset

/-! # The conditional tight-line hinge, in its surviving form

The two-ingredient hinge that this file replaces asked for

* **(a)** at most one free atom is light, and
* **(b)** the weighted free-pair row aggregate `sum_{c<d} (u_c+u_d) P_cd` is
  positive,

both conditional on no one-slot swap of the base triple being strict.
Ingredient **(b)** is FALSE, and so is its natural repair "(b) under the
additional hypothesis that every leverage is at least one": Wave C exhibits
rational-atom designs meeting every antecedent of
`BaseTripleTightLineFreeOffConicWeakToStrict`, with no strict one-slot swap and
every leverage strictly above one, at which the aggregate is negative.  Nothing
below uses an aggregate.

What survives is better shaped than what died.  Three eliminations happen here.

1. **The case split disappears.**  In a contradiction proof of the obligation,
   the hypothesis is failure of EVERY card-three candidate, and a one-slot swap
   is a card-three candidate.  "No one-slot swap is strict" is therefore not a
   case to enter but a consequence to read off
   (`no_strict_oneSlot_of_no_cardThree_posDef`).

2. **Ingredient (a) disappears.**  A weak base triple plus failure of every
   card-three candidate is an `IsTie`, and on a `(6,3)` tie every leverage is at
   least one.  A positive pair minor then forces both endpoints strictly heavy
   by itself, so liveness of a free pair IS the single scalar sign
   `0 < pairGapExcessOf` (`isLivePair_iff_pos_pairGapExcessOf_of_isTie`).

3. **The matrices and the direction disappear.**  Strict domination of a
   card-three set containing two free labels is exactly a positive pair minor
   together with a positive tie leg.

The result is `exists_posDef_cardThree_iff_oneSlot_or_freePairPositiveTie`: at a
tight-line antecedent, a strict card-three candidate exists if and only if some
one-slot swap is strict or some free pair is live with a positive tie leg.  Its
negation, `FreePairTieRefusal`, is an EXACT characterisation of the failure
locus and not a one-way necessary condition -- unlike the base-pair analogues
`exists_liveBasePair_all_discriminantTie_nonpos_of_not_nineteenCandidate` and
`exists_liveBasePair_freeTie_nonpos_of_not_nineteenCandidate`, whose conclusions
also hold at designs whose branch is true and which therefore cannot be
contradicted.

**HONESTY.** `baseTripleTightLineFreeOffConicWeakToStrict_iff_freePairResidual`
is an IFF, so this is a change of coordinates and not a gain in strength; the
residual's hypothesis is the conjecturally empty failure locus, so proving it
does the theorem's whole work.  What the coordinates buy is that the target is
now a purely scalar existential over three free pairs and their twelve
completions, with no matrix, no eigenvector, no orthonormal frame, no direction
quantifier, no heaviness selector and no average.

**NOT A LINE-ONLY FILE, DESPITE THE NAME.**
`BaseTripleTightLineFreeOffConicWeakToStrict` puts no rank condition on the base
gap, and the exhaustion above asks only for a nonzero tight direction, so Parts
0-5 cover BOTH branches of the tight-space dichotomy.  Part 6 makes the plane
side explicit: there the one-slot disjunct vanishes outright and the landed ten
matrix candidates ARE the three scalar free pairs, so ONE residual now serves
both branches.  Read the whole file before concluding it is about lines.
-/

variable {size : ℕ}

/-! ## Part 0 -- two purely combinatorial card counts -/

/-- A one-slot exchange of the base triple has card three. -/
theorem card_oneSlotSubset_of_mem_of_notMem {swapOut swapIn : Fin 6}
    (hswapOut : swapOut ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hswapIn : swapIn ∉ ({0, 1, 2} : Finset (Fin 6))) :
    (insert swapIn ((({0, 1, 2} : Finset (Fin 6))).erase swapOut)).card = 3 := by
  revert hswapOut hswapIn
  revert swapOut swapIn
  decide

/-- Three pairwise distinct labels span a card-three set. -/
theorem card_tripleInsert_of_distinct {first second third : Fin 6}
    (hne : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ({first, second, third} : Finset (Fin 6)).card = 3 := by
  revert hne hfirstThird hsecondThird
  revert first second third
  decide

/-! ## Part 1 -- liveness of a pair IS one scalar sign on the failure locus -/

/-- **On a `(6,3)` tie, `IsLivePair` collapses to its third conjunct.**  Both
endpoint heaviness conditions are automatic: a tie puts every leverage at least
one, and a positive pair minor upgrades both endpoints to strictly heavy. -/
theorem isLivePair_iff_pos_pairGapExcessOf_of_isTie
    (design : WeightedDesign 6 3) (htie : IsTie design) (first second : Fin 6) :
    IsLivePair design first second ↔ 0 < pairGapExcessOf design first second := by
  refine ⟨fun hlive => hlive.2.2, fun hminor => ?_⟩
  exact isLivePair_of_pairGapExcessOf_pos_of_leverage_one_le design first second hminor
    (leverage_one_le_of_isTie_sixThree design htie first)
    (leverage_one_le_of_isTie_sixThree design htie second)

/-- **The one-slot case is not a case.**  Failure of every card-three candidate
already excludes every one-slot swap, so a contradiction proof of the tight-line
branch never has to split on it. -/
theorem no_strict_oneSlot_of_no_cardThree_posDef
    (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    ¬ TightLineOneSlotFamily design := by
  rintro ⟨swapOut, hswapOut, swapIn, hswapIn, hpos⟩
  exact hnoStrict _ (card_oneSlotSubset_of_mem_of_notMem hswapOut hswapIn) hpos

/-! ## Part 2 -- the free-pair candidate and its refusal -/

/-- **Some free pair is live and one of its completions has a positive tie
leg.**  The scalar form of "some card-three set with two free labels strictly
dominates". -/
def FreePairPositiveTie (design : WeightedDesign 6 3) : Prop :=
  ∃ first second third : Fin 6,
    first ∈ ({3, 4, 5} : Finset (Fin 6)) ∧ second ∈ ({3, 4, 5} : Finset (Fin 6)) ∧
      first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
        IsLivePair design first second ∧
          0 < discriminantTie design first second third

/-- **The free-restricted tie refusal.**  The exact negation of
`FreePairPositiveTie`, and the free-label analogue of `LivePairTieRefusal`; it
quantifies over three pairs rather than fifteen. -/
def FreePairTieRefusal (design : WeightedDesign 6 3) : Prop :=
  ∀ first second third : Fin 6,
    first ∈ ({3, 4, 5} : Finset (Fin 6)) → second ∈ ({3, 4, 5} : Finset (Fin 6)) →
      first ≠ second → first ≠ third → second ≠ third →
        ¬ IsLivePair design first second ∨
          discriminantTie design first second third ≤ 0

theorem freePairTieRefusal_iff_not_freePairPositiveTie
    (design : WeightedDesign 6 3) :
    FreePairTieRefusal design ↔ ¬ FreePairPositiveTie design := by
  constructor
  · rintro hrefusal ⟨first, second, third, hfirst, hsecond, hne, hfirstThird,
      hsecondThird, hlive, htie⟩
    rcases hrefusal first second third hfirst hsecond hne hfirstThird hsecondThird with
      hnotLive | hnonpos
    · exact hnotLive hlive
    · exact absurd htie (not_lt_of_ge hnonpos)
  · intro hnone first second third hfirst hsecond hne hfirstThird hsecondThird
    by_cases hlive : IsLivePair design first second
    · refine Or.inr (le_of_not_gt fun htie => hnone ?_)
      exact ⟨first, second, third, hfirst, hsecond, hne, hfirstThird, hsecondThird,
        hlive, htie⟩
    · exact Or.inl hlive

/-- **A strict card-three set with two free labels yields the free candidate.**
Liveness of the free pair is the landed distance-two lemma; the positive tie leg
is the landed cross-axis criterion at that live pair. -/
theorem freePairPositiveTie_of_posDef_twoFreeLabels
    (design : WeightedDesign 6 3) (third first second : Fin 6)
    (hfirst : first ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hsecond : second ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hne : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hpos : (subsetSum design {third, first, second} - 1).PosDef) :
    FreePairPositiveTie design := by
  have hlive : IsLivePair design first second :=
    isLivePair_freePair_of_posDef_distanceTwoGap design third first second hne
      hfirstThird hsecondThird hpos
  rw [tripleInsert_rotate third first second] at hpos
  exact ⟨first, second, third, hfirst, hsecond, hne, hfirstThird, hsecondThird, hlive,
    (posDef_gap_iff_pos_discriminantTie_of_isLivePair design hne hfirstThird
      hsecondThird hlive).mp hpos⟩

/-- The free candidate produces a strict card-three set. -/
theorem exists_posDef_cardThree_of_freePairPositiveTie
    (design : WeightedDesign 6 3) (hcandidate : FreePairPositiveTie design) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef := by
  obtain ⟨first, second, third, _, _, hne, hfirstThird, hsecondThird, hlive, htie⟩ :=
    hcandidate
  refine ⟨{first, second, third}, card_tripleInsert_of_distinct hne hfirstThird
    hsecondThird, ?_⟩
  · exact (posDef_gap_iff_pos_discriminantTie_of_isLivePair design hne hfirstThird
      hsecondThird hlive).mpr htie

/-- The one-slot family produces a strict card-three set. -/
theorem exists_posDef_cardThree_of_tightLineOneSlotFamily
    (design : WeightedDesign 6 3) (hfamily : TightLineOneSlotFamily design) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef := by
  obtain ⟨swapOut, hswapOut, swapIn, hswapIn, hpos⟩ := hfamily
  exact ⟨_, card_oneSlotSubset_of_mem_of_notMem hswapOut hswapIn, hpos⟩

/-! ## Part 3 -- the exhaustion -/

/-- **THE FREE-PAIR EXHAUSTION.**  At a tight-line antecedent a strict
card-three candidate exists exactly when a one-slot swap is strict or some free
pair is live with a positive tie leg.

The base triple is excluded by its own tight direction; every other card-three
set either keeps two base labels -- a one-slot swap -- or brings in two free
labels, and the second alternative is exactly the free candidate.  Only
`tightDir` enters, and only to kill the base triple; neither line-freeness nor
off-conicity is used. -/
theorem exists_posDef_cardThree_iff_oneSlot_or_freePairPositiveTie
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ}
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (subsetSum design selected - 1).PosDef)
      ↔ TightLineOneSlotFamily design ∨ FreePairPositiveTie design := by
  classical
  constructor
  · rintro ⟨selected, hcard, hpos⟩
    have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    have hbaseNot :
        ¬ (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef :=
      not_posDef_baseTripleGap_of_tightDirection design htightNe htight
    rcases cardThreeFinsetsOfSix_enumeration selected hpow with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hpos hbaseNot
    · exact Or.inl ⟨2, by decide, 3, by decide, by
        simpa only [show insert (3 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 2) = {0, 1, 3} by decide] using hpos⟩
    · exact Or.inl ⟨2, by decide, 4, by decide, by
        simpa only [show insert (4 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 2) = {0, 1, 4} by decide] using hpos⟩
    · exact Or.inl ⟨2, by decide, 5, by decide, by
        simpa only [show insert (5 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 2) = {0, 1, 5} by decide] using hpos⟩
    · exact Or.inl ⟨1, by decide, 3, by decide, by
        simpa only [show insert (3 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 1) = {0, 2, 3} by decide] using hpos⟩
    · exact Or.inl ⟨1, by decide, 4, by decide, by
        simpa only [show insert (4 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 1) = {0, 2, 4} by decide] using hpos⟩
    · exact Or.inl ⟨1, by decide, 5, by decide, by
        simpa only [show insert (5 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 1) = {0, 2, 5} by decide] using hpos⟩
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 0 3 4
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 0 3 5
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 0 4 5
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inl ⟨0, by decide, 3, by decide, by
        simpa only [show insert (3 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 0) = {1, 2, 3} by decide] using hpos⟩
    · exact Or.inl ⟨0, by decide, 4, by decide, by
        simpa only [show insert (4 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 0) = {1, 2, 4} by decide] using hpos⟩
    · exact Or.inl ⟨0, by decide, 5, by decide, by
        simpa only [show insert (5 : Fin 6)
          ((({0, 1, 2} : Finset (Fin 6))).erase 0) = {1, 2, 5} by decide] using hpos⟩
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 1 3 4
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 1 3 5
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 1 4 5
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 2 3 4
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 2 3 5
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 2 4 5
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
    · exact Or.inr (freePairPositiveTie_of_posDef_twoFreeLabels design 3 4 5
        (by decide) (by decide) (by decide) (by decide) (by decide) hpos)
  · rintro (hfamily | hcandidate)
    · exact exists_posDef_cardThree_of_tightLineOneSlotFamily design hfamily
    · exact exists_posDef_cardThree_of_freePairPositiveTie design hcandidate

/-- **The free-pair refusal characterises tight-line failure.**  Not a one-way
necessary condition: at a tight-line antecedent, no strict one-slot swap plus
free-pair refusal is EQUIVALENT to failure of every card-three candidate. -/
theorem not_exists_posDef_cardThree_iff_freePairTieRefusal
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ}
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef)
      ↔ ¬ TightLineOneSlotFamily design ∧ FreePairTieRefusal design := by
  rw [freePairTieRefusal_iff_not_freePairPositiveTie]
  constructor
  · intro hfail
    refine ⟨no_strict_oneSlot_of_no_cardThree_posDef design hfail, fun hcandidate => ?_⟩
    obtain ⟨selected, hcard, hpos⟩ :=
      exists_posDef_cardThree_of_freePairPositiveTie design hcandidate
    exact hfail selected hcard hpos
  · rintro ⟨hnoOneSlot, hnoFree⟩ selected hcard hpos
    rcases (exists_posDef_cardThree_iff_oneSlot_or_freePairPositiveTie design htightNe
      htight).mp ⟨selected, hcard, hpos⟩ with hfamily | hcandidate
    · exact hnoOneSlot hfamily
    · exact hnoFree hcandidate

/-! ## Part 4 -- the assembly

The residual below is the obligation with everything discharged that can be:
heaviness (absorbed by the tie), the one-slot case (implied by failure),
positive definiteness (three scalar signs), the orthonormal frame and the
direction quantifier (absorbed by `discriminantTie`).
-/

/-- **The residual, in the tree's own scalar alphabet.**  Two polynomial signs
at one of three free pairs, with no liveness hypothesis: heaviness is supplied
by the tie in `freePairPositiveTie_of_freePairMinorPositiveTie_of_isTie`. -/
def FreePairMinorPositiveTie (design : WeightedDesign 6 3) : Prop :=
  ∃ first second third : Fin 6,
    first ∈ ({3, 4, 5} : Finset (Fin 6)) ∧ second ∈ ({3, 4, 5} : Finset (Fin 6)) ∧
      first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
        0 < pairGapExcessOf design first second ∧
          0 < discriminantTie design first second third

/-- **Ingredient (a) is eliminated.**  On a tie the minor alone gives liveness. -/
theorem freePairPositiveTie_of_freePairMinorPositiveTie_of_isTie
    (design : WeightedDesign 6 3) (htie : IsTie design)
    (hminor : FreePairMinorPositiveTie design) : FreePairPositiveTie design := by
  obtain ⟨first, second, third, hfirst, hsecond, hne, hfirstThird, hsecondThird,
    hpair, htieLeg⟩ := hminor
  exact ⟨first, second, third, hfirst, hsecond, hne, hfirstThird, hsecondThird,
    (isLivePair_iff_pos_pairGapExcessOf_of_isTie design htie first second).mpr hpair,
    htieLeg⟩

/-- **The full assembly.**  The `U(3,6)` tight-line obligation follows from one
scalar existential on the failure locus. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_of_freePairMinorPositiveTie
    (hresidual : ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      Dominates design ({0, 1, 2} : Finset (Fin 6)) →
      tightDir ≠ 0 →
      IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef) →
      FreePairMinorPositiveTie design) :
    BaseTripleTightLineFreeOffConicWeakToStrict := by
  intro design tightDir hlineFree hoffConic hdominates htightNe htight
  by_contra hnone
  have hfail : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef := by
    intro selected hcard hpos
    exact hnone ⟨selected, hcard, hpos⟩
  have htie : IsTie design :=
    isTie_of_dominates_base_of_no_cardThree_posDef design hdominates hfail
  have hcandidate : FreePairPositiveTie design :=
    freePairPositiveTie_of_freePairMinorPositiveTie_of_isTie design htie
      (hresidual design tightDir hlineFree hoffConic hdominates htightNe htight hfail)
  exact hnone (exists_posDef_cardThree_of_freePairPositiveTie design hcandidate)

/-- **HONESTY: the reduction is an equivalence, so it is a change of
coordinates and not a gain in strength.**  The converse holds because the
residual's hypothesis -- failure of every card-three candidate -- is exactly
what the obligation forbids, so once the obligation is proved the residual is
vacuously true. -/
theorem baseTripleTightLineFreeOffConicWeakToStrict_iff_freePairResidual :
    BaseTripleTightLineFreeOffConicWeakToStrict ↔
      ∀ (design : WeightedDesign 6 3) (tightDir : Fin 3 → ℝ),
        HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
        HasNoCommonQuadric design.atom →
        Dominates design ({0, 1, 2} : Finset (Fin 6)) →
        tightDir ≠ 0 →
        IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir →
        (∀ selected : Finset (Fin 6), selected.card = 3 →
          ¬ (subsetSum design selected - 1).PosDef) →
        FreePairMinorPositiveTie design := by
  refine ⟨fun hbranch design tightDir hlineFree hoffConic hdominates htightNe htight
      hfail => ?_, baseTripleTightLineFreeOffConicWeakToStrict_of_freePairMinorPositiveTie⟩
  obtain ⟨selected, hcard, hpos⟩ :=
    hbranch design tightDir hlineFree hoffConic hdominates htightNe htight
  exact absurd hpos (hfail selected hcard)

/-! ## Part 5 -- satisfiability, at a landed full-antecedent design

Both sides of the exhaustion are inhabited, so neither is vacuous.  The witness
is `freePairKillerDesign`, which meets every antecedent of the obligation and
whose branch is TRUE.
-/

/-- Every free label is `freeThreeLabel` of some index. -/
theorem exists_freeIndex_of_mem_freeTriple (label : Fin 6)
    (hlabel : label ∈ ({3, 4, 5} : Finset (Fin 6))) :
    ∃ index : Fin 3, freeThreeLabel index = label := by
  fin_cases label <;> simp_all [freeThreeLabel] <;> decide

/-- **`FreePairTieRefusal` IS SATISFIABLE, at a design meeting every antecedent
of the obligation.**  No free pair of `freePairKillerDesign` is live at all, so
the refusal holds there for the strongest possible reason. -/
theorem freePairTieRefusal_freePairKillerDesign :
    FreePairTieRefusal freePairKillerDesign := by
  intro first second third hfirst hsecond hne _ _
  obtain ⟨firstIndex, rfl⟩ := exists_freeIndex_of_mem_freeTriple first hfirst
  obtain ⟨secondIndex, rfl⟩ := exists_freeIndex_of_mem_freeTriple second hsecond
  exact Or.inl (not_isLivePair_freePairKillerDesign_freePair firstIndex secondIndex
    fun hindex => hne (by rw [hindex]))

/-- **The no-one-slot hypothesis carries the entire hinge.**  At
`freePairKillerDesign` the branch is TRUE and `FreePairTieRefusal` HOLDS, so the
exhaustion theorem forces a strict one-slot swap -- which that design has, five
times over.  Hence no UNCONDITIONAL free-pair statement can prove the branch,
and the conditional one is doing all the work. -/
theorem tightLineOneSlotFamily_freePairKillerDesign :
    TightLineOneSlotFamily freePairKillerDesign := by
  rcases (exists_posDef_cardThree_iff_oneSlot_or_freePairPositiveTie
    freePairKillerDesign freePairKillerDesign_tightDirection_ne_zero
    freePairKillerDesign_tightDirection_rayleigh).mp
      ⟨{0, 1, 3}, by decide, freePairKillerDesign_hasStrictTriple⟩ with
    hfamily | hcandidate
  · exact hfamily
  · exact absurd hcandidate
      ((freePairTieRefusal_iff_not_freePairPositiveTie freePairKillerDesign).mp
        freePairTieRefusal_freePairKillerDesign)

/-- **`FreePairPositiveTie` IS SATISFIABLE**, at the other landed fixture: the
strict triple `{0,4,5}` of `baseTieKillerDesign` has two free labels. -/
theorem freePairPositiveTie_baseTieKillerDesign :
    FreePairPositiveTie baseTieKillerDesign :=
  freePairPositiveTie_of_posDef_twoFreeLabels baseTieKillerDesign 0 4 5
    (by decide) (by decide) (by decide) (by decide) (by decide)
    baseTieKillerDesign_hasStrictTriple

/-- Liveness contains the minor, so the residual is the weaker of the two;
together with `freePairPositiveTie_of_freePairMinorPositiveTie_of_isTie` the two
coincide on every tie. -/
theorem freePairMinorPositiveTie_of_freePairPositiveTie
    (design : WeightedDesign 6 3) (hcandidate : FreePairPositiveTie design) :
    FreePairMinorPositiveTie design := by
  obtain ⟨first, second, third, hfirst, hsecond, hne, hfirstThird, hsecondThird,
    hlive, htieLeg⟩ := hcandidate
  exact ⟨first, second, third, hfirst, hsecond, hne, hfirstThird, hsecondThird,
    hlive.2.2, htieLeg⟩

/-- **`FreePairMinorPositiveTie` IS SATISFIABLE.** -/
theorem freePairMinorPositiveTie_baseTieKillerDesign :
    FreePairMinorPositiveTie baseTieKillerDesign :=
  freePairMinorPositiveTie_of_freePairPositiveTie baseTieKillerDesign
    freePairPositiveTie_baseTieKillerDesign

/-! ## Part 6 -- the PLANE branch collapses to the SAME scalar predicate

Everything above is branch-agnostic: `exists_posDef_cardThree_iff_oneSlot_or_freePairPositiveTie`
asks only for a nonzero tight direction at the base triple, which both branches
supply.  The plane branch supplies more -- a whole tight PLANE -- and the tree
already knows that this kills every candidate retaining two base labels
(`oneSlotSwap_not_posDef_of_planeBranch`).  So on the plane branch the one-slot
disjunct vanishes and the ten landed matrix candidates become the same three
free pairs and their tie legs.
-/

/-- **Every plane-branch candidate is a free-pair candidate.**  All ten
disjuncts of `PlaneBranchTenCandidate` carry two free labels, so each of them
produces `FreePairPositiveTie` through the landed distance-two liveness lemma
and the landed cross-axis criterion.  NO hypothesis at all. -/
theorem freePairPositiveTie_of_planeBranchTenCandidate
    (design : WeightedDesign 6 3) (hten : PlaneBranchTenCandidate design) :
    FreePairPositiveTie design := by
  rcases hten with h | h | h | h | h | h | h | h | h | h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 0 3 4
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 0 3 5
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 0 4 5
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 1 3 4
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 1 3 5
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 1 4 5
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 2 3 4
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 2 3 5
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · exact freePairPositiveTie_of_posDef_twoFreeLabels design 2 4 5
      (by decide) (by decide) (by decide) (by decide) (by decide) h
  · refine freePairPositiveTie_of_posDef_twoFreeLabels design 5 3 4
      (by decide) (by decide) (by decide) (by decide) (by decide) ?_
    simpa only [show ({5, 3, 4} : Finset (Fin 6)) = {3, 4, 5} by decide] using h

/-- **The ten landed matrix candidates ARE the three scalar free pairs.** -/
theorem planeBranchTenCandidate_iff_freePairPositiveTie
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    PlaneBranchTenCandidate design ↔ FreePairPositiveTie design := by
  refine ⟨freePairPositiveTie_of_planeBranchTenCandidate design, fun hcandidate => ?_⟩
  exact (exists_posDef_cardThree_iff_planeBranchTenCandidate design hdominates hfree).mp
    (exists_posDef_cardThree_of_freePairPositiveTie design hcandidate)

/-- **On the plane branch the one-slot disjunct is empty.**  The landed corank
obstruction, packaged as the family predicate the exhaustion speaks. -/
theorem not_tightLineOneSlotFamily_of_hasFreeTightDirection
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    ¬ TightLineOneSlotFamily design := by
  rintro ⟨swapOut, hswapOut, swapIn, hswapIn, hpos⟩
  exact oneSlotSwap_not_posDef_of_planeBranch design hdominates hfree swapOut swapIn
    hswapOut hswapIn hpos

/-- **The plane-branch exhaustion, with no one-slot disjunct.** -/
theorem exists_posDef_cardThree_iff_freePairPositiveTie_of_hasFreeTightDirection
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (subsetSum design selected - 1).PosDef)
      ↔ FreePairPositiveTie design := by
  rw [exists_posDef_cardThree_iff_planeBranchTenCandidate design hdominates hfree]
  exact planeBranchTenCandidate_iff_freePairPositiveTie design hdominates hfree

/-- **The plane-branch failure characterisation is the refusal alone.** -/
theorem not_exists_posDef_cardThree_iff_freePairTieRefusal_of_hasFreeTightDirection
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef)
      ↔ FreePairTieRefusal design := by
  rw [freePairTieRefusal_iff_not_freePairPositiveTie]
  constructor
  · intro hfail hcandidate
    obtain ⟨selected, hcard, hpos⟩ :=
      exists_posDef_cardThree_of_freePairPositiveTie design hcandidate
    exact hfail selected hcard hpos
  · intro hnone selected hcard hpos
    exact hnone ((exists_posDef_cardThree_iff_freePairPositiveTie_of_hasFreeTightDirection
      design hdominates hfree).mp ⟨selected, hcard, hpos⟩)

/-! ## Part 7 -- the failure characterisation with `IsLivePair` eliminated

`IsLivePair` is a three-conjunct `Prop`.  On the failure locus its first two
conjuncts are free (Part 1), so the whole characterisation can be stated with
nothing but two polynomial signs per candidate: twelve scalar inequalities in
the design's own alphabet, with no matrix, no direction and no predicate.
-/

/-- **The scalar refusal.**  The exact negation of `FreePairMinorPositiveTie`:
for every free pair and every completion, either the pair minor or the tie leg
is nonpositive. -/
def FreePairMinorRefusal (design : WeightedDesign 6 3) : Prop :=
  ∀ first second third : Fin 6,
    first ∈ ({3, 4, 5} : Finset (Fin 6)) → second ∈ ({3, 4, 5} : Finset (Fin 6)) →
      first ≠ second → first ≠ third → second ≠ third →
        pairGapExcessOf design first second ≤ 0 ∨
          discriminantTie design first second third ≤ 0

theorem freePairMinorRefusal_iff_not_freePairMinorPositiveTie
    (design : WeightedDesign 6 3) :
    FreePairMinorRefusal design ↔ ¬ FreePairMinorPositiveTie design := by
  constructor
  · rintro hrefusal ⟨first, second, third, hfirst, hsecond, hne, hfirstThird,
      hsecondThird, hminor, htie⟩
    rcases hrefusal first second third hfirst hsecond hne hfirstThird hsecondThird with
      hnonpos | hnonpos
    · exact absurd hminor (not_lt_of_ge hnonpos)
    · exact absurd htie (not_lt_of_ge hnonpos)
  · intro hnone first second third hfirst hsecond hne hfirstThird hsecondThird
    by_cases hminor : 0 < pairGapExcessOf design first second
    · refine Or.inr (le_of_not_gt fun htie => hnone ?_)
      exact ⟨first, second, third, hfirst, hsecond, hne, hfirstThird, hsecondThird,
        hminor, htie⟩
    · exact Or.inl (le_of_not_gt hminor)

/-- **THE SCALAR FAILURE CHARACTERISATION.**  At a weakly dominating base triple
with a nonzero tight direction, failure of every card-three candidate is
EQUIVALENT to "no one-slot swap is strict, and every free pair either has a
nonpositive minor or a nonpositive tie leg at every completion".  No matrix, no
`IsLivePair`, no direction on the right-hand side. -/
theorem not_exists_posDef_cardThree_iff_freePairMinorRefusal
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (htightNe : tightDir ≠ 0)
    (htight : IsTightDirectionOf design ({0, 1, 2} : Finset (Fin 6)) tightDir) :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef)
      ↔ ¬ TightLineOneSlotFamily design ∧ FreePairMinorRefusal design := by
  rw [freePairMinorRefusal_iff_not_freePairMinorPositiveTie]
  constructor
  · intro hfail
    refine ⟨no_strict_oneSlot_of_no_cardThree_posDef design hfail, fun hminor => ?_⟩
    have htie : IsTie design :=
      isTie_of_dominates_base_of_no_cardThree_posDef design hdominates hfail
    obtain ⟨selected, hcard, hpos⟩ := exists_posDef_cardThree_of_freePairPositiveTie design
      (freePairPositiveTie_of_freePairMinorPositiveTie_of_isTie design htie hminor)
    exact hfail selected hcard hpos
  · rintro ⟨hnoOneSlot, hnoMinor⟩ selected hcard hpos
    rcases (exists_posDef_cardThree_iff_oneSlot_or_freePairPositiveTie design htightNe
      htight).mp ⟨selected, hcard, hpos⟩ with hfamily | hcandidate
    · exact hnoOneSlot hfamily
    · exact hnoMinor (freePairMinorPositiveTie_of_freePairPositiveTie design hcandidate)

/-- **On the plane branch, twelve scalar inequalities and nothing else.** -/
theorem not_exists_posDef_cardThree_iff_freePairMinorRefusal_of_hasFreeTightDirection
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfree : HasFreeTightDirection design ({0, 1, 2} : Finset (Fin 6))) :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef)
      ↔ FreePairMinorRefusal design := by
  rw [freePairMinorRefusal_iff_not_freePairMinorPositiveTie]
  constructor
  · intro hfail hminor
    have htie : IsTie design :=
      isTie_of_dominates_base_of_no_cardThree_posDef design hdominates hfail
    obtain ⟨selected, hcard, hpos⟩ := exists_posDef_cardThree_of_freePairPositiveTie design
      (freePairPositiveTie_of_freePairMinorPositiveTie_of_isTie design htie hminor)
    exact hfail selected hcard hpos
  · intro hnoMinor selected hcard hpos
    exact hnoMinor (freePairMinorPositiveTie_of_freePairPositiveTie design
      ((exists_posDef_cardThree_iff_freePairPositiveTie_of_hasFreeTightDirection design
        hdominates hfree).mp ⟨selected, hcard, hpos⟩))

/-! ## Part 8 -- ingredient (a) on the failure locus, in EXISTENTIAL form

The brief asked for ingredient (a) -- at most one light free atom -- under the
no-one-slot hypothesis.  On the failure locus a stronger statement is available
from a strictly weaker input: a `(6,3)` tie has every leverage at least one, so
"light" degenerates to "leverage exactly one", and on the primitive stratum such
an atom is UNIQUE in the whole design.  Two of the three free atoms are then
strictly heavy and a both-heavy free pair EXISTS.

The uniqueness input is stated as a hypothesis so that this file imports only
landed modules; it is exactly the conclusion of the double-light deflation
theorem, which the Codex lane proved during this wave.
-/

/-- On a tie every leverage is at least one, so a leverage away from one is
strictly heavy. -/
theorem gapExcessOf_pos_of_isTie_of_leverage_ne_one
    (design : WeightedDesign 6 3) (htie : IsTie design) (label : Fin 6)
    (hne : leverageOf (design.atom label) ≠ 1) : 0 < gapExcessOf design label := by
  have hone : 1 ≤ leverageOf (design.atom label) :=
    leverage_one_le_of_isTie_sixThree design htie label
  have hlt : 1 < leverageOf (design.atom label) := lt_of_le_of_ne hone (Ne.symm hne)
  simpa [gapExcessOf, sub_pos] using hlt

/-- **INGREDIENT (a), EXISTENTIAL FORM.**  A tie whose leverage-one atom is
unique has a free pair with BOTH endpoints strictly heavy. -/
theorem exists_heavy_freePair_of_isTie_of_leverageOne_unique
    (design : WeightedDesign 6 3) (htie : IsTie design)
    (hunique : ∀ first second : Fin 6, leverageOf (design.atom first) = 1 →
      leverageOf (design.atom second) = 1 → first = second) :
    ∃ first second : Fin 6, first ∈ ({3, 4, 5} : Finset (Fin 6)) ∧
      second ∈ ({3, 4, 5} : Finset (Fin 6)) ∧ first ≠ second ∧
        0 < gapExcessOf design first ∧ 0 < gapExcessOf design second := by
  by_cases hthree : leverageOf (design.atom 3) = 1
  · have hfour : leverageOf (design.atom 4) ≠ 1 := fun hfour =>
      absurd (hunique 3 4 hthree hfour) (by decide)
    have hfive : leverageOf (design.atom 5) ≠ 1 := fun hfive =>
      absurd (hunique 3 5 hthree hfive) (by decide)
    exact ⟨4, 5, by decide, by decide, by decide,
      gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie 4 hfour,
      gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie 5 hfive⟩
  · by_cases hfour : leverageOf (design.atom 4) = 1
    · have hfive : leverageOf (design.atom 5) ≠ 1 := fun hfive =>
        absurd (hunique 4 5 hfour hfive) (by decide)
      exact ⟨3, 5, by decide, by decide, by decide,
        gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie 3 hthree,
        gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie 5 hfive⟩
    · exact ⟨3, 4, by decide, by decide, by decide,
        gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie 3 hthree,
        gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie 4 hfour⟩

/-- **The general form: of any three distinct labels, two are strictly heavy.**
The free-pair statement above is the instance at `3, 4, 5`; the base-pair
instance is `exists_heavy_basePair_of_isTie_of_leverageOne_unique`. -/
theorem exists_two_heavy_of_isTie_of_leverageOne_unique
    (design : WeightedDesign 6 3) (htie : IsTie design)
    (hunique : ∀ first second : Fin 6, leverageOf (design.atom first) = 1 →
      leverageOf (design.atom second) = 1 → first = second)
    (firstLabel secondLabel thirdLabel : Fin 6)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    (0 < gapExcessOf design firstLabel ∧ 0 < gapExcessOf design secondLabel) ∨
      (0 < gapExcessOf design firstLabel ∧ 0 < gapExcessOf design thirdLabel) ∨
        (0 < gapExcessOf design secondLabel ∧ 0 < gapExcessOf design thirdLabel) := by
  by_cases hfirst : leverageOf (design.atom firstLabel) = 1
  · have hsecond : leverageOf (design.atom secondLabel) ≠ 1 := fun hsecond =>
      hfirstSecond (hunique firstLabel secondLabel hfirst hsecond)
    have hthird : leverageOf (design.atom thirdLabel) ≠ 1 := fun hthird =>
      hfirstThird (hunique firstLabel thirdLabel hfirst hthird)
    exact Or.inr (Or.inr ⟨gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie _ hsecond,
      gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie _ hthird⟩)
  · by_cases hsecond : leverageOf (design.atom secondLabel) = 1
    · have hthird : leverageOf (design.atom thirdLabel) ≠ 1 := fun hthird =>
        hsecondThird (hunique secondLabel thirdLabel hsecond hthird)
      exact Or.inr (Or.inl ⟨gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie _ hfirst,
        gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie _ hthird⟩)
    · exact Or.inl ⟨gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie _ hfirst,
        gapExcessOf_pos_of_isTie_of_leverage_ne_one design htie _ hsecond⟩

/-- **Two of the three BASE labels are strictly heavy too.** -/
theorem exists_heavy_basePair_of_isTie_of_leverageOne_unique
    (design : WeightedDesign 6 3) (htie : IsTie design)
    (hunique : ∀ first second : Fin 6, leverageOf (design.atom first) = 1 →
      leverageOf (design.atom second) = 1 → first = second) :
    ∃ first second : Fin 6, first ∈ ({0, 1, 2} : Finset (Fin 6)) ∧
      second ∈ ({0, 1, 2} : Finset (Fin 6)) ∧ first ≠ second ∧
        0 < gapExcessOf design first ∧ 0 < gapExcessOf design second := by
  rcases exists_two_heavy_of_isTie_of_leverageOne_unique design htie hunique 0 1 2
    (by decide) (by decide) (by decide) with
    ⟨hleft, hright⟩ | ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact ⟨0, 1, by decide, by decide, by decide, hleft, hright⟩
  · exact ⟨0, 2, by decide, by decide, by decide, hleft, hright⟩
  · exact ⟨1, 2, by decide, by decide, by decide, hleft, hright⟩

/-- Line-freeness at the empty family forbids a parallel pair; the pattern side
is a closed finite check. -/
theorem patternForbidsParallelPair_lineFamilyPattern_nil :
    PatternForbidsParallelPair (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  decide

/-- A line-free `(6,3)` design has no parallel pair -- the standing hypothesis of
the double-light deflation. -/
theorem not_hasParallelPair_of_hasLinePattern_nil
    (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    ¬ HasParallelPair design :=
  (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_hasLinePattern patternForbidsParallelPair_lineFamilyPattern_nil
      design hlineFree)

/-- **The failure-locus form.**  On the failure locus of the obligation, with a
unique leverage-one atom, a both-heavy free pair exists. -/
theorem exists_heavy_freePair_of_no_cardThree_posDef_of_leverageOne_unique
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hfail : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef)
    (hunique : ∀ first second : Fin 6, leverageOf (design.atom first) = 1 →
      leverageOf (design.atom second) = 1 → first = second) :
    ∃ first second : Fin 6, first ∈ ({3, 4, 5} : Finset (Fin 6)) ∧
      second ∈ ({3, 4, 5} : Finset (Fin 6)) ∧ first ≠ second ∧
        0 < gapExcessOf design first ∧ 0 < gapExcessOf design second :=
  exists_heavy_freePair_of_isTie_of_leverageOne_unique design
    (isTie_of_dominates_base_of_no_cardThree_posDef design hdominates hfail) hunique

/-! ## Part 9 -- satisfiability and contradictability of the scalar refusal -/

/-- **`FreePairMinorRefusal` IS SATISFIABLE**, at a landed design meeting every
antecedent of the obligation: all three free pair minors of
`freePairKillerDesign` are negative (`-1`, `-31/4`, `-1`). -/
theorem freePairMinorRefusal_freePairKillerDesign :
    FreePairMinorRefusal freePairKillerDesign := by
  intro first second third hfirst hsecond hne _ _
  obtain ⟨firstIndex, rfl⟩ := exists_freeIndex_of_mem_freeTriple first hfirst
  obtain ⟨secondIndex, rfl⟩ := exists_freeIndex_of_mem_freeTriple second hsecond
  refine Or.inl ?_
  have hindex : firstIndex ≠ secondIndex := fun hindex => hne (by rw [hindex])
  revert hindex
  fin_cases firstIndex <;> fin_cases secondIndex <;>
    first
      | (intro hindex; exact absurd rfl hindex)
      | (intro _
         norm_num [freeThreeLabel, pairGapExcessOf, gapExcessOf, gapPairingOf, leverageOf,
           dotProduct, Fin.sum_univ_three, freePairKillerDesign, freePairKillerAtom,
           Matrix.cons_val_two])

/-- **`FreePairMinorRefusal` IS CONTRADICTABLE.**  It FAILS at
`baseTieKillerDesign`, a design meeting every antecedent whose branch is TRUE --
so it is a genuine characterisation of failure and not a statement that also
holds where the branch holds. -/
theorem not_freePairMinorRefusal_baseTieKillerDesign :
    ¬ FreePairMinorRefusal baseTieKillerDesign :=
  fun hrefusal =>
    (freePairMinorRefusal_iff_not_freePairMinorPositiveTie baseTieKillerDesign).mp hrefusal
      freePairMinorPositiveTie_baseTieKillerDesign

end Gtz
