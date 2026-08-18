import Gtz.Wave.OneLineSurvivorWiring
import Gtz.Wave.PivotLoadScoreReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Pivot-load ledgers for the line residuals

The one-line and two-meeting-lines obligations already carry exact
localization theorems: inside their normal blind spots, every strict triple
belongs to the finite candidate family named by the obligation.  Consequently
failure of the named candidate family is not a local failure.  It is the full
no-strict ledger over all twenty triples.

This module spends that observation on the aggregate pivot-load reduction.
It provides:

* one common no-strict pivot ledger for a `(6,3)` design;
* exact equivalences between failure of each line candidate family and the
  global no-strict ledger, under the already-landed localization hypotheses;
* direct scalar producers: a card-three set carrying pivot load at least
  three fires the appropriate finite candidate family.

No registry proposition is changed here.  The load threshold is sufficient,
not asserted necessary; the failure equivalences, by contrast, are exact.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. A common scalar ledger for strict-triple failure -/

/-- The full pivot-load information forced by failure of every strict triple
at `(6,3)`.  Keeping the no-strict hypothesis as the first conjunct makes the
record directly consumable by older refusal and stall reductions. -/
def HasNoStrictPivotLoadLedger (design : WeightedDesign 6 3) : Prop :=
  (∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) ∧
    (∀ selected : Finset (Fin 6), selected.card = 3 →
      ∑ c ∈ selected, pivotLoadScore design c ∈ Set.Ioo (1 : ℝ) 3) ∧
    (∀ selected : Finset (Fin 6), selected.card = 3 →
      ∑ c ∈ selected, scaledResidualDiag design c ∈ Set.Ioo (0 : ℝ) 2) ∧
    (highPivotLabels design).card ≤ 2 ∧
    4 ≤ (lowPivotLabels design).card

/-- Package every universal consequence of a no-strict ledger in one step. -/
theorem hasNoStrictPivotLoadLedger_of_noStrict
    (design : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) :
    HasNoStrictPivotLoadLedger design := by
  refine ⟨hnoStrict, ?_, ?_, ?_, ?_⟩
  · intro selected hcard
    exact triple_pivotLoadScore_mem_Ioo_of_noStrict design hnoStrict selected hcard
  · intro selected hcard
    exact triple_scaledResidualDiag_mem_Ioo_of_noStrict design hnoStrict selected hcard
  · exact card_highPivotLabels_le_two_of_noStrict design hnoStrict
  · exact four_le_card_lowPivotLabels_of_noStrict design hnoStrict

/-- Recover the original global failure ledger from its scalar package. -/
theorem noStrict_of_hasNoStrictPivotLoadLedger
    (design : WeightedDesign 6 3)
    (hledger : HasNoStrictPivotLoadLedger design) :
    ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef :=
  hledger.1

/-- The load window projection of the packaged ledger. -/
theorem triple_pivotLoadScore_mem_Ioo_of_ledger
    (design : WeightedDesign 6 3)
    (hledger : HasNoStrictPivotLoadLedger design)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ∑ c ∈ selected, pivotLoadScore design c ∈ Set.Ioo (1 : ℝ) 3 :=
  hledger.2.1 selected hcard

/-- The residual-diagonal window projection of the packaged ledger. -/
theorem triple_scaledResidualDiag_mem_Ioo_of_ledger
    (design : WeightedDesign 6 3)
    (hledger : HasNoStrictPivotLoadLedger design)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ∑ c ∈ selected, scaledResidualDiag design c ∈ Set.Ioo (0 : ℝ) 2 :=
  hledger.2.2.1 selected hcard

/-! ## 2. One line: exact failure and a scalar producer -/

/-- In the one-line normal blind spot, existence of any strict triple is
equivalent to the ten-candidate disjunction. -/
theorem exists_posDef_cardThree_iff_planeBranchTenCandidate_of_oneLineNormalBlind
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hblind : IsOneLineNormalBlindSpot design) :
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (subsetSum design selected - 1).PosDef) ↔
      PlaneBranchTenCandidate design := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    exact planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind
      design hpattern hblind selected hcard hposDef
  · exact exists_posDef_cardThree_of_planeBranchTenCandidate design

/-- Exact contrapositive form of the one-line localization: failure of the
ten named candidates is failure of all twenty triples. -/
theorem noStrict_iff_not_planeBranchTenCandidate_of_oneLineNormalBlind
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hblind : IsOneLineNormalBlindSpot design) :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef) ↔
      ¬ PlaneBranchTenCandidate design := by
  constructor
  · intro hnoStrict hcandidates
    obtain ⟨selected, hcard, hposDef⟩ :=
      exists_posDef_cardThree_of_planeBranchTenCandidate design hcandidates
    exact hnoStrict selected hcard hposDef
  · intro hfailure selected hcard hposDef
    exact hfailure
      (planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind
        design hpattern hblind selected hcard hposDef)

/-- Failure of the exact one-line candidate family therefore exposes the
common pivot-load ledger, including all twenty strict load windows. -/
theorem hasNoStrictPivotLoadLedger_of_oneLine_candidateFailure
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hblind : IsOneLineNormalBlindSpot design)
    (hfailure : ¬ PlaneBranchTenCandidate design) :
    HasNoStrictPivotLoadLedger design :=
  hasNoStrictPivotLoadLedger_of_noStrict design
    ((noStrict_iff_not_planeBranchTenCandidate_of_oneLineNormalBlind
      design hpattern hblind).mpr hfailure)

/-- A single aggregate-load carrier fires the one-line candidate family.  The
selected triple need not be named in advance: localization places the strict
witness produced by the load theorem into the ten-candidate list. -/
theorem planeBranchTenCandidate_of_oneLine_pivotLoadScore_sum_ge_three
    (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hblind : IsOneLineNormalBlindSpot design)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hload : 3 ≤ ∑ c ∈ selected, pivotLoadScore design c) :
    PlaneBranchTenCandidate design := by
  have hposDef := posDef_subsetSum_of_pivotLoadScore_sum_ge_rank
    design (by norm_num) selected hcard hload
  exact planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind
    design hpattern hblind selected hcard hposDef

/-! ## 3. Two meeting lines: exact failure and the same scalar producer -/

/-- The four-transversal disjunction directly packages a strict card-three
witness. -/
-- **#DUPLICATE (tagged 2026-08-17, verified by read).**  The twin of this
-- declaration is `Gtz.exists_posDef_cardThree_of_twoMeetingLinesTransversalStrict`
-- at Gtz/Wave/OneLineWedgeFlatSplit.lean:1070 — same name, same statement, same
-- proof shape.  Neither module imports the other, and no module imports both,
-- so the clash is latent and today's build passes.  The first module that
-- imports both fails to compile.  KEEP ONE.
theorem exists_posDef_cardThree_of_twoMeetingLinesTransversalStrict
    (design : WeightedDesign 6 3)
    (htransversal : TwoMeetingLinesTransversalStrict design) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum design selected - 1).PosDef := by
  rcases htransversal with h135 | h145 | h235 | h245
  · exact ⟨{1, 3, 5}, by decide, h135⟩
  · exact ⟨{1, 4, 5}, by decide, h145⟩
  · exact ⟨{2, 3, 5}, by decide, h235⟩
  · exact ⟨{2, 4, 5}, by decide, h245⟩

/-- Under both normal blind spots, existence of any strict triple is exactly
the four-transversal statement. -/
theorem exists_posDef_cardThree_iff_twoMeetingLinesTransversalStrict_of_blind
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4}) :
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (subsetSum design selected - 1).PosDef) ↔
      TwoMeetingLinesTransversalStrict design := by
  constructor
  · rintro ⟨selected, hcard, hposDef⟩
    rcases twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
      design normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond selected hcard hposDef with
      h135 | h145 | h235 | h245
    · exact Or.inl (h135 ▸ hposDef)
    · exact Or.inr (Or.inl (h145 ▸ hposDef))
    · exact Or.inr (Or.inr (Or.inl (h235 ▸ hposDef)))
    · exact Or.inr (Or.inr (Or.inr (h245 ▸ hposDef)))
  · exact exists_posDef_cardThree_of_twoMeetingLinesTransversalStrict design

/-- Exact contrapositive form for the two-meeting-lines residual: failure of
the four transversals is failure of every strict triple. -/
theorem noStrict_iff_not_twoMeetingLinesTransversalStrict_of_blind
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4}) :
    (∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef) ↔
      ¬ TwoMeetingLinesTransversalStrict design := by
  constructor
  · intro hnoStrict htransversal
    obtain ⟨selected, hcard, hposDef⟩ :=
      exists_posDef_cardThree_of_twoMeetingLinesTransversalStrict design htransversal
    exact hnoStrict selected hcard hposDef
  · intro hfailure selected hcard hposDef
    apply hfailure
    rcases twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
      design normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond selected hcard hposDef with
      h135 | h145 | h235 | h245
    · exact Or.inl (h135 ▸ hposDef)
    · exact Or.inr (Or.inl (h145 ▸ hposDef))
    · exact Or.inr (Or.inr (Or.inl (h235 ▸ hposDef)))
    · exact Or.inr (Or.inr (Or.inr (h245 ▸ hposDef)))

/-- Failure of the four transversals therefore exposes exactly the same
global scalar ledger as failure of the one-line ten-candidate family. -/
theorem hasNoStrictPivotLoadLedger_of_twoMeetingLines_candidateFailure
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (hfailure : ¬ TwoMeetingLinesTransversalStrict design) :
    HasNoStrictPivotLoadLedger design :=
  hasNoStrictPivotLoadLedger_of_noStrict design
    ((noStrict_iff_not_twoMeetingLinesTransversalStrict_of_blind design
      normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
      hblindFirst hblindSecond).mpr hfailure)

/-- The aggregate load theorem produces one of the four transversals under
the two normal blind spots, again without naming the selected triple first. -/
theorem twoMeetingLinesTransversalStrict_of_pivotLoadScore_sum_ge_three
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hload : 3 ≤ ∑ c ∈ selected, pivotLoadScore design c) :
    TwoMeetingLinesTransversalStrict design := by
  have hposDef := posDef_subsetSum_of_pivotLoadScore_sum_ge_rank
    design (by norm_num) selected hcard hload
  rcases twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
    design normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond selected hcard hposDef with
    h135 | h145 | h235 | h245
  · exact Or.inl (h135 ▸ hposDef)
  · exact Or.inr (Or.inl (h145 ▸ hposDef))
  · exact Or.inr (Or.inr (Or.inl (h235 ▸ hposDef)))
  · exact Or.inr (Or.inr (Or.inr (h245 ▸ hposDef)))

end Gtz
