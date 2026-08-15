import Gtz.Reduction.FrameDropDescent
import Gtz.Wave.LineResidualPivotLoadWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The complement-pivot trace ledger

The full-selection pivot already carries a block-drop theorem:

  `sum_{c in omitted} pivot(univ,c) < 1`

forces the complementary selection to remain positive definite.  This module
spends that theorem on the unresolved `(6,3)` branch instead of reproving its
matrix trace proof.

The resulting ledger is sharper than the pointwise high/low-pivot split.

* every omitted triple has full-pivot sum at least one;
* at most two labels have pivot strictly below `1/3`;
* at least four labels have pivot at least `1/3`;
* since at most two labels have pivot at least one, at least two labels lie in
  the genuine middle band `[1/3,1)`;
* any omitted pair whose pivot sum is below one produces a SPECIFIC stalled
  positive-definite card-four selection, namely its complement.

The last statement connects the scalar projection picture directly to the
card-four stall machinery: a cheap pair trace does not by itself solve the
cell, but it identifies the exact stall that a chart-specific escape must move.

Finally, the one-line and two-meeting-lines localization theorems turn failure
of their finite candidate families into the full ledger without retaining any
geometry in the proof.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The existing block drop, exposed as a complement criterion -/

/-- **THE COMPLEMENT TRACE CRITERION.**  A set whose full-selection pivots sum
to less than one may be omitted while preserving positive definiteness.

This is `posDef_sdiff_of_pivotSum_lt_one` at the full selection.  The theorem is
restated in complement notation because that is the projection/minor form used
by every live `(6,3)` residual. -/
theorem posDef_compl_of_sum_pivot_univ_lt_one (D : WeightedDesign m k)
    (hm : 2 ≤ m) (omitted : Finset (Fin m))
    (hsum : ∑ c ∈ omitted, pivot D Finset.univ c < 1) :
    (subsetSum D omittedᶜ - 1).PosDef := by
  have hdrop := posDef_sdiff_of_pivotSum_lt_one D
    (Finset.subset_univ omitted) (posDef_fullExcess D hm) hsum
  simpa only [← Finset.compl_eq_univ_sdiff] using hdrop

/-- Contrapositive form: failure of the complementary selection prices the
omitted pivot trace by one. -/
theorem one_le_sum_pivot_univ_of_not_posDef_compl (D : WeightedDesign m k)
    (hm : 2 ≤ m) (omitted : Finset (Fin m))
    (hfailure : ¬ (subsetSum D omittedᶜ - 1).PosDef) :
    1 ≤ ∑ c ∈ omitted, pivot D Finset.univ c := by
  by_contra hlt
  push Not at hlt
  exact hfailure (posDef_compl_of_sum_pivot_univ_lt_one D hm omitted hlt)

/-! ## 2. Every omitted triple costs one on the no-strict branch -/

/-- **THE NO-STRICT COMPLEMENT TRACE BARRIER.**  In an unresolved `(6,3)`
design every card-three set, read as the labels OMITTED by its complementary
triple, carries full-selection pivot sum at least one. -/
theorem one_le_sum_pivot_univ_of_noStrict (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (omitted : Finset (Fin 6)) (hcard : omitted.card = 3) :
    1 ≤ ∑ c ∈ omitted, pivot D Finset.univ c := by
  have hcomplCard : omittedᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  exact one_le_sum_pivot_univ_of_not_posDef_compl D (by norm_num) omitted
    (hnoStrict omittedᶜ hcomplCard)

/-- The complement form of the same barrier, convenient when a selected triple
is already in scope. -/
theorem one_le_sum_pivot_univ_compl_of_noStrict (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    1 ≤ ∑ c ∈ selectedᶜ, pivot D Finset.univ c := by
  have hcomplCard : selectedᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  exact one_le_sum_pivot_univ_of_noStrict D hnoStrict selectedᶜ hcomplCard

/-! ## 3. The one-third pivot census -/

/-- Labels whose full-selection pivot is strictly below one third. -/
noncomputable def subThirdPivotLabels (D : WeightedDesign 6 3) : Finset (Fin 6) :=
  Finset.univ.filter fun c => pivot D Finset.univ c < 1 / 3

/-- Labels whose full-selection pivot is at least one third. -/
noncomputable def thirdPivotLabels (D : WeightedDesign 6 3) : Finset (Fin 6) :=
  Finset.univ.filter fun c => 1 / 3 ≤ pivot D Finset.univ c

/-- Labels in the genuine middle band `[1/3,1)`. -/
noncomputable def middlePivotLabels (D : WeightedDesign 6 3) : Finset (Fin 6) :=
  Finset.univ.filter fun c =>
    1 / 3 ≤ pivot D Finset.univ c ∧ pivot D Finset.univ c < 1

/-- The below-third and at-least-third sets are exact complements. -/
theorem subThirdPivotLabels_eq_compl_thirdPivotLabels (D : WeightedDesign 6 3) :
    subThirdPivotLabels D = (thirdPivotLabels D)ᶜ := by
  ext c
  simp only [subThirdPivotLabels, thirdPivotLabels, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_compl, not_le]

/-- **AT MOST TWO SUB-THIRD PIVOTS.**  Three such labels would have total pivot
strictly below one, contradicting the complement trace barrier. -/
theorem card_subThirdPivotLabels_le_two_of_noStrict (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    (subThirdPivotLabels D).card ≤ 2 := by
  by_contra hnot
  have hbig : 3 ≤ (subThirdPivotLabels D).card := by omega
  obtain ⟨selected, hsubset, hcard⟩ := Finset.exists_subset_card_eq hbig
  have hnonempty : selected.Nonempty := Finset.card_pos.mp (by omega)
  have hsumLt : (∑ c ∈ selected, pivot D Finset.univ c) <
      ∑ _c ∈ selected, (1 / 3 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hnonempty fun c hc => ?_
    exact (Finset.mem_filter.mp (hsubset hc)).2
  have hbarrier := one_le_sum_pivot_univ_of_noStrict D hnoStrict selected hcard
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsumLt
  norm_num at hsumLt
  linarith

/-- **AT LEAST FOUR THIRD-PIVOT LABELS.**  This is the complement count of the
previous theorem. -/
theorem four_le_card_thirdPivotLabels_of_noStrict (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    4 ≤ (thirdPivotLabels D).card := by
  have hsmall := card_subThirdPivotLabels_le_two_of_noStrict D hnoStrict
  rw [subThirdPivotLabels_eq_compl_thirdPivotLabels,
    Finset.card_compl, Fintype.card_fin] at hsmall
  omega

/-- High pivots are a subset of the at-least-third pivots. -/
theorem highPivotLabels_subset_thirdPivotLabels (D : WeightedDesign 6 3) :
    highPivotLabels D ⊆ thirdPivotLabels D := by
  intro c hc
  have hhigh := (Finset.mem_filter.mp hc).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ c, ?_⟩
  norm_num
  linarith

/-- The middle band is exactly the third-pivot set after removing the high
pivots. -/
theorem middlePivotLabels_eq_thirdPivotLabels_sdiff_highPivotLabels
    (D : WeightedDesign 6 3) :
    middlePivotLabels D = thirdPivotLabels D \ highPivotLabels D := by
  ext c
  simp only [middlePivotLabels, thirdPivotLabels, highPivotLabels,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨hthird, hlt⟩
    exact ⟨hthird, by simpa only [not_le] using hlt⟩
  · rintro ⟨hthird, hnotHigh⟩
    exact ⟨hthird, by simpa only [not_le] using hnotHigh⟩

/-- **THE MIDDLE-PIVOT FLOOR.**  Every unresolved `(6,3)` design has at least
two labels with pivot in `[1/3,1)`: at least four reach one third, while the
aggregate load theorem permits at most two to reach one. -/
theorem two_le_card_middlePivotLabels_of_noStrict (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    2 ≤ (middlePivotLabels D).card := by
  rw [middlePivotLabels_eq_thirdPivotLabels_sdiff_highPivotLabels,
    Finset.card_sdiff_of_subset (highPivotLabels_subset_thirdPivotLabels D)]
  have hthird := four_le_card_thirdPivotLabels_of_noStrict D hnoStrict
  have hhigh := card_highPivotLabels_le_two_of_noStrict D hnoStrict
  omega

/-! ## 4. A low-pivot pair identifies a specific stall -/

/-- **THE LOW-PAIR STALL.**  On the no-strict branch, if an omitted pair has
full-pivot sum below one, its complement is not merely positive definite: it is
a stalled card-four selection.

The block-drop theorem gives positive definiteness.  Any sub-one chart pivot in
the resulting four-set would erase to a positive-definite triple, contradicting
the ledger. -/
theorem cardFour_stall_of_pair_pivotSum_lt_one_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (omitted : Finset (Fin 6)) (hcard : omitted.card = 2)
    (hsum : ∑ c ∈ omitted, pivot D Finset.univ c < 1) :
    omittedᶜ.card = 4
      ∧ (subsetSum D omittedᶜ - 1).PosDef
      ∧ ∀ label ∈ omittedᶜ,
          1 ≤ chartLadderPivot D.atom (designChartPoint D).mass
            (designChartPoint D).weight omittedᶜ label := by
  have hcomplCard : omittedᶜ.card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hpd : (subsetSum D omittedᶜ - 1).PosDef :=
    posDef_compl_of_sum_pivot_univ_lt_one D (by norm_num) omitted hsum
  refine ⟨hcomplCard, hpd, ?_⟩
  intro label hmem
  by_contra hnot
  have hlt : chartLadderPivot D.atom (designChartPoint D).mass
      (designChartPoint D).weight omittedᶜ label < 1 := lt_of_not_ge hnot
  have hchart : (directionChartGap D.atom (designChartPoint D).mass
      (designChartPoint D).weight omittedᶜ).PosDef := by
    rwa [directionChartGap_designChartPoint D omittedᶜ]
  have heraseChart := (posDef_directionChartGap_erase_iff D.atom
    (designChartPoint D).mass (designChartPoint D).weight
    (designChartPoint D).mass_pos (designChartPoint D).weight_pos
    omittedᶜ hmem hchart).mpr hlt
  have herase : (subsetSum D (omittedᶜ.erase label) - 1).PosDef := by
    rwa [directionChartGap_designChartPoint D (omittedᶜ.erase label)] at heraseChart
  have heraseCard : (omittedᶜ.erase label).card = 3 := by
    rw [Finset.card_erase_of_mem hmem, hcomplCard]
  exact hnoStrict (omittedᶜ.erase label) heraseCard herase

/-! ## 5. One common package and the line-family producers -/

/-- The full scalar package now forced by a no-strict `(6,3)` design. -/
def HasNoStrictComplementPivotLedger (D : WeightedDesign 6 3) : Prop :=
  HasNoStrictPivotLoadLedger D
    ∧ (∀ omitted : Finset (Fin 6), omitted.card = 3 →
        1 ≤ ∑ c ∈ omitted, pivot D Finset.univ c)
    ∧ (subThirdPivotLabels D).card ≤ 2
    ∧ 4 ≤ (thirdPivotLabels D).card
    ∧ 2 ≤ (middlePivotLabels D).card
    ∧ (∀ omitted : Finset (Fin 6), omitted.card = 2 →
        (∑ c ∈ omitted, pivot D Finset.univ c < 1) →
          omittedᶜ.card = 4
            ∧ (subsetSum D omittedᶜ - 1).PosDef
            ∧ ∀ label ∈ omittedᶜ,
                1 ≤ chartLadderPivot D.atom (designChartPoint D).mass
                  (designChartPoint D).weight omittedᶜ label)

/-- Package the complement trace, one-third census and low-pair stalls together
with the previously landed aggregate-load ledger. -/
theorem hasNoStrictComplementPivotLedger_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    HasNoStrictComplementPivotLedger D := by
  refine ⟨hasNoStrictPivotLoadLedger_of_noStrict D hnoStrict,
    one_le_sum_pivot_univ_of_noStrict D hnoStrict,
    card_subThirdPivotLabels_le_two_of_noStrict D hnoStrict,
    four_le_card_thirdPivotLabels_of_noStrict D hnoStrict,
    two_le_card_middlePivotLabels_of_noStrict D hnoStrict, ?_⟩
  intro omitted hcard hsum
  exact cardFour_stall_of_pair_pivotSum_lt_one_of_noStrict
    D hnoStrict omitted hcard hsum

/-- One-line candidate failure exposes the complete complement-pivot ledger. -/
theorem hasNoStrictComplementPivotLedger_of_oneLine_candidateFailure
    (D : WeightedDesign 6 3)
    (hpattern : HasLinePattern D (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hblind : IsOneLineNormalBlindSpot D)
    (hfailure : ¬ PlaneBranchTenCandidate D) :
    HasNoStrictComplementPivotLedger D := by
  apply hasNoStrictComplementPivotLedger_of_noStrict D
  exact (noStrict_iff_not_planeBranchTenCandidate_of_oneLineNormalBlind
    D hpattern hblind).mpr hfailure

/-- Two-meeting-lines candidate failure exposes the same complete ledger. -/
theorem hasNoStrictComplementPivotLedger_of_twoMeetingLines_candidateFailure
    (D : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      D.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      D.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt D normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt D normalSecond {0, 3, 4})
    (hfailure : ¬ TwoMeetingLinesTransversalStrict D) :
    HasNoStrictComplementPivotLedger D := by
  apply hasNoStrictComplementPivotLedger_of_noStrict D
  exact (noStrict_iff_not_twoMeetingLinesTransversalStrict_of_blind D
    normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond).mpr hfailure

end Gtz
