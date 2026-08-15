import Gtz.Wave.TwoOutsideMomentLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The two-outside refusal envelope

The one-target refusal law bounds one diagonal entry of the mass-moment Gram.
The polarised moment law supplies its off-diagonal entry and proves that the
resulting `2x2` determinant is strictly positive for distinct K4 labels.

This module composes the two facts.  If every exchange into each of two
outside labels is refused, their mixed moment lies strictly inside the product
of the two scalar refusal budgets.  The contrapositive is the consumable form:
when the closed cross data violate this envelope, an exchange into one of the
two labels is positive definite.

Unlike the old excess threshold, this criterion retains the sign and size of
the mixed cross term.  Together with the K4 circuit decomposition, every term
in its hypothesis is determined by the inverse data of the selected set.
-/

namespace Gtz

open Finset Matrix

/-- Total deletion-pivot excess of a chart selection. -/
noncomputable def chartPivotExcess {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) : ℝ :=
  ∑ label ∈ selected,
    (chartLadderPivot direction mass weight selected label - 1)

/-- A positive-definite mass moment is strictly positive on every nonzero
ladder dual. -/
theorem chartMomentCross_self_pos_of_dual_ne {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (target : Fin size)
    (hmoment : (∑ label, mass label • atomMatrix (direction label)).PosDef)
    (hdual : chartLadderDual direction mass weight selected target ≠ 0) :
    0 < chartMomentCross direction mass weight selected target target := by
  unfold chartMomentCross
  have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hdual
  rwa [star_trivial] at hstep

/-- Pair independence in particular makes each member of the pair nonzero. -/
theorem left_ne_zero_of_pair_independent {dim : ℕ} {left right : Fin dim → ℝ}
    (hindependent : ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • left + rightCoeff • right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0) :
    left ≠ 0 := by
  intro hleft
  have hcoeff := hindependent 1 0 (by rw [hleft]; simp)
  exact one_ne_zero hcoeff.1

/-- Pair independence in particular makes the right member nonzero. -/
theorem right_ne_zero_of_pair_independent {dim : ℕ} {left right : Fin dim → ℝ}
    (hindependent : ∀ leftCoeff rightCoeff : ℝ,
      leftCoeff • left + rightCoeff • right = 0 →
        leftCoeff = 0 ∧ rightCoeff = 0) :
    right ≠ 0 := by
  intro hright
  have hcoeff := hindependent 0 1 (by rw [hright]; simp)
  exact one_ne_zero hcoeff.2

/-- **THE TWO-OUTSIDE REFUSAL ENVELOPE.**  If all exchanges into each of two
distinct outside K4 labels fail, the squared mixed moment is strictly below
the product of their two scalar excess budgets. -/
theorem kFour_twoOutside_refusal_envelope
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    {left right : Fin 6} (hleft : left ∉ selected) (hright : right ∉ selected)
    (hne : left ≠ right)
    (hnoLeft : ∀ leaving ∈ selected,
      ¬ (directionChartGap kFourDirection point.mass point.weight
        (insert left (selected.erase leaving))).PosDef)
    (hnoRight : ∀ leaving ∈ selected,
      ¬ (directionChartGap kFourDirection point.mass point.weight
        (insert right (selected.erase leaving))).PosDef) :
    chartMomentCross kFourDirection point.mass point.weight selected left right ^ 2
      < ((1 + chartLadderPivot kFourDirection point.mass point.weight
              selected left)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected left)
        * ((1 + chartLadderPivot kFourDirection point.mass point.weight
              selected right)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected right) := by
  let moment := ∑ label, point.mass label • atomMatrix (kFourDirection label)
  have hmoment : moment.PosDef := posDef_massMoment_kFourDirection point
  have hindependent :=
    chartLadderDual_pair_independent_of_ladderVector_pair_independent
      kFourDirection point.mass point.weight selected hpd left right
        (kFour_chartLadderVector_pair_independent point hne)
  have hmomentLeft : 0 < chartMomentCross kFourDirection point.mass point.weight
      selected left left := by
    apply chartMomentCross_self_pos_of_dual_ne kFourDirection point.mass
      point.weight selected left hmoment
    exact left_ne_zero_of_pair_independent hindependent
  have hmomentRight : 0 < chartMomentCross kFourDirection point.mass point.weight
      selected right right := by
    apply chartMomentCross_self_pos_of_dual_ne kFourDirection point.mass
      point.weight selected right hmoment
    exact right_ne_zero_of_pair_independent hindependent
  have hpriceLeft := pivot_add_moment_le_excess_of_no_exchange kFourDirection
    point.mass point.weight point.mass_pos point.weight_pos selected hleft hpd
      hnoLeft
  have hpriceRight := pivot_add_moment_le_excess_of_no_exchange kFourDirection
    point.mass point.weight point.mass_pos point.weight_pos selected hright hpd
      hnoRight
  change chartLadderPivot kFourDirection point.mass point.weight selected left
      + chartMomentCross kFourDirection point.mass point.weight selected left left
    ≤ (1 + chartLadderPivot kFourDirection point.mass point.weight selected left)
      * chartPivotExcess kFourDirection point.mass point.weight selected at hpriceLeft
  change chartLadderPivot kFourDirection point.mass point.weight selected right
      + chartMomentCross kFourDirection point.mass point.weight selected right right
    ≤ (1 + chartLadderPivot kFourDirection point.mass point.weight selected right)
      * chartPivotExcess kFourDirection point.mass point.weight selected at hpriceRight
  have hupperLeft :
      chartMomentCross kFourDirection point.mass point.weight selected left left
        ≤ (1 + chartLadderPivot kFourDirection point.mass point.weight selected left)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected left := by
    linarith
  have hupperRight :
      chartMomentCross kFourDirection point.mass point.weight selected right right
        ≤ (1 + chartLadderPivot kFourDirection point.mass point.weight selected right)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected right := by
    linarith
  have hnonnegUpperLeft : 0 ≤
      (1 + chartLadderPivot kFourDirection point.mass point.weight selected left)
          * chartPivotExcess kFourDirection point.mass point.weight selected
        - chartLadderPivot kFourDirection point.mass point.weight selected left :=
    le_trans hmomentLeft.le hupperLeft
  have hproduct :
      chartMomentCross kFourDirection point.mass point.weight selected left left
          * chartMomentCross kFourDirection point.mass point.weight selected right right
        ≤ ((1 + chartLadderPivot kFourDirection point.mass point.weight selected left)
              * chartPivotExcess kFourDirection point.mass point.weight selected
            - chartLadderPivot kFourDirection point.mass point.weight selected left)
          * ((1 + chartLadderPivot kFourDirection point.mass point.weight selected right)
              * chartPivotExcess kFourDirection point.mass point.weight selected
            - chartLadderPivot kFourDirection point.mass point.weight selected right) :=
    mul_le_mul hupperLeft hupperRight hmomentRight.le hnonnegUpperLeft
  exact lt_of_lt_of_le
    (kFour_chartMomentCross_sq_lt_self_mul_self point selected hpd hne) hproduct

/-- Matrix-free form of the refusal envelope.  The mixed moment is the
weight-weighted mixed inverse-cross sum over all six labels. -/
theorem kFour_twoOutside_weightedCross_refusal_envelope
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    {left right : Fin 6} (hleft : left ∉ selected) (hright : right ∉ selected)
    (hne : left ≠ right)
    (hnoLeft : ∀ leaving ∈ selected,
      ¬ (directionChartGap kFourDirection point.mass point.weight
        (insert left (selected.erase leaving))).PosDef)
    (hnoRight : ∀ leaving ∈ selected,
      ¬ (directionChartGap kFourDirection point.mass point.weight
        (insert right (selected.erase leaving))).PosDef) :
    (∑ label, point.weight label
        * chartLadderCross kFourDirection point.mass point.weight selected label left
        * chartLadderCross kFourDirection point.mass point.weight selected label right) ^ 2
      < ((1 + chartLadderPivot kFourDirection point.mass point.weight
              selected left)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected left)
        * ((1 + chartLadderPivot kFourDirection point.mass point.weight
              selected right)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected right) := by
  rw [← chartMomentCross_eq_weighted_cross_mul kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos selected left right]
  exact kFour_twoOutside_refusal_envelope point selected hpd hleft hright hne
    hnoLeft hnoRight

/-- **THE TWO-OUTSIDE EXCHANGE CRITERION.**  If the mixed moment reaches the
product of the two refusal budgets, some exchange into one of the two outside
labels is positive definite. -/
theorem kFour_exists_exchange_of_twoOutside_envelope_failure
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    {left right : Fin 6} (hleft : left ∉ selected) (hright : right ∉ selected)
    (hne : left ≠ right)
    (hfailure :
      ((1 + chartLadderPivot kFourDirection point.mass point.weight selected left)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected left)
        * ((1 + chartLadderPivot kFourDirection point.mass point.weight selected right)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected right)
        ≤ chartMomentCross kFourDirection point.mass point.weight
            selected left right ^ 2) :
    (∃ leaving ∈ selected,
      (directionChartGap kFourDirection point.mass point.weight
        (insert left (selected.erase leaving))).PosDef)
      ∨ ∃ leaving ∈ selected,
        (directionChartGap kFourDirection point.mass point.weight
          (insert right (selected.erase leaving))).PosDef := by
  by_contra hnone
  push Not at hnone
  have henvelope := kFour_twoOutside_refusal_envelope point selected hpd hleft
    hright hne hnone.1 hnone.2
  linarith

/-- The same exchange criterion in the selected-cross coordinates supplied by
the polarised cross-energy identity. -/
theorem kFour_exists_exchange_of_twoOutside_cross_failure
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    {left right : Fin 6} (hleft : left ∉ selected) (hright : right ∉ selected)
    (hne : left ≠ right)
    (hfailure :
      ((1 + chartLadderPivot kFourDirection point.mass point.weight selected left)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected left)
        * ((1 + chartLadderPivot kFourDirection point.mass point.weight selected right)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected right)
        ≤ (∑ source ∈ selected,
              chartLadderCross kFourDirection point.mass point.weight selected
                source left
                * chartLadderCross kFourDirection point.mass point.weight selected
                    source right
            - chartLadderCross kFourDirection point.mass point.weight selected
                left right) ^ 2) :
    (∃ leaving ∈ selected,
      (directionChartGap kFourDirection point.mass point.weight
        (insert left (selected.erase leaving))).PosDef)
      ∨ ∃ leaving ∈ selected,
        (directionChartGap kFourDirection point.mass point.weight
          (insert right (selected.erase leaving))).PosDef := by
  apply kFour_exists_exchange_of_twoOutside_envelope_failure point selected hpd
    hleft hright hne
  have hmixed := crossEnergy_pair_eq_cross_add_moment kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos selected hpd left right
  have hmixed' :
      (∑ source ∈ selected,
          chartLadderCross kFourDirection point.mass point.weight selected
              source left
            * chartLadderCross kFourDirection point.mass point.weight selected
                source right)
          - chartLadderCross kFourDirection point.mass point.weight selected
              left right
        = chartMomentCross kFourDirection point.mass point.weight
            selected left right := by
    linarith
  rwa [hmixed'] at hfailure

/-- A four-label subset of the six-label chart has exactly two distinct
outside labels. -/
theorem kFour_exists_complPair_of_cardFour (selected : Finset (Fin 6))
    (hcard : selected.card = 4) :
    ∃ left right : Fin 6, left ≠ right ∧ selectedᶜ = {left, right} := by
  have hcomplCard : selectedᶜ.card = 2 := by
    rw [Finset.card_compl, hcard]
    norm_num
  obtain ⟨left, right, hne, hpair⟩ := Finset.card_eq_two.mp hcomplCard
  exact ⟨left, right, hne, hpair⟩

/-- Card-four wrapper for the cross-coordinate criterion.  A proof of the
single outside-pair envelope failure produces a concrete positive-definite
exchange. -/
theorem kFour_exists_posDef_exchange_of_cardFour_cross_failure
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hfailure : ∀ left right : Fin 6, left ≠ right → selectedᶜ = {left, right} →
      ((1 + chartLadderPivot kFourDirection point.mass point.weight selected left)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected left)
        * ((1 + chartLadderPivot kFourDirection point.mass point.weight selected right)
            * chartPivotExcess kFourDirection point.mass point.weight selected
          - chartLadderPivot kFourDirection point.mass point.weight selected right)
        ≤ (∑ source ∈ selected,
              chartLadderCross kFourDirection point.mass point.weight selected
                source left
                * chartLadderCross kFourDirection point.mass point.weight selected
                    source right
            - chartLadderCross kFourDirection point.mass point.weight selected
                left right) ^ 2) :
    ∃ entering ∈ selectedᶜ, ∃ leaving ∈ selected,
      (directionChartGap kFourDirection point.mass point.weight
        (insert entering (selected.erase leaving))).PosDef := by
  obtain ⟨left, right, hne, hpair⟩ :=
    kFour_exists_complPair_of_cardFour selected hcard
  have hleftCompl : left ∈ selectedᶜ := by rw [hpair]; simp
  have hrightCompl : right ∈ selectedᶜ := by rw [hpair]; simp
  have hleft : left ∉ selected := Finset.mem_compl.mp hleftCompl
  have hright : right ∉ selected := Finset.mem_compl.mp hrightCompl
  rcases kFour_exists_exchange_of_twoOutside_cross_failure point selected hpd
    hleft hright hne (hfailure left right hne hpair) with hexchange | hexchange
  · obtain ⟨leaving, hmem, hpdExchange⟩ := hexchange
    exact ⟨left, hleftCompl, leaving, hmem, hpdExchange⟩
  · obtain ⟨leaving, hmem, hpdExchange⟩ := hexchange
    exact ⟨right, hrightCompl, leaving, hmem, hpdExchange⟩

end Gtz
