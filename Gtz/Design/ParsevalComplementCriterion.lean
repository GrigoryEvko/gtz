import Gtz.Design.OneLineComplementCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# The Parseval complement criterion

The complement-leverage criterion bounds the complement's squared readings by
`(∑ leverage) * (probe energy)`, which discards every trace of the weights.
Parseval computes the same quantity exactly: the WEIGHTED squared readings of
all labels sum to the probe energy, so the complement's weighted readings are
the probe energy minus the selection's.

* `sum_compl_weighted_sq_eq` is that identity, at every size and every rank.
* `sum_compl_weighted_sq_ge_of_nonpos` is the needle it carries.  A selection
  whose gap form is nonpositive at a probe leaves `(1 - cap)` of the probe
  energy to the complement's WEIGHTED readings.  The cap enters once, on the
  selection's own side, and never again.
* `posDef_of_weightedComplLeverage_lt` is the criterion:
  `∑_{c ∉ S} weight c * leverage c < 1 - cap` forces strict domination.
* `sum_weight_mul_leverage_eq_rank` is the trace of Parseval, so the criterion
  reads `∑_{c ∈ S} weight c * leverage c > rank - 1 + cap`.
* `weightedComplLeverage_le_cap_mul` shows the hypothesis is implied by the
  leverage-criterion hypothesis, so this criterion fires wherever that one does
  and beyond.

The gain is not cosmetic.  The leverage criterion needs `cap * B < 1 - cap` with
`B` the complement's leverage sum; heaviness gives `B ≥ 3`, so it is silent once
`cap ≥ 1/4`.  The weighted sum carries the weights of the complement, which are
free to be small while the cap, a maximum over ALL labels, is large.
-/

variable {size rank : ℕ}

/-! ## The exact complement identity -/

/-- **THE PARSEVAL COMPLEMENT IDENTITY.**  The complement's weighted squared
readings are the probe energy minus the selection's.  No inequality anywhere. -/
theorem sum_compl_weighted_sq_eq (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ) :
    (∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
      = probe ⬝ᵥ probe
        - ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
  rw [sum_weight_mul_sq_dotProduct design probe] at hsplit
  linarith

/-- Every design of positive size is nonempty in its label type. -/
theorem nonempty_label_of_design (design : WeightedDesign size rank) :
    Nonempty (Fin size) := by
  rcases isEmpty_or_nonempty (Fin size) with hemp | hne
  · exact absurd (by
      rw [← design.weight_sum_one, Finset.univ_eq_empty, Finset.sum_empty]) one_ne_zero
  · exact hne

/-! ## The weighted needle -/

/-- **THE WEIGHTED NEEDLE.**  A selection whose gap form is nonpositive at a
probe leaves `(1 - cap)` of the probe energy to the complement's WEIGHTED
squared readings.

The cap is spent once, comparing the selection's weighted readings with its
unweighted ones; Parseval supplies the rest as an equality.  The landed needle
spends the cap a second time on the complement, and that second spend is the
lossy step this theorem removes. -/
theorem sum_compl_weighted_sq_ge_of_nonpos (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ)
    (hnonpos : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) ≤ 0) :
    (1 - cap) * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hcapPos : 0 < cap :=
    pos_of_weight_le design hcap (nonempty_label_of_design design).some
  have hsel : ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
      Matrix.one_mulVec] at hnonpos
    linarith
  have hweighted :
      (∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        ≤ cap * ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun label _ => ?_
    nlinarith [hcap label, sq_nonneg (design.atom label ⬝ᵥ probe)]
  rw [sum_compl_weighted_sq_eq]
  nlinarith [hsel, hweighted, hcapPos]

/-- A failing selection prices its complement's weighted readings. -/
theorem sum_compl_weighted_sq_ge_of_not_posDef (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size))
    (hfail : ¬ (subsetSum design selected - 1).PosDef) :
    ∃ probe : Fin rank → ℝ, probe ≠ 0 ∧
      (1 - cap) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ selectedᶜ,
            design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hprobe, hnonpos⟩ :=
    exists_probe_nonpos_of_not_posDef design selected hfail
  exact ⟨probe, hprobe, sum_compl_weighted_sq_ge_of_nonpos design hcap selected probe hnonpos⟩

/-! ## The criterion -/

/-- **THE PARSEVAL COMPLEMENT CRITERION.**  A cap on the weights and a small
WEIGHTED leverage sum outside the selection force strict domination.

The weighted needle prices a failure from below and Cauchy-Schwarz caps each
weighted reading by its weighted leverage.  The hypothesis separates the two
bounds, so no failure survives. -/
theorem posDef_of_weightedComplLeverage_lt (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size))
    (hlt : (∑ freeLabel ∈ selectedᶜ,
        design.weight freeLabel * leverageOf (design.atom freeLabel)) < 1 - cap) :
    (subsetSum design selected - 1).PosDef := by
  by_contra hfail
  obtain ⟨probe, hprobe, hprice⟩ :=
    sum_compl_weighted_sq_ge_of_not_posDef design hcap selected hfail
  have hpos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos_of_ne_zero hprobe
  have hbound :
      (∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        ≤ (∑ label ∈ selectedᶜ, design.weight label * leverageOf (design.atom label))
            * (probe ⬝ᵥ probe) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun label _ => ?_
    have hcs := sq_dotProduct_le_leverage_mul (design.atom label) probe
    nlinarith [(design.weight_pos label).le]
  nlinarith [hprice, hbound, hpos]

/-! ## The trace of Parseval -/

/-- **THE TRACE IDENTITY.**  The weighted leverages of a design sum to its rank.
This is the trace of the Parseval resolution, read one coordinate at a time. -/
theorem sum_weight_mul_leverage_eq_rank (design : WeightedDesign size rank) :
    (∑ label, design.weight label * leverageOf (design.atom label)) = (rank : ℝ) := by
  have hcol : ∀ i : Fin rank,
      (∑ label, design.weight label * (design.atom label i) ^ 2) = 1 := by
    intro i
    have hparseval := sum_weight_mul_sq_dotProduct design (Pi.single i (1 : ℝ))
    simpa [dotProduct_single, Pi.single_apply] using hparseval
  calc (∑ label, design.weight label * leverageOf (design.atom label))
      = ∑ label, ∑ i, design.weight label * (design.atom label i) ^ 2 := by
        refine Finset.sum_congr rfl fun label _ => ?_
        rw [leverageOf, Finset.mul_sum]
    _ = ∑ i, ∑ label, design.weight label * (design.atom label i) ^ 2 := Finset.sum_comm
    _ = ∑ _i : Fin rank, (1 : ℝ) := Finset.sum_congr rfl fun i _ => hcol i
    _ = (rank : ℝ) := by simp

/-- **THE CRITERION IN TRACE FORM.**  Strict domination follows once the
selection's own weighted leverage passes `rank - 1 + cap`.  The complement's
share is the rest of the rank. -/
theorem posDef_of_selectedWeightedLeverage_gt (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size))
    (hgt : (rank : ℝ) - 1 + cap
        < ∑ label ∈ selected, design.weight label * leverageOf (design.atom label)) :
    (subsetSum design selected - 1).PosDef := by
  refine posDef_of_weightedComplLeverage_lt design hcap selected ?_
  have hsplit := Finset.sum_add_sum_compl selected
    (fun label => design.weight label * leverageOf (design.atom label))
  rw [sum_weight_mul_leverage_eq_rank design] at hsplit
  linarith

/-! ## The criterion subsumes the leverage criterion -/

/-- The weighted complement leverage never exceeds the capped one, so this
criterion's hypothesis is implied by the leverage criterion's. -/
theorem weightedComplLeverage_le_cap_mul (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size)) :
    (∑ label ∈ selectedᶜ, design.weight label * leverageOf (design.atom label))
      ≤ cap * ∑ label ∈ selectedᶜ, leverageOf (design.atom label) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun label _ => ?_
  have hlev : 0 ≤ leverageOf (design.atom label) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [hcap label]

/-! ## The orthogonal complement gap -/

/-- **A DEGENERATE SELECTION HANDS ITS COMPLEMENT A STRICT GAP.**  If every atom
of a selection is orthogonal to a probe, Parseval puts the whole probe energy on
the complement's weighted readings, and the cap turns that into a strictly
positive gap form for the complement at that very probe.

Division-free: the conclusion is `(1 - cap) * energy ≤ cap * gap`.  No case
split, no eigenvalue, and no hypothesis on the complement. -/
theorem cap_mul_complGap_ge_of_orthogonal (design : WeightedDesign size rank) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ)
    (horth : ∀ label ∈ selected, design.atom label ⬝ᵥ probe = 0) :
    (1 - cap) * (probe ⬝ᵥ probe)
      ≤ cap * (probe ⬝ᵥ ((subsetSum design selectedᶜ - 1) *ᵥ probe)) := by
  have hcapPos : 0 < cap :=
    pos_of_weight_le design hcap (nonempty_label_of_design design).some
  have hsel : (∑ label ∈ selected,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun label hlabel => ?_
    rw [horth label hlabel]
    ring
  have hfull : (∑ label ∈ selectedᶜ,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2) = probe ⬝ᵥ probe := by
    rw [sum_compl_weighted_sq_eq, hsel]
    ring
  have hcapBound : (∑ label ∈ selectedᶜ,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        ≤ cap * ∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun label _ => ?_
    nlinarith [hcap label, sq_nonneg (design.atom label ⬝ᵥ probe)]
  have hgap : probe ⬝ᵥ ((subsetSum design selectedᶜ - 1) *ᵥ probe)
      = (∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
      Matrix.one_mulVec]
  rw [hgap]
  nlinarith [hfull, hcapBound]

/-! ## The one-line instances -/

/-- The weighted leverage outside the free triple is the line's. -/
theorem sum_compl_freeTriple_weightedLeverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({3, 4, 5} : Finset (Fin 6)))ᶜ,
        design.weight label * leverageOf (design.atom label))
      = design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 2 * leverageOf (design.atom 2) := by
  rw [compl_freeTriple_eq_lineTriple]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- **THE WEIGHTED LIGHT LINE CLOSES THE TEN-CANDIDATE RESIDUAL.**  The line's
WEIGHTED leverage, not its leverage, is what has to stay below `1 - cap`.

The line atoms may be arbitrarily heavy provided they are lightly weighted, and
the cap is a maximum over all six labels, so this hypothesis does not bound the
cap through the line's leverage. -/
theorem planeBranchTenCandidate_of_weightedLineLeverage_lt (design : WeightedDesign 6 3)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 2 * leverageOf (design.atom 2) < 1 - cap) :
    PlaneBranchTenCandidate design := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
  refine posDef_of_weightedComplLeverage_lt design hcap _ ?_
  rw [sum_compl_freeTriple_weightedLeverage]
  exact hlt

/-- **The residual holds on the lightly-weighted-line region**, with none of the
residual's own six hypotheses consumed. -/
theorem oneLineResidual_of_weightedLineLeverage_lt (design : WeightedDesign 6 3)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 2 * leverageOf (design.atom 2) < 1 - cap)
    (_hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (_hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (_hweightHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel)
    (_hcapBlind : IsCapBlindSpot design)
    (_hlineBlind : IsOneLineNormalBlindSpot design)
    (_hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) :
    PlaneBranchTenCandidate design :=
  planeBranchTenCandidate_of_weightedLineLeverage_lt design hcap hlt

/-- **THE FREE TRIPLE IS STRICT AT THE LINE NORMAL.**  At a direction the three
line atoms all read zero on, the free triple's gap form is strictly positive,
with no case split and no hypothesis beyond the cap.

This is a positive reading at ONE direction, not positive definiteness; it is
the exact statement the line normal supplies. -/
theorem cap_mul_freeTripleGap_ge_at_lineNormal (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap) (probe : Fin 3 → ℝ)
    (horth : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)), design.atom label ⬝ᵥ probe = 0) :
    (1 - cap) * (probe ⬝ᵥ probe)
      ≤ cap * (probe ⬝ᵥ ((subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1) *ᵥ probe)) := by
  have hcompl : (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hbase := cap_mul_complGap_ge_of_orthogonal design hcap
    ({0, 1, 2} : Finset (Fin 6)) probe horth
  rwa [hcompl] at hbase

end Gtz
