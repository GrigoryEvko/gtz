import Gtz.Design.ParsevalComplementCriterion
import Gtz.Design.ChartlessKill
import Gtz.Quantitative.GeneralPositionWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# The selected-maximum weight criterion

The Parseval complement criterion spends a cap that ranges over ALL labels.
Only the weights INSIDE the selection are ever used, so the cap can be replaced
by the maximum weight of the selection alone.  The complement's weights, which
may be much larger, never enter.

* `posDef_of_selectedWeightedForm_gt` is the criterion in form language: if the
  selection's weighted reading beats `selectedMax` times the probe energy at
  every nonzero probe, the selection dominates strictly.  No leverage is taken,
  so nothing is discarded.
* `posDef_of_complWeightedForm_lt` is the same statement read through Parseval
  at the complement.
* `posDef_of_complWeightedLeverage_lt_selectedMax` is the leverage corollary.
  It is the landed `posDef_of_weightedComplLeverage_lt` with the global cap
  replaced by the selection's own maximum, so it fires wherever that one does
  and beyond.

The form version is strictly stronger than the leverage version.  Passing to
leverages replaces the selection's weighted form by its trace, so a selection
whose weighted form is spread across the rank is priced by its largest
eigenvalue rather than by its trace.

## The orthogonal identity

At a probe every selected atom reads zero on, Parseval gives the complement's
weighted readings EXACTLY: they equal the probe energy.  The landed needle at
such a probe supplies only an inequality.

* `sum_compl_weighted_sq_eq_energy_of_orthogonal` is the identity.
* `one_le_sum_compl_weightedLeverage_of_orthogonal` is its trace consequence:
  the complement carries at least one full unit of weighted leverage.

At the one-line stratum the three line atoms share a unit normal, so the free
triple carries weighted leverage at least one and the line carries at most two.
-/

variable {size rank : ℕ}

/-! ## The gap form -/

/-- The gap form of a selection at a probe: its squared readings minus the
probe energy. -/
theorem dotProduct_gapForm_eq_readings_sub_energy (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe)
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec]

/-! ## The criterion -/

/-- **THE SELECTED-MAXIMUM CRITERION.**  Only the weights inside the selection
are used.  If the selection's weighted reading beats `selectedMax` times the
probe energy at every nonzero probe, the selection dominates strictly.

The proof divides the weighted readings by the selection's own maximum weight,
which is exactly the step the global cap was previously paying for. -/
theorem posDef_of_selectedWeightedForm_gt (design : WeightedDesign size rank)
    {selectedMax : ℝ} (hpos : 0 < selectedMax)
    (selected : Finset (Fin size))
    (hle : ∀ label ∈ selected, design.weight label ≤ selectedMax)
    (hform : ∀ probe : Fin rank → ℝ, probe ≠ 0 →
      selectedMax * (probe ⬝ᵥ probe)
        < ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2) :
    (subsetSum design selected - 1).PosDef := by
  by_contra hfail
  obtain ⟨probe, hprobe, hnonpos⟩ :=
    exists_probe_nonpos_of_not_posDef design selected hfail
  have hgap : (∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2) ≤ probe ⬝ᵥ probe := by
    rw [dotProduct_gapForm_eq_readings_sub_energy] at hnonpos
    linarith
  have hweighted :
      (∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        ≤ selectedMax * ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun label hlabel => ?_
    nlinarith [hle label hlabel, sq_nonneg (design.atom label ⬝ᵥ probe)]
  have hscaled :
      selectedMax * (∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
        ≤ selectedMax * (probe ⬝ᵥ probe) :=
    mul_le_mul_of_nonneg_left hgap hpos.le
  have hstrict := hform probe hprobe
  linarith

/-- **THE COMPLEMENT FORM.**  Read through Parseval, the criterion prices the
complement: a complement whose weighted reading stays below `(1 - selectedMax)`
times the probe energy at every nonzero probe cannot block the selection. -/
theorem posDef_of_complWeightedForm_lt (design : WeightedDesign size rank)
    {selectedMax : ℝ} (hpos : 0 < selectedMax)
    (selected : Finset (Fin size))
    (hle : ∀ label ∈ selected, design.weight label ≤ selectedMax)
    (hform : ∀ probe : Fin rank → ℝ, probe ≠ 0 →
      (∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        < (1 - selectedMax) * (probe ⬝ᵥ probe)) :
    (subsetSum design selected - 1).PosDef := by
  refine posDef_of_selectedWeightedForm_gt design hpos selected hle fun probe hprobe => ?_
  have hid := sum_compl_weighted_sq_eq design selected probe
  have hbound := hform probe hprobe
  linarith

/-- **THE LEVERAGE COROLLARY.**  The landed weighted-leverage criterion with the
global cap replaced by the selection's own maximum weight.  Since that maximum
never exceeds the cap, this fires wherever the landed criterion does, and on
designs whose heavy labels all sit outside the selection it fires when the
landed one is silent. -/
theorem posDef_of_complWeightedLeverage_lt_selectedMax (design : WeightedDesign size rank)
    {selectedMax : ℝ} (hpos : 0 < selectedMax)
    (selected : Finset (Fin size))
    (hle : ∀ label ∈ selected, design.weight label ≤ selectedMax)
    (hlt : (∑ label ∈ selectedᶜ, design.weight label * leverageOf (design.atom label))
        < 1 - selectedMax) :
    (subsetSum design selected - 1).PosDef := by
  refine posDef_of_complWeightedForm_lt design hpos selected hle fun probe hprobe => ?_
  have hpe : 0 < probe ⬝ᵥ probe := dotProduct_self_pos_of_ne_zero hprobe
  have hbound :
      (∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        ≤ (∑ label ∈ selectedᶜ, design.weight label * leverageOf (design.atom label))
            * (probe ⬝ᵥ probe) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun label _ => ?_
    have hcs := sq_dotProduct_le_leverage_mul (design.atom label) probe
    nlinarith [(design.weight_pos label).le]
  nlinarith [hbound, hlt, hpe]

/-! ## The matrix interface -/

/-- **THE CRITERION AS A MATRIX CONDITION.**  Parseval makes the design's total
weighted part the identity, so the complement form condition is the positive
definiteness of one explicit matrix: the complement's weighted part subtracted
from `(1 - selectedMax)` times the identity.

This is the checkable interface.  It is strictly stronger than the leverage
corollary, which replaces the same matrix by its trace. -/
theorem posDef_of_complWeightedMatrix (design : WeightedDesign size rank)
    {selectedMax : ℝ} (hpos : 0 < selectedMax)
    (selected : Finset (Fin size))
    (hle : ∀ label ∈ selected, design.weight label ≤ selectedMax)
    (hmat : ((1 - selectedMax) • (1 : Matrix (Fin rank) (Fin rank) ℝ)
        - ∑ label ∈ selectedᶜ,
            design.weight label • atomMatrix (design.atom label)).PosDef) :
    (subsetSum design selected - 1).PosDef := by
  refine posDef_of_complWeightedForm_lt design hpos selected hle fun probe hprobe => ?_
  have hread := (Matrix.posDef_iff_dotProduct_mulVec.mp hmat).2 hprobe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub,
    dotProduct_sum_smul_atomMatrix_mulVec, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Matrix.one_mulVec] at hread
  linarith

/-! ## The orthogonal identity -/

/-- **THE EXACT ORTHOGONAL IDENTITY.**  At a probe every selected atom reads
zero on, the complement's weighted squared readings equal the probe energy
exactly.  Parseval leaves no inequality: the selected side contributes nothing,
so the complement carries the whole energy. -/
theorem sum_compl_weighted_sq_eq_energy_of_orthogonal (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ)
    (horth : ∀ label ∈ selected, design.atom label ⬝ᵥ probe = 0) :
    (∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
      = probe ⬝ᵥ probe := by
  have hsel : (∑ label ∈ selected,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun label hlabel => ?_
    rw [horth label hlabel]
    ring
  rw [sum_compl_weighted_sq_eq, hsel]
  ring

/-- **THE COMPLEMENT CARRIES A FULL UNIT OF WEIGHTED LEVERAGE.**  A selection
degenerate at some probe hands its complement weighted leverage at least one.

Cauchy-Schwarz turns the exact identity into a trace statement, one term at a
time.  No eigenvalue is extracted. -/
theorem one_le_sum_compl_weightedLeverage_of_orthogonal (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ) (hprobe : probe ≠ 0)
    (horth : ∀ label ∈ selected, design.atom label ⬝ᵥ probe = 0) :
    1 ≤ ∑ label ∈ selectedᶜ, design.weight label * leverageOf (design.atom label) := by
  have hpe : 0 < probe ⬝ᵥ probe := dotProduct_self_pos_of_ne_zero hprobe
  have hexact := sum_compl_weighted_sq_eq_energy_of_orthogonal design selected probe horth
  have hbound :
      (∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        ≤ (∑ label ∈ selectedᶜ, design.weight label * leverageOf (design.atom label))
            * (probe ⬝ᵥ probe) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun label _ => ?_
    have hcs := sq_dotProduct_le_leverage_mul (design.atom label) probe
    nlinarith [(design.weight_pos label).le]
  nlinarith [hexact, hbound, hpe]

/-! ## The one-line stratum -/

/-- The complement of the line triple is the free triple. -/
theorem compl_lineTriple_eq_freeTriple :
    (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by
  decide

/-- The weighted leverage of the free triple, written out. -/
theorem sum_freeTriple_weightedLeverage (design : WeightedDesign 6 3) :
    (∑ label ∈ ({3, 4, 5} : Finset (Fin 6)),
        design.weight label * leverageOf (design.atom label))
      = design.weight 3 * leverageOf (design.atom 3)
        + design.weight 4 * leverageOf (design.atom 4)
        + design.weight 5 * leverageOf (design.atom 5) := by
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- **THE FREE TRIPLE CARRIES A FULL UNIT.**  At the one-line stratum the three
line atoms share a unit normal, so the free triple's weighted leverage is at
least one. -/
theorem one_le_freeTriple_weightedLeverage (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    1 ≤ design.weight 3 * leverageOf (design.atom 3)
      + design.weight 4 * leverageOf (design.atom 4)
      + design.weight 5 * leverageOf (design.atom 5) := by
  obtain ⟨unitNormal, hunit, horth⟩ := oneLine_exists_unitLineNormal design hpattern
  have hne : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  have hbase := one_le_sum_compl_weightedLeverage_of_orthogonal design
    ({0, 1, 2} : Finset (Fin 6)) unitNormal hne horth
  rw [compl_lineTriple_eq_freeTriple, sum_freeTriple_weightedLeverage] at hbase
  exact hbase

/-- **THE LINE CARRIES AT MOST TWO.**  The weighted leverages of a rank-three
design sum to three, and the free triple already holds one of them. -/
theorem sum_lineWeightedLeverage_le_two (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    design.weight 0 * leverageOf (design.atom 0)
      + design.weight 1 * leverageOf (design.atom 1)
      + design.weight 2 * leverageOf (design.atom 2) ≤ 2 := by
  have hfree := one_le_freeTriple_weightedLeverage design hpattern
  have hsplit := Finset.sum_add_sum_compl ({3, 4, 5} : Finset (Fin 6))
    (fun label => design.weight label * leverageOf (design.atom label))
  rw [sum_weight_mul_leverage_eq_rank design, sum_freeTriple_weightedLeverage,
    sum_compl_freeTriple_weightedLeverage] at hsplit
  norm_num at hsplit
  linarith

/-- **THE FREE TRIPLE FIRES ON A LIGHTLY WEIGHTED LINE, PRICED BY ITS OWN
MAXIMUM.**  Only the three FREE weights bound the threshold.  The line atoms
may carry weights as large as the design permits.

This strictly improves the landed criterion, which prices the same conclusion by
a cap ranging over all six labels. -/
theorem planeBranchTenCandidate_of_weightedLineLeverage_lt_freeMax
    (design : WeightedDesign 6 3) {freeMax : ℝ} (hpos : 0 < freeMax)
    (hw3 : design.weight 3 ≤ freeMax) (hw4 : design.weight 4 ≤ freeMax)
    (hw5 : design.weight 5 ≤ freeMax)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 2 * leverageOf (design.atom 2) < 1 - freeMax) :
    PlaneBranchTenCandidate design := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
  refine posDef_of_complWeightedLeverage_lt_selectedMax design hpos
    ({3, 4, 5} : Finset (Fin 6)) ?_ ?_
  · intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with h | h | h <;> subst h <;> assumption
  · rw [sum_compl_freeTriple_weightedLeverage]
    exact hlt

/-- **The residual holds on the region where the line is lightly weighted
against the free triple's own maximum**, with none of the residual's six
hypotheses consumed. -/
theorem oneLineResidual_of_weightedLineLeverage_lt_freeMax
    (design : WeightedDesign 6 3) {freeMax : ℝ} (hpos : 0 < freeMax)
    (hw3 : design.weight 3 ≤ freeMax) (hw4 : design.weight 4 ≤ freeMax)
    (hw5 : design.weight 5 ≤ freeMax)
    (hlt : design.weight 0 * leverageOf (design.atom 0)
        + design.weight 1 * leverageOf (design.atom 1)
        + design.weight 2 * leverageOf (design.atom 2) < 1 - freeMax)
    (_hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (_hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (_hweightHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel)
    (_hcapBlind : IsCapBlindSpot design)
    (_hlineBlind : IsOneLineNormalBlindSpot design)
    (_hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) :
    PlaneBranchTenCandidate design :=
  planeBranchTenCandidate_of_weightedLineLeverage_lt_freeMax design hpos hw3 hw4 hw5 hlt

end Gtz
