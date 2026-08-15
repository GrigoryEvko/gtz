import Gtz.Design.TwoMeetingLinesNeedle
import Gtz.Design.MarginTransfer
import Gtz.Design.FreePairPlane

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-!
# The complement-leverage criterion, and the one-line free triple

The universal needle prices a failing selection: some nonzero probe reads the
complement's squared overlaps above `(1 - cap) / cap` times the probe energy.
Cauchy-Schwarz caps each squared overlap by the atom's leverage. The two bounds
meet, and a selection whose complement carries little leverage cannot fail.

* `posDef_of_cap_mul_complLeverageSum_lt` is the criterion, at every size and
  every rank: `cap * (complement leverage sum) < 1 - cap` forces the selection
  to dominate strictly. It reads no eigenvalue and no determinant.
* `planeBranchTenCandidate_of_lineLeverageSum_lt` is the one-line instance. The
  free triple `{3,4,5}` has the three line atoms as its complement, so a light
  line closes the ten-candidate residual through its last disjunct.

The criterion is unconditional. It assumes no line pattern, no blind spot and
no weak dominator.
-/

variable {size rank : ℕ}

/-! ## The two bounds -/

/-- Cauchy-Schwarz in overlap form. A squared overlap is at most the leverage
times the probe energy. -/
theorem sq_dotProduct_le_leverage_mul (atomVector probe : Fin rank → ℝ) :
    (atomVector ⬝ᵥ probe) ^ 2 ≤ leverageOf atomVector * (probe ⬝ᵥ probe) := by
  rw [← atom_form_eq_sq]
  exact atom_form_le_leverage atomVector probe

/-- The complement's squared overlaps are capped by its leverage sum. -/
theorem sum_compl_sq_le_leverageSum_mul (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ) :
    (∑ label ∈ selectedᶜ, (design.atom label ⬝ᵥ probe) ^ 2)
      ≤ (∑ label ∈ selectedᶜ, leverageOf (design.atom label)) * (probe ⬝ᵥ probe) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun label _ => sq_dotProduct_le_leverage_mul _ _

/-- A nonzero probe carries positive energy. -/
theorem dotProduct_self_pos_of_ne_zero {probe : Fin rank → ℝ} (hprobe : probe ≠ 0) :
    0 < probe ⬝ᵥ probe := by
  rcases (dotProduct_self_nonneg probe).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (eq_zero_of_dotProduct_self_eq_zero heq.symm) hprobe

/-! ## The criterion -/

/-- **THE COMPLEMENT-LEVERAGE CRITERION.**  A cap on the weights and a small
leverage sum outside the selection force strict domination.

The needle prices a failure from below and Cauchy-Schwarz caps the same
quantity from above. The hypothesis separates the two bounds, so no failure
survives. Every quantity is a leverage or a weight. -/
theorem posDef_of_cap_mul_complLeverageSum_lt (design : WeightedDesign size rank)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (selected : Finset (Fin size)) (label : Fin size)
    (hlt : cap * (∑ freeLabel ∈ selectedᶜ, leverageOf (design.atom freeLabel)) < 1 - cap) :
    (subsetSum design selected - 1).PosDef := by
  by_contra hfail
  obtain ⟨probe, hprobe, hprice⟩ :=
    sum_compl_sq_ge_of_not_posDef design hcap selected hfail
  have hcapPos : 0 < cap := pos_of_weight_le design hcap label
  have hpos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos_of_ne_zero hprobe
  have hbound := sum_compl_sq_le_leverageSum_mul design selected probe
  nlinarith [mul_pos hcapPos hpos]

/-! ## The one-line free triple -/

/-- The free triple leaves exactly the three line atoms outside. -/
theorem compl_freeTriple_eq_lineTriple :
    (({3, 4, 5} : Finset (Fin 6)))ᶜ = ({0, 1, 2} : Finset (Fin 6)) := by
  decide

/-- The leverage sum outside the free triple is the line atoms' leverage sum. -/
theorem sum_compl_freeTriple_leverage (design : WeightedDesign 6 3) :
    (∑ label ∈ (({3, 4, 5} : Finset (Fin 6)))ᶜ, leverageOf (design.atom label))
      = leverageOf (design.atom 0) + leverageOf (design.atom 1)
        + leverageOf (design.atom 2) := by
  rw [compl_freeTriple_eq_lineTriple]
  simp [Finset.sum_insert, Finset.mem_insert, add_assoc]

/-- **THE LIGHT LINE CLOSES THE TEN-CANDIDATE RESIDUAL.**  If the weights are
capped and the three line atoms carry leverage sum below `(1 - cap) / cap`,
then the free triple `{3,4,5}` dominates strictly, which is the last of the ten
candidates.

The statement assumes no line pattern and no blind spot: the free triple is a
candidate at every design of size six. -/
theorem planeBranchTenCandidate_of_lineLeverageSum_lt (design : WeightedDesign 6 3)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0) + leverageOf (design.atom 1)
        + leverageOf (design.atom 2)) < 1 - cap) :
    PlaneBranchTenCandidate design := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
  refine posDef_of_cap_mul_complLeverageSum_lt design hcap _ 0 ?_
  rw [sum_compl_freeTriple_leverage]
  exact hlt

/-- **The residual holds on the light-line region.**  Every design of the
one-line residual whose weights are capped and whose line leverage sum stays
below `(1 - cap) / cap` satisfies the ten-candidate selector, with no other
hypothesis of the residual consumed. -/
theorem oneLineResidual_of_lineLeverageSum_lt (design : WeightedDesign 6 3)
    {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hlt : cap * (leverageOf (design.atom 0) + leverageOf (design.atom 1)
        + leverageOf (design.atom 2)) < 1 - cap)
    (_hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (_hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (_hweightHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel)
    (_hcapBlind : IsCapBlindSpot design)
    (_hlineBlind : IsOneLineNormalBlindSpot design)
    (_hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) :
    PlaneBranchTenCandidate design :=
  planeBranchTenCandidate_of_lineLeverageSum_lt design hcap hlt

end Gtz
