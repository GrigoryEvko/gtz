/-
# The residual leverage ledger

Agent 1.3 proved that when a base subset and its complement PARTITION the labels and
the complement is exactly rank-sized, the complement is an orthonormal frame for the
residual metric.  Its report names the scope limit exactly: "At `(7,3)` with a base
triple the complement has FOUR labels and NONE of items 20-23, 29, 31-33 fire.  The
over-complete case is NOT addressed: there `F^T R^-1 F` is a rank-`rank` projection,
not the identity, and nothing here says so."

`(7,3)` is the global frontier cell, so that is the case that matters.  This file
supplies the over-complete statement in the form that survives: not orthonormality,
which is false, but a LEDGER.  Writing

  residualLeverage(c) = t_c * <g_c, R^-1 g_c>,    R = sum over the subset of t_c g_c g_c^T,

the scores are nonnegative, each is at most one, and they SUM TO THE RANK -- exactly the
hat-matrix ledger of least squares, here with no least squares in sight.  Two readings:

* exactly-determined (|S| = rank): rank scores, each at most one, summing to rank, so
  every one equals one.  That re-derives agent 1.3's diagonal half from the ledger, with
  no matrix factorisation and no square root.
* over-complete (|S| > rank): the scores are a sub-probability profile of total mass
  `rank`, so some label carries at least `rank / |S|`.  At `(7,3)` off a base triple:
  four scores, each at most one, summing to three -- some complement atom carries at
  least three quarters.

Everything runs on one shipped identity, `Gtz.trace_mul_atomMatrix`
(Gtz/Design/StressFreeNormalizer.lean:123).
-/
import Gtz.Core.Basic
import Gtz.Design.LeverageBound
import Gtz.Reduction.BranchTransferConstants
import Gtz.Design.StressFreeNormalizer
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1 -- the weighted mass of a label subset -/

/-- The WEIGHTED atom sum of a label subset.  Distinct from `Gtz.subsetSum`, which is
weight-free because domination does not see the weights; the residual metric does. -/
noncomputable def weightedSubsetMass (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) : Matrix (Fin rank) (Fin rank) ℝ :=
  ∑ label ∈ labelSet, design.weight label • atomMatrix (design.atom label)

/-- Parseval, read as a statement about the full label set. -/
theorem weightedSubsetMass_univ (design : WeightedDesign size rank) :
    weightedSubsetMass design Finset.univ = 1 := design.isParseval

/-- **The complement carries the residual.**  Subtracting a base subset's weighted mass
from the identity leaves exactly the complement's weighted mass. -/
theorem weightedSubsetMass_compl_eq_one_sub (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) :
    weightedSubsetMass design baseSetᶜ = 1 - weightedSubsetMass design baseSet := by
  have hsplit : weightedSubsetMass design baseSet + weightedSubsetMass design baseSetᶜ
      = weightedSubsetMass design Finset.univ := by
    rw [weightedSubsetMass, weightedSubsetMass, weightedSubsetMass]
    exact Finset.sum_add_sum_compl baseSet _
  rw [weightedSubsetMass_univ] at hsplit
  rw [← hsplit]
  abel

/-- The quadratic form of a weighted subset mass is the subset's Parseval sum. -/
theorem dotProduct_weightedSubsetMass_mulVec (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ (weightedSubsetMass design labelSet *ᵥ probe)
      = ∑ label ∈ labelSet, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
  rw [weightedSubsetMass, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [smul_mulVec, atomMatrix, Matrix.vecMulVec_mulVec, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, op_smul_eq_mul,
    dotProduct_comm probe (design.atom label)]
  ring

/-- The quadratic form of a weighted subset mass is nonnegative. -/
theorem dotProduct_weightedSubsetMass_mulVec_nonneg (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (probe : Fin rank → ℝ) :
    0 ≤ probe ⬝ᵥ (weightedSubsetMass design labelSet *ᵥ probe) := by
  rw [dotProduct_weightedSubsetMass_mulVec]
  exact Finset.sum_nonneg fun label _ =>
    mul_nonneg (design.weight_pos label).le (sq_nonneg _)

/-- Expanding a trace against a weighted subset mass, one atom at a time.  This is the
whole engine; `Gtz.trace_mul_atomMatrix` does the per-atom step. -/
theorem trace_mul_weightedSubsetMass (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (multiplier : Matrix (Fin rank) (Fin rank) ℝ) :
    Matrix.trace (multiplier * weightedSubsetMass design labelSet)
      = ∑ label ∈ labelSet, design.weight label
          * (design.atom label ⬝ᵥ (multiplier *ᵥ design.atom label)) := by
  rw [weightedSubsetMass, Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]

/-! ## Part 2 -- the ledger -/

/-- **The residual leverage score of a label**, measured in the metric its own subset
generates.  In the exactly-determined case this is identically one; in general it is a
sub-probability weight. -/
noncomputable def residualLeverage (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (label : Fin size) : ℝ :=
  design.weight label
    * (design.atom label ⬝ᵥ ((weightedSubsetMass design labelSet)⁻¹ *ᵥ design.atom label))

/-- **THE LEDGER.**  The residual leverage scores of a subset sum to the rank.  No
heaviness, no tightness, no bound on the subset size -- only invertibility of the mass
the subset itself generates. -/
theorem sum_residualLeverage_eq_rank (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size))
    (hunit : IsUnit (weightedSubsetMass design labelSet).det) :
    ∑ label ∈ labelSet, residualLeverage design labelSet label = (rank : ℝ) := by
  have hkey := trace_mul_weightedSubsetMass design labelSet
    (weightedSubsetMass design labelSet)⁻¹
  rw [Matrix.nonsing_inv_mul _ hunit, Matrix.trace_one, Fintype.card_fin] at hkey
  exact hkey.symm

/-- Recovering an atom from its image under the inverse metric. -/
theorem weightedSubsetMass_mulVec_inv_mulVec (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (probe : Fin rank → ℝ)
    (hunit : IsUnit (weightedSubsetMass design labelSet).det) :
    weightedSubsetMass design labelSet *ᵥ ((weightedSubsetMass design labelSet)⁻¹ *ᵥ probe)
      = probe := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]

/-- The depth of an atom in the inverse metric is nonnegative -- proved from the subset's
own Parseval sum, so no positive definiteness is assumed. -/
theorem dotProduct_inv_weightedSubsetMass_mulVec_nonneg (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (probe : Fin rank → ℝ)
    (hunit : IsUnit (weightedSubsetMass design labelSet).det) :
    0 ≤ probe ⬝ᵥ ((weightedSubsetMass design labelSet)⁻¹ *ᵥ probe) := by
  have hrecover := weightedSubsetMass_mulVec_inv_mulVec design labelSet probe hunit
  have hnonneg := dotProduct_weightedSubsetMass_mulVec_nonneg design labelSet
    ((weightedSubsetMass design labelSet)⁻¹ *ᵥ probe)
  rw [hrecover, dotProduct_comm] at hnonneg
  exact hnonneg

/-- Every residual leverage score is nonnegative. -/
theorem residualLeverage_nonneg (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (label : Fin size)
    (hunit : IsUnit (weightedSubsetMass design labelSet).det) :
    0 ≤ residualLeverage design labelSet label :=
  mul_nonneg (design.weight_pos label).le
    (dotProduct_inv_weightedSubsetMass_mulVec_nonneg design labelSet (design.atom label) hunit)

/-- The scalar step of the leverage cap, isolated from the design. -/
theorem le_one_of_mul_sq_le_self (weightValue depthValue : ℝ)
    (hdepthNonneg : 0 ≤ depthValue)
    (hbound : weightValue * depthValue ^ 2 ≤ depthValue) :
    weightValue * depthValue ≤ 1 := by
  rcases eq_or_lt_of_le hdepthNonneg with hzero | hpos
  · rw [← hzero]; simp
  · nlinarith [hbound, hpos]

/-- **THE CAP.**  A residual leverage score never exceeds one.  The atom's own term is
carved out of the subset's Parseval sum and the remaining terms are nonnegative -- the
Loewner statement `R - t_c g_c g_c^T` positive semidefinite, spelled as scalars. -/
theorem residualLeverage_le_one (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) {pivotLabel : Fin size} (hmem : pivotLabel ∈ labelSet)
    (hunit : IsUnit (weightedSubsetMass design labelSet).det) :
    residualLeverage design labelSet pivotLabel ≤ 1 := by
  have hrecover := weightedSubsetMass_mulVec_inv_mulVec design labelSet
    (design.atom pivotLabel) hunit
  have hquad := dotProduct_weightedSubsetMass_mulVec design labelSet
    ((weightedSubsetMass design labelSet)⁻¹ *ᵥ design.atom pivotLabel)
  rw [hrecover, dotProduct_comm] at hquad
  have hsplit := Finset.add_sum_erase labelSet
    (fun label => design.weight label
      * (design.atom label
          ⬝ᵥ ((weightedSubsetMass design labelSet)⁻¹ *ᵥ design.atom pivotLabel)) ^ 2) hmem
  have hrestNonneg : 0 ≤ ∑ label ∈ labelSet.erase pivotLabel, design.weight label
      * (design.atom label
          ⬝ᵥ ((weightedSubsetMass design labelSet)⁻¹ *ᵥ design.atom pivotLabel)) ^ 2 :=
    Finset.sum_nonneg fun label _ =>
      mul_nonneg (design.weight_pos label).le (sq_nonneg _)
  have hdepthNonneg := dotProduct_inv_weightedSubsetMass_mulVec_nonneg design labelSet
    (design.atom pivotLabel) hunit
  refine le_one_of_mul_sq_le_self (design.weight pivotLabel) _ hdepthNonneg ?_
  linarith [hquad, hsplit, hrestNonneg]

/-! ## Part 3 -- the two readings -/

/-- **Exactly determined: every score is one.**  `rank` scores, each at most one, summing
to `rank`.  This is agent 1.3's diagonal half, re-derived from the ledger without any
matrix factorisation and without a square root. -/
theorem residualLeverage_eq_one_of_card_eq_rank (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (hcard : labelSet.card = rank)
    (hunit : IsUnit (weightedSubsetMass design labelSet).det)
    {pivotLabel : Fin size} (hmem : pivotLabel ∈ labelSet) :
    residualLeverage design labelSet pivotLabel = 1 := by
  have hslackSum : ∑ label ∈ labelSet, (1 - residualLeverage design labelSet label) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      sum_residualLeverage_eq_rank design labelSet hunit, hcard, sub_self]
  have hslackNonneg : ∀ label ∈ labelSet,
      0 ≤ 1 - residualLeverage design labelSet label := fun label hlabel =>
    sub_nonneg.mpr (residualLeverage_le_one design labelSet hlabel hunit)
  have hslackZero := (Finset.sum_eq_zero_iff_of_nonneg hslackNonneg).mp hslackSum pivotLabel hmem
  linarith [hslackZero]

/-- **Over-complete: the scores are a sub-probability profile of total mass `rank`.**
Some label of the subset carries at least the average share. -/
theorem exists_residualLeverage_card_mul_ge (design : WeightedDesign size rank)
    (labelSet : Finset (Fin size)) (hnonempty : labelSet.Nonempty)
    (hunit : IsUnit (weightedSubsetMass design labelSet).det) :
    ∃ heavyLabel ∈ labelSet,
      (rank : ℝ) ≤ labelSet.card * residualLeverage design labelSet heavyLabel := by
  obtain ⟨heavyLabel, hmem, hmax⟩ :=
    Finset.exists_max_image labelSet (residualLeverage design labelSet) hnonempty
  refine ⟨heavyLabel, hmem, ?_⟩
  have hsum := sum_residualLeverage_eq_rank design labelSet hunit
  have hcap : ∑ label ∈ labelSet, residualLeverage design labelSet label
      ≤ labelSet.card • residualLeverage design labelSet heavyLabel :=
    Finset.sum_le_card_nsmul labelSet _ _ hmax
  rw [hsum, nsmul_eq_mul] at hcap
  exact hcap

/-! ## Part 4 -- the ledger is non-vacuous, and it extends a shipped theorem -/

/-- Parseval makes the full label set's mass the identity, whose determinant is a unit.
So the ledger's hypothesis is satisfied by EVERY design at `labelSet = univ`. -/
theorem isUnit_det_weightedSubsetMass_univ (design : WeightedDesign size rank) :
    IsUnit (weightedSubsetMass design Finset.univ).det := by
  rw [weightedSubsetMass_univ, Matrix.det_one]
  exact isUnit_one

/-- **At the full label set the residual leverage IS the atom share.**  The new object
restricts to the tree's `Gtz.atomShare` (Gtz/Reduction/BranchTransferConstants.lean:263),
so the ledger generalises `Gtz.sum_atomShare_eq_rank` from `univ` to an arbitrary subset
measured in its own mass. -/
theorem residualLeverage_univ_eq_atomShare (design : WeightedDesign size rank)
    (label : Fin size) :
    residualLeverage design Finset.univ label = atomShare design label := by
  rw [residualLeverage, atomShare, weightedSubsetMass_univ, inv_one,
    Matrix.one_mulVec, leverageOf_eq_dotProduct]

/-- **Cross-check.**  The shipped share ledger falls out of the residual ledger at
`univ`, by a different route than the tree's own proof. -/
theorem sum_atomShare_eq_rank_ofResidualLedger (design : WeightedDesign size rank) :
    ∑ label, atomShare design label = (rank : ℝ) := by
  rw [← sum_residualLeverage_eq_rank design Finset.univ
    (isUnit_det_weightedSubsetMass_univ design)]
  exact Finset.sum_congr rfl fun label _ => (residualLeverage_univ_eq_atomShare design label).symm

/-! ## Part 5 -- the frontier cell -/

/-- **The `(7,3)` reading.**  Off a base triple the complement carries four labels; the
four residual leverage scores are each at most one and sum to three, so one of them is at
least three quarters.  Nothing here assumes the design is a tie or that the base triple
dominates -- only that the complement's own mass is invertible. -/
theorem exists_residualLeverage_ge_three_quarters_sevenThree (design : WeightedDesign 7 3)
    (baseTriple : Finset (Fin 7)) (hcard : baseTriple.card = 3)
    (hunit : IsUnit (weightedSubsetMass design baseTripleᶜ).det) :
    ∃ heavyLabel ∈ baseTripleᶜ,
      (3 : ℝ) / 4 ≤ residualLeverage design baseTripleᶜ heavyLabel := by
  have hcompl : (baseTripleᶜ : Finset (Fin 7)).card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hnonempty : (baseTripleᶜ : Finset (Fin 7)).Nonempty :=
    Finset.card_pos.mp (by rw [hcompl]; norm_num)
  obtain ⟨heavyLabel, hmem, hbound⟩ :=
    exists_residualLeverage_card_mul_ge design baseTripleᶜ hnonempty hunit
  refine ⟨heavyLabel, hmem, ?_⟩
  rw [hcompl] at hbound
  norm_num at hbound
  linarith [hbound]

/-- At `(7,3)` the complement's four scores are each capped by one, so the profile is a
genuine sub-probability vector of mass three -- the statement that replaces agent 1.3's
orthonormal frame once the complement is over-complete. -/
theorem residualLeverage_le_one_sevenThree (design : WeightedDesign 7 3)
    (baseTriple : Finset (Fin 7))
    (hunit : IsUnit (weightedSubsetMass design baseTripleᶜ).det)
    {pivotLabel : Fin 7} (hmem : pivotLabel ∈ baseTripleᶜ) :
    0 ≤ residualLeverage design baseTripleᶜ pivotLabel
      ∧ residualLeverage design baseTripleᶜ pivotLabel ≤ 1 :=
  ⟨residualLeverage_nonneg design baseTripleᶜ pivotLabel hunit,
    residualLeverage_le_one design baseTripleᶜ hmem hunit⟩

end Gtz
