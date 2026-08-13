/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.MassGapDescent
import Gtz.Reduction.DegenerateHingeArm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The frame-priced descent: Parseval prices every stage, not only the first

The mass-gap descent drops a label of a strictly dominating set when that
label's pivot value is less than one, and the pivot values of the set add up to
the rank plus the trace of the inverse gap.  That budget alone is a pigeonhole
and it stalls: the inverse trace GROWS at every drop, so the criterion prices
the FIRST stage and no later one.

This module supplies the missing price.  The design identity
`Sum_c weight_c * atomMatrix (atom c) = 1` -- the frame law -- contracts against
the inverse gap of an ARBITRARY region and gives the trace of that inverse
exactly.  Thus the pigeonhole becomes an identity at every stage, and the leak
that separates one stage from the next is named and bounded.

## 1. The exact stage law

`Gtz.sum_weight_pivot_eq_trace_inv` -- at every region and with no hypothesis,
the weight-averaged pivot values of ALL labels equal the trace of the inverse
gap of that region.  Subtracting it from the pivot budget gives the stage law
`Gtz.sum_freeWeight_pivot_eq_rank_add_outside`:

  `Sum_{c in R} (1 - weight_c) * pivot_c(R) = rank + Sum_{c not in R} weight_c * pivot_c(R)`.

At `R = univ` the leak is empty, thus `Gtz.sum_freeWeight_pivot_univ_eq_rank`
reads `Sum_c (1 - weight_c) * pivot_c = rank`, and a stalled full set forces
`size <= rank + 1` (`Gtz.exists_pivot_lt_one_univ`).  **THE FIRST DROP IS FREE
AT EVERY DESIGN OF SIZE MORE THAN `rank + 1`, WITH NO WEIGHT HYPOTHESIS.**

## 2. The multi-drop, and the price of a stage

A set of labels whose pivot values add up to less than one drops as a block
(`Gtz.posDef_sdiff_of_pivotSum_lt_one`), because the erased atoms are majorized
by that sum times the gap (`Gtz.gap_form_sdiff_ge_of_pivotSum`).  The same
majorization prices the next stage: after the block drop the pivot values grow
by at most the factor `(1 - sum)` inverted
(`Gtz.pivot_sdiff_le_of_pivotSum`).  Together with the stage law this bounds the
leak, and `Gtz.exists_pivot_lt_one_of_dropBudget` continues the descent.

## 3. What a tie costs

`Gtz.not_isTie_of_pivotDropAtRank` -- the drop condition of the mass-gap module
is STRONGER than the hinge: it forbids ties outright, and
`Gtz.not_pivotDropAtRank_two_one` refutes it at an explicit two-label design.
Thus no successor should attack `Gtz.PivotDropAtRank` itself.
What survives is quantitative: `Gtz.tie_pivotSum_ge_half` -- at a tie EVERY
subset of card `size - rank - 1` carries pivot mass at least one half.

## 4. The mass-gap ledger, sharpened at every excess card

`Gtz.middleInverseFormSum_ge_of_tie` lifts the one-drop cap of the mass-gap
module to a cap on every drop SET.  `Gtz.MiddleFormDrop` names the residue it
leaves, and `Gtz.tieFreeMassGappedStress_of_middleFormDrop` closes the recut arm
from it.  The stress leverage law `Gtz.stressLeverage_le_one` and the negative
side rigidity `Gtz.negSide_leverage_eq_one_of_card_eq_rank` price the residue at
the rank-four deciding cell.

## 5. The re-assembly

The two registry hinge obligations, on the current arm list: the recut mass-gap
arm, the selection, the partial-support arm, the stress-free arm and the
hyperplane cover.

## 6. The frame layer, and what it gives the atom-ceiling program

Part 3 never reads `weight_sum_one`.  Thus the whole stage law holds for a bare
family of atoms resolving the identity with scales of ANY total, which is the
shape the atom-energy ceiling works in.  Part 8 restates the laws there
(`Gtz.frame_stage_law`, `Gtz.frame_exists_pivot_lt_one_univ`), and Part 10
removes the domination hypothesis outright (`Gtz.frame_posDef_gap_univ`).  The
headline: **`Gtz.frame_exists_drop_of_subUnit` -- a frame of more than `rank`
atoms whose positive scales add up to less than one always spares an atom.**
The bare pigeonhole needs the total scale below `(atomCount - rank) / atomCount`
for that; the frame law needs only `less than one`, at every rank and every
count.

## 7. Two free drops

`Gtz.inverseForm_add_atomMatrix` is the exact rank-one pivot update, and with it
`Gtz.exists_two_erase_posDef` gives a strictly dominating subset of card
`size - 2` at every design of size at least `2 * rank + 1`.  The deciding cell of
every rank four and up is such a cell
(`Gtz.exists_two_erase_posDef_thresholdCell`), thus the tie of the hinge never
stalls in the first two stages.
-/

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1: the inverse gap is an inner product -/

/-- A symmetric matrix pairs its two arguments the same way round.  The proof is
the explicit double sum, thus it depends on no Mathlib name that drifts. -/
theorem dotProduct_mulVec_comm_of_symm {dim : ℕ} {gramMat : Matrix (Fin dim) (Fin dim) ℝ}
    (hsymm : gramMatᵀ = gramMat) (leftVec rightVec : Fin dim → ℝ) :
    leftVec ⬝ᵥ (gramMat *ᵥ rightVec) = rightVec ⬝ᵥ (gramMat *ᵥ leftVec) := by
  have hentry : ∀ i j : Fin dim, gramMat j i = gramMat i j := by
    intro i j
    have hcongr := congrFun (congrFun hsymm i) j
    simpa using hcongr
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hentry a b]
  ring

/-- The inverse of a positive definite matrix is symmetric, thus its form is
symmetric. -/
theorem inverseForm_comm {gramMat : Matrix (Fin rank) (Fin rank) ℝ} (hposDef : gramMat.PosDef)
    (leftVec rightVec : Fin rank → ℝ) :
    leftVec ⬝ᵥ (gramMat⁻¹ *ᵥ rightVec) = rightVec ⬝ᵥ (gramMat⁻¹ *ᵥ leftVec) := by
  refine dotProduct_mulVec_comm_of_symm ?_ leftVec rightVec
  rw [Matrix.transpose_nonsing_inv, PosDef.transpose_eq hposDef]

/-- **CAUCHY-SCHWARZ IN THE INVERSE GAP.**  The inverse form of a positive
definite matrix is a genuine inner product, thus its cross term is capped by the
two diagonal terms.  The proof is the discriminant of the quadratic in the shift
parameter, and it inverts nothing. -/
theorem inverseForm_sq_le {gramMat : Matrix (Fin rank) (Fin rank) ℝ} (hposDef : gramMat.PosDef)
    (leftVec rightVec : Fin rank → ℝ) :
    (leftVec ⬝ᵥ (gramMat⁻¹ *ᵥ rightVec)) ^ 2
      ≤ (leftVec ⬝ᵥ (gramMat⁻¹ *ᵥ leftVec)) * (rightVec ⬝ᵥ (gramMat⁻¹ *ᵥ rightVec)) := by
  have hexpand : ∀ shift : ℝ,
      (rightVec ⬝ᵥ (gramMat⁻¹ *ᵥ rightVec)) * (shift * shift)
          + 2 * (leftVec ⬝ᵥ (gramMat⁻¹ *ᵥ rightVec)) * shift
          + (leftVec ⬝ᵥ (gramMat⁻¹ *ᵥ leftVec))
        = (leftVec + shift • rightVec) ⬝ᵥ (gramMat⁻¹ *ᵥ (leftVec + shift • rightVec)) := by
    intro shift
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul,
      inverseForm_comm hposDef rightVec leftVec]
    ring
  have hnonneg : ∀ shift : ℝ, 0 ≤ (rightVec ⬝ᵥ (gramMat⁻¹ *ᵥ rightVec)) * (shift * shift)
      + 2 * (leftVec ⬝ᵥ (gramMat⁻¹ *ᵥ rightVec)) * shift
      + (leftVec ⬝ᵥ (gramMat⁻¹ *ᵥ leftVec)) := by
    intro shift
    rw [hexpand shift]
    exact inverseForm_nonneg hposDef _
  have hdiscrim := discrim_le_zero hnonneg
  rw [discrim] at hdiscrim
  nlinarith [hdiscrim]

/-- The identity matrix is positive definite. -/
theorem posDef_one_matrix : (1 : Matrix (Fin rank) (Fin rank) ℝ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq Matrix.transpose_one, fun probe hprobe => ?_⟩
  rw [star_trivial, Matrix.one_mulVec]
  exact selfDotProduct_pos hprobe

/-! ## Part 2: the multi-drop and the price of one stage -/

/-- **THE BLOCK DROP IS A LOEWNER STEP.**  Erasing a set of labels shrinks the
gap by at most the labels' pivot mass, measured against the gap itself.  Every
erased atom is capped by its own pivot times the gap
(`Gtz.dotProduct_sq_le_inverseForm_mul_form`), and the caps add. -/
theorem gap_form_sdiff_ge_of_pivotSum (design : WeightedDesign size rank)
    {base dropped : Finset (Fin size)} (hsub : dropped ⊆ base)
    (hposDef : (subsetSum design base - 1).PosDef) (probe : Fin rank → ℝ) :
    (1 - ∑ c ∈ dropped, pivot design base c)
        * (probe ⬝ᵥ ((subsetSum design base - 1) *ᵥ probe))
      ≤ probe ⬝ᵥ ((subsetSum design (base \ dropped) - 1) *ᵥ probe) := by
  classical
  have hsplit : subsetSum design (base \ dropped) + ∑ c ∈ dropped, atomMatrix (design.atom c)
      = subsetSum design base := Finset.sum_sdiff hsub
  have hmatrix : subsetSum design (base \ dropped) - 1
      = (subsetSum design base - 1) - ∑ c ∈ dropped, atomMatrix (design.atom c) := by
    rw [← hsplit]; abel
  have hcap : ∀ c ∈ dropped,
      (design.atom c ⬝ᵥ probe) ^ 2
        ≤ pivot design base c * (probe ⬝ᵥ ((subsetSum design base - 1) *ᵥ probe)) := by
    intro c _
    rw [pivot_eq_inverseForm]
    exact dotProduct_sq_le_inverseForm_mul_form hposDef (design.atom c) probe
  have hsum : ∑ c ∈ dropped, (design.atom c ⬝ᵥ probe) ^ 2
      ≤ (∑ c ∈ dropped, pivot design base c)
        * (probe ⬝ᵥ ((subsetSum design base - 1) *ᵥ probe)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hcap
  have hform : probe ⬝ᵥ ((subsetSum design (base \ dropped) - 1) *ᵥ probe)
      = probe ⬝ᵥ ((subsetSum design base - 1) *ᵥ probe)
        - ∑ c ∈ dropped, (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [hmatrix, Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum]
    refine congrArg (fun value => probe ⬝ᵥ ((subsetSum design base - 1) *ᵥ probe) - value) ?_
    exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq (design.atom c) probe
  rw [hform]
  linarith

/-- **THE BLOCK DROP.**  A set of labels whose pivot values add up to less than
one erases without breaking strict domination.  At card one this is
`Gtz.posDef_erase_of_pivot_lt_one`, and the general form is what a descent of
more than one step needs. -/
theorem posDef_sdiff_of_pivotSum_lt_one (design : WeightedDesign size rank)
    {base dropped : Finset (Fin size)} (hsub : dropped ⊆ base)
    (hposDef : (subsetSum design base - 1).PosDef)
    (hsum : ∑ c ∈ dropped, pivot design base c < 1) :
    (subsetSum design (base \ dropped) - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one design (base \ dropped)),
      fun probe hprobe => ?_⟩
  have hbase : 0 < probe ⬝ᵥ ((subsetSum design base - 1) *ᵥ probe) := by
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rwa [star_trivial] at hstep
  have hstep := gap_form_sdiff_ge_of_pivotSum design hsub hposDef probe
  rw [star_trivial]
  nlinarith [hstep, hbase, hsum]

/-- **THE PRICE OF A STAGE.**  After a block drop the pivot values grow by at
most the inverted slack of the dropped mass.  This is the monotone replacement
the pigeonhole lacks: the criterion of the next stage is priced by the criterion
of this one. -/
theorem pivot_sdiff_le_of_pivotSum (design : WeightedDesign size rank)
    {base dropped : Finset (Fin size)} (hsub : dropped ⊆ base)
    (hposDef : (subsetSum design base - 1).PosDef)
    (hsum : ∑ c ∈ dropped, pivot design base c < 1) (label : Fin size) :
    pivot design (base \ dropped) label
      ≤ (1 - ∑ c ∈ dropped, pivot design base c)⁻¹ * pivot design base label := by
  classical
  have hslack : 0 < 1 - ∑ c ∈ dropped, pivot design base c := by linarith
  have hsmall : (subsetSum design (base \ dropped) - 1).PosDef :=
    posDef_sdiff_of_pivotSum_lt_one design hsub hposDef hsum
  have hbound := inverseForm_le_of_form_le_smul hsmall hposDef hslack
    (fun probe => gap_form_sdiff_ge_of_pivotSum design hsub hposDef probe) (design.atom label)
  rw [pivot_eq_inverseForm, pivot_eq_inverseForm]
  exact hbound

/-! ## Part 3: the frame law prices every stage

The design identity is a resolution of the identity matrix.  Contracted against
the inverse gap of ANY region it returns the trace of that inverse exactly.
This is the one ingredient the pivot budget does not carry, and it is the whole
content of this part. -/

/-- **THE FRAME LAW, CONTRACTED.**  The weight-averaged pivot values of ALL
labels against ANY region equal the trace of that region's inverse gap.  No
hypothesis at all: the identity is `trace (gapInv * 1)`. -/
theorem sum_weight_pivot_eq_trace_inv (design : WeightedDesign size rank)
    (base : Finset (Fin size)) :
    ∑ c, design.weight c * pivot design base c
      = Matrix.trace ((subsetSum design base - 1)⁻¹) := by
  classical
  have hterm : ∀ c : Fin size, design.weight c * pivot design base c
      = Matrix.trace ((subsetSum design base - 1)⁻¹
          * (design.weight c • atomMatrix (design.atom c))) := by
    intro c
    simp only [pivot, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Matrix.trace_sum, ← Matrix.mul_sum,
    design.isParseval, Matrix.mul_one]

/-- Every weight of a design is at most one. -/
theorem weight_le_one (design : WeightedDesign size rank) (label : Fin size) :
    design.weight label ≤ 1 := by
  classical
  rw [← design.weight_sum_one]
  exact Finset.single_le_sum (fun c _ => (design.weight_pos c).le) (Finset.mem_univ label)

/-- **THE FULL ATOM SET OF A DESIGN STRICTLY DOMINATES.**  The gap of the whole
label set is the free-mass matrix, and every free weight is positive at two
labels or more.  Thus the descent always has a place to start. -/
theorem posDef_gap_univ (design : WeightedDesign size rank) (htwo : 2 ≤ size) :
    (subsetSum design Finset.univ - 1).PosDef := by
  classical
  have hmatrix : subsetSum design Finset.univ - 1
      = ∑ c, (1 - design.weight c) • atomMatrix (design.atom c) := by
    have hsplit : ∑ c, (1 - design.weight c) • atomMatrix (design.atom c)
        = (∑ c, atomMatrix (design.atom c))
          - ∑ c, design.weight c • atomMatrix (design.atom c) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
    rw [hsplit, design.isParseval, subsetSum]
  have hsymm : (subsetSum design Finset.univ - 1)ᵀ = subsetSum design Finset.univ - 1 :=
    transpose_subsetSum_sub_one design Finset.univ
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial, hmatrix, weighted_atomForm_eq_on]
  obtain ⟨badLabel, hbad⟩ : ∃ c, design.atom c ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hprobe (weightedDesign_atoms_span design hall)
  refine Finset.sum_pos' (fun c _ => ?_) ⟨badLabel, Finset.mem_univ badLabel, ?_⟩
  · exact mul_nonneg (by linarith [weight_le_one design c]) (sq_nonneg _)
  · exact mul_pos (by linarith [weight_lt_one design htwo badLabel])
      (by positivity)

/-- **THE STAGE LAW.**  At every region the free-weight-averaged pivot values of
the region equal the rank plus the LEAK, the weight-averaged pivot values of the
labels outside the region.  This is the pivot budget minus the frame law, and it
holds at every stage of a descent. -/
theorem sum_freeWeight_pivot_eq_rank_add_outside (design : WeightedDesign size rank)
    (base : Finset (Fin size)) (hposDef : (subsetSum design base - 1).PosDef) :
    ∑ c ∈ base, (1 - design.weight c) * pivot design base c
      = (rank : ℝ) + ∑ c ∈ baseᶜ, design.weight c * pivot design base c := by
  classical
  have hall : ∑ c ∈ base, design.weight c * pivot design base c
      + ∑ c ∈ baseᶜ, design.weight c * pivot design base c
      = Matrix.trace ((subsetSum design base - 1)⁻¹) := by
    rw [Finset.sum_add_sum_compl]
    exact sum_weight_pivot_eq_trace_inv design base
  have hbudget := sum_pivot_eq_rank_add_trace_inv design base hposDef
  have hsplit : ∑ c ∈ base, (1 - design.weight c) * pivot design base c
      = ∑ c ∈ base, pivot design base c
        - ∑ c ∈ base, design.weight c * pivot design base c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hbudget]
  linarith

/-- The free-weight version at the full label set: the leak is empty. -/
theorem sum_freeWeight_pivot_univ_eq_rank (design : WeightedDesign size rank)
    (htwo : 2 ≤ size) :
    ∑ c, (1 - design.weight c) * pivot design Finset.univ c = (rank : ℝ) := by
  classical
  have hstep := sum_freeWeight_pivot_eq_rank_add_outside design Finset.univ
    (posDef_gap_univ design htwo)
  rw [Finset.compl_univ, Finset.sum_empty, add_zero] at hstep
  simpa using hstep

/-- **THE STAGE LAW READ AS A DROP.**  A region whose leak is smaller than its
free excess carries a droppable label. -/
theorem exists_pivot_lt_one_of_leak (design : WeightedDesign size rank)
    {base : Finset (Fin size)} (hposDef : (subsetSum design base - 1).PosDef)
    (hleak : ∑ c ∈ baseᶜ, design.weight c * pivot design base c
      < ∑ c ∈ base, (1 - design.weight c) - rank) :
    ∃ label ∈ base, pivot design base label < 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hlower : ∑ c ∈ base, (1 - design.weight c)
      ≤ ∑ c ∈ base, (1 - design.weight c) * pivot design base c := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hfree : 0 ≤ 1 - design.weight c := by linarith [weight_le_one design c]
    nlinarith [hnone c hc, hfree]
  rw [sum_freeWeight_pivot_eq_rank_add_outside design base hposDef] at hlower
  linarith

/-- **THE FIRST DROP IS FREE.**  Every design whose size exceeds `rank + 1`
carries a label the full-set domination can spare.  No weight cap, no spectral
hypothesis, no stress: the frame law alone. -/
theorem exists_pivot_lt_one_univ (design : WeightedDesign size rank) (hbig : rank + 1 < size) :
    ∃ label, pivot design Finset.univ label < 1 := by
  classical
  have htwo : 2 ≤ size := by omega
  have hsum : ∑ c, (1 - design.weight c) = (size : ℝ) - 1 := by
    rw [Finset.sum_sub_distrib, design.weight_sum_one]
    simp
  have hleak : ∑ c ∈ (Finset.univ : Finset (Fin size))ᶜ,
      design.weight c * pivot design Finset.univ c
      < ∑ c, (1 - design.weight c) - rank := by
    rw [Finset.compl_univ, Finset.sum_empty, hsum]
    have hcast : (rank : ℝ) + 1 < (size : ℝ) := by exact_mod_cast hbig
    linarith
  obtain ⟨label, -, hlabel⟩ :=
    exists_pivot_lt_one_of_leak design (posDef_gap_univ design htwo) hleak
  exact ⟨label, hlabel⟩

/-- **A STRICTLY DOMINATING SET OF CARD ONE BELOW THE SIZE.**  The first drop,
carried out. -/
theorem exists_erase_posDef_univ (design : WeightedDesign size rank) (hbig : rank + 1 < size) :
    ∃ label : Fin size, (Finset.univ.erase label).card = size - 1
      ∧ (subsetSum design (Finset.univ.erase label) - 1).PosDef := by
  classical
  have htwo : 2 ≤ size := by omega
  obtain ⟨label, hlabel⟩ := exists_pivot_lt_one_univ design hbig
  refine ⟨label, ?_, posDef_erase_of_pivot_lt_one design (Finset.mem_univ label)
    (posDef_gap_univ design htwo) hlabel⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ, Fintype.card_fin]

/-- **THE MEDIANT OF THE STAGE LAW.**  Some label's pivot value is at most the
rank divided by the free mass of the whole label set.  Stated
multiplication-only, thus no division and no positivity side condition. -/
theorem exists_pivot_univ_le_mediant (design : WeightedDesign size rank) (htwo : 2 ≤ size) :
    ∃ label : Fin size, pivot design Finset.univ label * ((size : ℝ) - 1) ≤ rank := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum : ∑ c, (1 - design.weight c) = (size : ℝ) - 1 := by
    rw [Finset.sum_sub_distrib, design.weight_sum_one]
    simp
  have hbig : ∑ c, (1 - design.weight c) * (rank : ℝ)
      < ∑ c, (1 - design.weight c) * (pivot design Finset.univ c * ((size : ℝ) - 1)) := by
    refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun c _ => ?_
    have hfree : 0 < 1 - design.weight c := by linarith [weight_lt_one design htwo c]
    exact mul_lt_mul_of_pos_left (hnone c) hfree
  rw [← Finset.sum_mul, hsum] at hbig
  have hrewrite : ∑ c, (1 - design.weight c) * (pivot design Finset.univ c * ((size : ℝ) - 1))
      = (∑ c, (1 - design.weight c) * pivot design Finset.univ c) * ((size : ℝ) - 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hrewrite, sum_freeWeight_pivot_univ_eq_rank design htwo] at hbig
  linarith

/-! ## Part 4: the descent of more than one stage, and what a tie costs -/

/-- **THE DESCENT CONTINUES.**  A dropped set whose every member's pivot value
stays below the slack of the dropped mass leaves a region that is still not
stalled, provided the region has more than `rank` labels.  The leak of the
stage law is bounded by the price of the stage. -/
theorem exists_pivot_lt_one_of_dropBudget (design : WeightedDesign size rank)
    (htwo : 2 ≤ size) {dropped : Finset (Fin size)} (hne : dropped.Nonempty)
    (hbudget : ∀ c ∈ dropped, pivot design Finset.univ c
      < 1 - ∑ d ∈ dropped, pivot design Finset.univ d)
    (hcard : rank + 1 ≤ (Finset.univ \ dropped).card) :
    ∃ label ∈ Finset.univ \ dropped, pivot design (Finset.univ \ dropped) label < 1 := by
  classical
  set base := (Finset.univ : Finset (Fin size)) \ dropped with hbase
  have hunivPosDef := posDef_gap_univ design htwo
  obtain ⟨witness, hwitness⟩ := hne
  have hmass : ∑ d ∈ dropped, pivot design Finset.univ d < 1 := by
    have hstep := hbudget witness hwitness
    have hnonneg := pivot_nonneg design Finset.univ hunivPosDef witness
    linarith
  have hslack : 0 < 1 - ∑ d ∈ dropped, pivot design Finset.univ d := by linarith
  have hposDef : (subsetSum design base - 1).PosDef :=
    posDef_sdiff_of_pivotSum_lt_one design (Finset.subset_univ dropped) hunivPosDef hmass
  have houtside : ∀ c ∈ dropped, pivot design base c < 1 := by
    intro c hc
    have hstep := pivot_sdiff_le_of_pivotSum design (Finset.subset_univ dropped) hunivPosDef
      hmass c
    have hscaled : (1 - ∑ d ∈ dropped, pivot design Finset.univ d)⁻¹
        * pivot design Finset.univ c < 1 := by
      rw [inv_mul_lt_iff₀ hslack, mul_one]
      exact hbudget c hc
    exact lt_of_le_of_lt hstep hscaled
  have hcompl : baseᶜ = dropped := by
    rw [hbase]
    ext c
    simp
  have hleak : ∑ c ∈ baseᶜ, design.weight c * pivot design base c
      < ∑ c ∈ base, (1 - design.weight c) - rank := by
    have hstrict : ∑ c ∈ baseᶜ, design.weight c * pivot design base c
        < ∑ c ∈ baseᶜ, design.weight c := by
      rw [hcompl]
      refine Finset.sum_lt_sum_of_nonempty ⟨witness, hwitness⟩ fun c hc => ?_
      have hweight := design.weight_pos c
      nlinarith [houtside c hc]
    have htotal : ∑ c ∈ base, design.weight c + ∑ c ∈ baseᶜ, design.weight c = 1 := by
      rw [Finset.sum_add_sum_compl]
      exact design.weight_sum_one
    have hfree : ∑ c ∈ base, (1 - design.weight c)
        = (base.card : ℝ) - ∑ c ∈ base, design.weight c := by
      rw [Finset.sum_sub_distrib]
      simp
    have hcardBound : (rank : ℝ) + 1 ≤ (base.card : ℝ) := by exact_mod_cast hcard
    linarith
  exact exists_pivot_lt_one_of_leak design hposDef hleak

/-- **THE DEEPEST DROP.**  A dropped set of card `size - rank - 1` whose members
all stay under the slack carries the descent all the way to card `rank`. -/
theorem exists_rankSized_posDef_of_dropBudget (design : WeightedDesign size rank)
    (htwo : 2 ≤ size) (hrank : rank + 2 ≤ size) {dropped : Finset (Fin size)}
    (hcard : dropped.card = size - rank - 1)
    (hbudget : ∀ c ∈ dropped, pivot design Finset.univ c
      < 1 - ∑ d ∈ dropped, pivot design Finset.univ d) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  have hne : dropped.Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have hbaseCard : ((Finset.univ : Finset (Fin size)) \ dropped).card = rank + 1 := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin, hcard]
    omega
  obtain ⟨label, hmem, hlabel⟩ := exists_pivot_lt_one_of_dropBudget design htwo hne hbudget
    (by omega)
  have hunivPosDef := posDef_gap_univ design htwo
  obtain ⟨witness, hwitness⟩ := hne
  have hmass : ∑ d ∈ dropped, pivot design Finset.univ d < 1 := by
    have hstep := hbudget witness hwitness
    have hnonneg := pivot_nonneg design Finset.univ hunivPosDef witness
    linarith
  have hposDef : (subsetSum design ((Finset.univ : Finset (Fin size)) \ dropped) - 1).PosDef :=
    posDef_sdiff_of_pivotSum_lt_one design (Finset.subset_univ dropped) hunivPosDef hmass
  refine ⟨((Finset.univ : Finset (Fin size)) \ dropped).erase label, ?_,
    posDef_erase_of_pivot_lt_one design hmem hposDef hlabel⟩
  rw [Finset.card_erase_of_mem hmem, hbaseCard]
  omega

/-- **A TIE BLOCKS EVERY DEEP DROP.**  At a tie no subset of card
`size - rank - 1` can keep all its pivot values under the slack of its own
mass. -/
theorem tie_dropBudget_blocked (design : WeightedDesign size rank) (htie : IsTie design)
    (htwo : 2 ≤ size) (hrank : rank + 2 ≤ size) {dropped : Finset (Fin size)}
    (hcard : dropped.card = size - rank - 1) :
    ∃ c ∈ dropped, 1 - ∑ d ∈ dropped, pivot design Finset.univ d
      ≤ pivot design Finset.univ c := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨selected, hselectedCard, hselectedPosDef⟩ :=
    exists_rankSized_posDef_of_dropBudget design htwo hrank hcard hnone
  exact htie.2 selected hselectedCard hselectedPosDef

/-- **THE PIVOT MASS OF A TIE.**  At a tie EVERY subset of card
`size - rank - 1` carries pivot mass at least one half against the full label
set.  This is a quantitative, division-free constraint on a tie that no earlier
law supplies. -/
theorem tie_pivotSum_ge_half (design : WeightedDesign size rank) (htie : IsTie design)
    (htwo : 2 ≤ size) (hrank : rank + 2 ≤ size) (dropped : Finset (Fin size))
    (hcard : dropped.card = size - rank - 1) :
    (1 : ℝ) ≤ 2 * ∑ d ∈ dropped, pivot design Finset.univ d := by
  classical
  obtain ⟨witness, hwitness, hstep⟩ := tie_dropBudget_blocked design htie htwo hrank hcard
  have hsingle : pivot design Finset.univ witness
      ≤ ∑ d ∈ dropped, pivot design Finset.univ d :=
    Finset.single_le_sum
      (fun c _ => pivot_nonneg design Finset.univ (posDef_gap_univ design htwo) c) hwitness
  linarith

/-! ### The drop condition is stronger than the hinge

`Gtz.PivotDropAtRank` was introduced in the mass-gap module as a SUFFICIENT
residue for the deepest arm.  It is too strong to be a stepping stone: it
forbids ties outright, while the hinge only asks that a tie carry a parallel
pair.  The explicit two-label design below refutes it. -/

/-- **THE DROP CONDITION FORBIDS TIES.**  Applied to the full label set, which
always dominates strictly, the drop condition carries every design down to a
strictly dominating subset of card `rank`. -/
theorem not_isTie_of_pivotDropAtRank (hdrop : PivotDropAtRank size rank)
    (design : WeightedDesign size rank) (htwo : 2 ≤ size) (hrank : rank < size) :
    ¬ IsTie design := by
  classical
  intro htie
  obtain ⟨dominating, -, hcard, hposDef⟩ :=
    exists_rankSized_posDef_of_pivotDrop' design
      (fun probeSet _hsubset hbig hprobePosDef => hdrop design probeSet hbig hprobePosDef)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
      (posDef_gap_univ design htwo)
  exact htie.2 dominating hcard hposDef

/-- The two-label design of rank one: two equal atoms of unit length, each of
weight one half. -/
noncomputable def tieWitness : WeightedDesign 2 1 where
  atom := fun _ => fun _ => 1
  weight := fun _ => 1 / 2
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_two]
    norm_num
  isParseval := by
    ext i j
    fin_cases i
    fin_cases j
    simp [atomMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]

/-- The gap of every single label of the two-label design vanishes. -/
theorem tieWitness_singleton_gap (label : Fin 2) :
    subsetSum tieWitness {label} - 1 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [subsetSum, tieWitness, atomMatrix, Matrix.vecMulVec_apply]

/-- **THE TWO-LABEL DESIGN IS A TIE.**  Each single label dominates weakly and
none dominates strictly. -/
theorem isTie_tieWitness : IsTie tieWitness := by
  classical
  constructor
  · refine ⟨{(0 : Fin 2)}, by simp, ?_⟩
    rw [Dominates, tieWitness_singleton_gap]
    exact Matrix.PosSemidef.zero
  · intro selected hcard hposDef
    obtain ⟨label, hlabel⟩ := Finset.card_eq_one.mp hcard
    rw [hlabel, tieWitness_singleton_gap] at hposDef
    have hprobe : (fun _ => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
      intro hzero
      have := congrFun hzero ⟨0, by omega⟩
      norm_num at this
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rw [star_trivial, Matrix.zero_mulVec, dotProduct_zero] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- **THE DROP CONDITION IS FALSE.**  A design carrying a tie refutes it, and
the two-label design of rank one is such a design.  Thus no successor should
attack `Gtz.PivotDropAtRank`: the design-level frame law does NOT make the bare
drop condition true, because a tie is exactly its counterexample. -/
theorem not_pivotDropAtRank_two_one : ¬ PivotDropAtRank 2 1 := fun hdrop =>
  not_isTie_of_pivotDropAtRank hdrop tieWitness (by omega) (by omega) isTie_tieWitness

/-! ### The Loewner reading of the frame law

The frame law also gives a scalar floor for the gap of the full label set, in
terms of the largest weight.  It is weaker than the stage law of Part 3 at the
full set, but it is the form a region-wise argument consumes when the leak is
not available. -/

/-- **THE GAP OF THE FULL SET IS FLOORED BY THE LARGEST WEIGHT.**  With every
weight at most `weightCap`, the gap of the full label set majorizes the identity
scaled by the free ratio of that cap. -/
theorem gap_univ_form_ge_of_maxWeight (design : WeightedDesign size rank)
    {weightCap : ℝ} (hcapPos : 0 < weightCap) (hcap : ∀ c, design.weight c ≤ weightCap)
    (probe : Fin rank → ℝ) :
    ((1 - weightCap) / weightCap) * (probe ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ probe))
      ≤ probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe) := by
  classical
  have hparseval : ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
    rw [← weighted_atomForm_eq_on Finset.univ design.weight design.atom probe, design.isParseval,
      Matrix.one_mulVec]
  have hgap : probe ⬝ᵥ ((subsetSum design Finset.univ - 1) *ᵥ probe)
      = (∑ c, (design.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, subsetSum, Matrix.sum_mulVec,
      dotProduct_sum]
    refine congrArg (fun value => value - probe ⬝ᵥ probe) ?_
    exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq (design.atom c) probe
  have hscaled : ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      ≤ weightCap * ∑ c, (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_right (hcap c) (sq_nonneg _)
  rw [hgap, Matrix.one_mulVec, div_mul_eq_mul_div, div_le_iff₀ hcapPos]
  nlinarith [hparseval, hscaled]

/-- The gap of the full set, as a Loewner floor with the identity as the middle
matrix.  This is the shape `Gtz.trace_inv_le_of_form_le_smul` consumes. -/
theorem trace_inv_univ_le_of_maxWeight (design : WeightedDesign size rank) (htwo : 2 ≤ size)
    {weightCap : ℝ} (hcapPos : 0 < weightCap) (hcapLt : weightCap < 1)
    (hcap : ∀ c, design.weight c ≤ weightCap) :
    Matrix.trace ((subsetSum design Finset.univ - 1)⁻¹)
      ≤ ((1 - weightCap) / weightCap)⁻¹ * (rank : ℝ) := by
  have hlevel : 0 < (1 - weightCap) / weightCap := div_pos (by linarith) hcapPos
  have hstep := trace_inv_le_of_form_le_smul (posDef_gap_univ design htwo)
    (posDef_one_matrix (rank := rank)) hlevel
    (fun probe => gap_univ_form_ge_of_maxWeight design hcapPos hcap probe)
  rwa [inv_one, Matrix.trace_one, Fintype.card_fin] at hstep

/-! ## Part 5: the stress leverage law -/

/-- The middle form of a stress dominates each of its own terms. -/
theorem middleForm_ge_single {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (coeff : Fin atomCount → ℝ) (support : Finset (Fin atomCount))
    (hnonneg : ∀ c ∈ support, 0 ≤ coeff c) {label : Fin atomCount} (hlabel : label ∈ support)
    (probe : Fin rank → ℝ) :
    coeff label * (atomFamily label ⬝ᵥ probe) ^ 2
      ≤ probe ⬝ᵥ ((∑ c ∈ support, coeff c • atomMatrix (atomFamily c)) *ᵥ probe) := by
  rw [weighted_atomForm_eq_on]
  exact Finset.single_le_sum (f := fun c => coeff c * (atomFamily c ⬝ᵥ probe) ^ 2)
    (fun c hc => mul_nonneg (hnonneg c hc) (sq_nonneg _)) hlabel

/-- **THE LEVERAGE SCORE IS AT MOST ONE.**  A vector that the matrix dominates,
scaled by its own coefficient, has inverse form at most one.  The proof reads
the domination at the dual vector and nowhere else. -/
theorem inverseForm_scaled_le_one {middleMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hmiddle : middleMat.PosDef) {scale : ℝ} {source : Fin rank → ℝ}
    (hdominated : ∀ probe : Fin rank → ℝ,
      scale * (source ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ (middleMat *ᵥ probe)) :
    scale * (source ⬝ᵥ (middleMat⁻¹ *ᵥ source)) ≤ 1 := by
  have hunit : IsUnit middleMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hmiddle.det_pos)
  set dual : Fin rank → ℝ := middleMat⁻¹ *ᵥ source with hdual
  have hmulDual : middleMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv middleMat hunit, Matrix.one_mulVec]
  have hdualForm : dual ⬝ᵥ (middleMat *ᵥ dual) = source ⬝ᵥ dual := by
    rw [hmulDual, dotProduct_comm]
  have hpair : (source ⬝ᵥ dual) = source ⬝ᵥ (middleMat⁻¹ *ᵥ source) := rfl
  have hstep := hdominated dual
  rw [hdualForm] at hstep
  have hnonneg : 0 ≤ source ⬝ᵥ dual := inverseForm_nonneg hmiddle source
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · rw [hpair] at hzero
    rw [← hzero, mul_zero]
    norm_num
  · rw [hpair] at hpos hstep ⊢
    nlinarith [hstep, hpos]

/-- **THE POSITIVE SIDE LEVERAGE.**  Each positive-side leverage score of a
full-support stress is at most one. -/
theorem stressLeverage_le_one (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hmiddle : (∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
      stressCoeff c • atomMatrix (design.atom c)).PosDef)
    {label : Fin size} (hlabel : 0 < stressCoeff label) :
    stressCoeff label * (design.atom label ⬝ᵥ
        ((∑ d ∈ Finset.univ.filter fun d => 0 < stressCoeff d,
          stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom label))
      ≤ 1 := by
  classical
  refine inverseForm_scaled_le_one hmiddle fun probe => ?_
  exact middleForm_ge_single design.atom stressCoeff _
    (fun c hc => le_of_lt (Finset.mem_filter.mp hc).2)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hlabel⟩) probe

/-- **THE MIDDLE BUDGET, GENERAL.**  The coefficient-weighted inverse forms of a
positive definite coefficient sum add up to the rank exactly.  The design
version `Gtz.sum_stress_middleInverseForm_eq_rank` is one instance. -/
theorem sum_coeff_inverseForm_eq_rank {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (coeff : Fin atomCount → ℝ)
    (support : Finset (Fin atomCount))
    (hposDef : (∑ c ∈ support, coeff c • atomMatrix (atomFamily c)).PosDef) :
    ∑ c ∈ support, coeff c * (atomFamily c ⬝ᵥ
        ((∑ d ∈ support, coeff d • atomMatrix (atomFamily d))⁻¹ *ᵥ atomFamily c))
      = (rank : ℝ) := by
  classical
  set middleMat : Matrix (Fin rank) (Fin rank) ℝ :=
    ∑ c ∈ support, coeff c • atomMatrix (atomFamily c) with hmiddleMat
  have hunit : IsUnit middleMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hterm : ∀ c ∈ support,
      coeff c * (atomFamily c ⬝ᵥ (middleMat⁻¹ *ᵥ atomFamily c))
        = Matrix.trace (middleMat⁻¹ * (coeff c • atomMatrix (atomFamily c))) := by
    intro c _
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  rw [Finset.sum_congr rfl hterm, ← Matrix.trace_sum, ← Matrix.mul_sum, ← hmiddleMat,
    Matrix.nonsing_inv_mul middleMat hunit, Matrix.trace_one, Fintype.card_fin]

/-- **THE NEGATIVE SIDE RIGIDITY.**  When the negative side of a full-support
stress carries exactly `rank` labels, EVERY negative-side leverage score is
exactly one.  The scores are at most one and they add up to the rank over the
same number of labels. -/
theorem negSide_leverage_eq_one_of_card_eq_rank (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hmiddle : (∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
      stressCoeff c • atomMatrix (design.atom c)).PosDef)
    (hcard : (Finset.univ.filter fun c => stressCoeff c < 0).card = rank)
    {label : Fin size} (hlabel : stressCoeff label < 0) :
    (-stressCoeff label) * (design.atom label ⬝ᵥ
        ((∑ d ∈ Finset.univ.filter fun d => 0 < stressCoeff d,
          stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom label))
      = 1 := by
  classical
  set negSide := Finset.univ.filter (fun c => stressCoeff c < 0) with hnegSide
  set middleMat : Matrix (Fin rank) (Fin rank) ℝ :=
    ∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
      stressCoeff c • atomMatrix (design.atom c) with hmiddleMat
  have hswap : middleMat = ∑ c ∈ negSide, (-stressCoeff c) • atomMatrix (design.atom c) := by
    rw [hmiddleMat, hnegSide]
    exact posSideSum_eq_negSideSum design.atom hstress
  have hnegPosDef : (∑ c ∈ negSide, (-stressCoeff c) • atomMatrix (design.atom c)).PosDef := by
    rw [← hswap]; exact hmiddle
  have hbudget := sum_coeff_inverseForm_eq_rank design.atom (fun c => -stressCoeff c) negSide
    hnegPosDef
  rw [← hswap] at hbudget
  have hle : ∀ c ∈ negSide,
      (-stressCoeff c) * (design.atom c ⬝ᵥ (middleMat⁻¹ *ᵥ design.atom c)) ≤ 1 := by
    intro c hc
    have hsign : stressCoeff c < 0 := by
      rw [hnegSide] at hc
      exact (Finset.mem_filter.mp hc).2
    refine inverseForm_scaled_le_one hmiddle fun probe => ?_
    rw [hswap]
    refine middleForm_ge_single design.atom (fun d => -stressCoeff d) negSide
      (fun d hd => ?_) hc probe
    have hdsign : stressCoeff d < 0 := by
      rw [hnegSide] at hd
      exact (Finset.mem_filter.mp hd).2
    linarith
  have hmem : label ∈ negSide := by
    rw [hnegSide]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ label, hlabel⟩
  by_contra hne
  have hlt : (-stressCoeff label) * (design.atom label ⬝ᵥ (middleMat⁻¹ *ᵥ design.atom label))
      < 1 := lt_of_le_of_ne (hle label hmem) hne
  have hstrict : ∑ c ∈ negSide, (-stressCoeff c)
        * (design.atom c ⬝ᵥ (middleMat⁻¹ *ᵥ design.atom c))
      < ∑ c ∈ negSide, (1 : ℝ) :=
    Finset.sum_lt_sum (fun c hc => hle c hc) ⟨label, hmem, hlt⟩
  rw [hbudget, Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at hstrict
  exact absurd hstrict (lt_irrefl _)

/-! ## Part 6: the mass-gap ledger at every excess card -/

/-- **THE PIVOT OF THE POSITIVE SIDE IS PRICED BY THE MIDDLE MATRIX.**  This is
the per-label half of `Gtz.exists_pivot_lt_one_of_massGap`, extracted so that a
drop SET can consume it. -/
theorem pivot_posSide_le_middleInverseForm (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (hlevel : boundCeiling < freeFloor) (label : Fin size) :
    pivot design (Finset.univ.filter fun c => 0 < stressCoeff c) label
      ≤ (freeFloor - boundCeiling)⁻¹ * (design.atom label ⬝ᵥ
          ((∑ d ∈ Finset.univ.filter fun d => 0 < stressCoeff d,
            stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom label)) := by
  classical
  have hlevelPos : 0 < freeFloor - boundCeiling := by linarith
  have hspans : ∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
    pos_side_spans design.atom
      (fun _probe hprobe => weightedDesign_atoms_span design hprobe) hstress hfull
  have hmiddlePosDef := posDef_posSideSum_of_spans design.atom hspans
  have hgapPosDef : (subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c)
      - 1).PosDef :=
    posDef_gap_posSide_of_massGap design hstress hfull
      ⟨freeFloor, boundCeiling, hfree, hbound, hlevel⟩
  rw [pivot_eq_inverseForm]
  exact inverseForm_le_of_form_le_smul hgapPosDef hmiddlePosDef hlevelPos
    (fun probe => massGap_gap_form_ge design hstress hfull hfree hbound probe) (design.atom label)

/-- **THE SHARP CAP AT EVERY EXCESS CARD.**  A tie forces the level difference of
every mass-gapped stress under the middle inverse form of EVERY drop set that
would reach card `rank`.  At a drop set of card one this is
`Gtz.massProduct_le_rank_of_tie_of_posSideCard_succ` read through the mediant,
and at higher cards it is new: the shipped ledger stopped at one drop. -/
theorem middleInverseFormSum_ge_of_tie (design : WeightedDesign size rank)
    (htie : IsTie design) {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (hlevel : boundCeiling < freeFloor) {dropped : Finset (Fin size)}
    (hsub : dropped ⊆ Finset.univ.filter fun c => 0 < stressCoeff c)
    (hcard : ((Finset.univ.filter fun c => 0 < stressCoeff c) \ dropped).card = rank) :
    freeFloor - boundCeiling
      ≤ ∑ c ∈ dropped, (design.atom c ⬝ᵥ
          ((∑ d ∈ Finset.univ.filter fun d => 0 < stressCoeff d,
            stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c)) := by
  classical
  by_contra hsmall
  push Not at hsmall
  have hlevelPos : 0 < freeFloor - boundCeiling := by linarith
  have hgapPosDef : (subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c)
      - 1).PosDef :=
    posDef_gap_posSide_of_massGap design hstress hfull
      ⟨freeFloor, boundCeiling, hfree, hbound, hlevel⟩
  have hpivotSum : ∑ c ∈ dropped,
      pivot design (Finset.univ.filter fun c => 0 < stressCoeff c) c < 1 := by
    have hterm : ∑ c ∈ dropped,
        pivot design (Finset.univ.filter fun c => 0 < stressCoeff c) c
        ≤ (freeFloor - boundCeiling)⁻¹ * ∑ c ∈ dropped, (design.atom c ⬝ᵥ
            ((∑ d ∈ Finset.univ.filter fun d => 0 < stressCoeff d,
              stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun c _ =>
        pivot_posSide_le_middleInverseForm design hstress hfull hfree hbound hlevel c
    have hscaled : (freeFloor - boundCeiling)⁻¹ * ∑ c ∈ dropped, (design.atom c ⬝ᵥ
        ((∑ d ∈ Finset.univ.filter fun d => 0 < stressCoeff d,
          stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c)) < 1 := by
      rw [inv_mul_lt_iff₀ hlevelPos, mul_one]
      exact hsmall
    exact lt_of_le_of_lt hterm hscaled
  exact htie.2 _ hcard
    (posDef_sdiff_of_pivotSum_lt_one design hsub hgapPosDef hpivotSum)

/-- **THE RESIDUE OF THE RECUT ARM, AS A DROP.**  A mass-gapped full-support
stress whose positive side carries a drop set of small middle inverse form
closes the recut arm.  This strictly generalizes the shipped one-drop firing:
at a drop set of card one it IS `Gtz.exists_pivot_lt_one_of_massGap`. -/
def MiddleFormDrop (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ)
      (freeFloor boundCeiling : ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    IsPrimitiveDesign design →
    (∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c) →
    (∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c)) →
    boundCeiling < freeFloor →
    ∃ dropped ⊆ Finset.univ.filter fun c => 0 < stressCoeff c,
      ((Finset.univ.filter fun c => 0 < stressCoeff c) \ dropped).card = rank
        ∧ ∑ c ∈ dropped, (design.atom c ⬝ᵥ
            ((∑ d ∈ Finset.univ.filter fun d => 0 < stressCoeff d,
              stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c))
          < freeFloor - boundCeiling

/-- **THE RECUT ARM FROM THE DROP RESIDUE.** -/
theorem tieFreeMassGappedStress_of_middleFormDrop (hdrop : MiddleFormDrop size rank) :
    TieFreeMassGappedStress size rank := by
  classical
  intro design stressCoeff hstress hfull hprimitive htie hgap
  obtain ⟨freeFloor, boundCeiling, hfree, hbound, hlevel⟩ := hgap
  obtain ⟨dropped, hsub, hcard, hsmall⟩ := hdrop design stressCoeff freeFloor boundCeiling
    hstress hfull hprimitive hfree hbound hlevel
  exact absurd (middleInverseFormSum_ge_of_tie design htie hstress hfull hfree hbound hlevel
    hsub hcard) (not_le.mpr hsmall)

/-- The rank-four deciding cell: the recut arm reduces to the two big positive
side cards, and each of those is now a drop-set question of card one or two. -/
theorem tieFreeMassGappedStress_ten_four_of_middleFormDrop
    (hdrop : MiddleFormDrop 10 4) : TieFreeMassGappedStress 10 4 :=
  tieFreeMassGappedStress_of_middleFormDrop hdrop

/-! ## Part 7: the re-assembly of both hinge obligations

The arm list has moved twice since the threshold-cell map was written.  The
deepest arm carries a tie and a primitive design (`Gtz.TieFreeMassGappedStress`,
the mass-gap module), and the degenerate arm costs one residual and no
predecessor rank (`Gtz.DegenerateHyperplaneCover`, the degenerate hinge module).
The two registry obligations on that joined list follow. -/

/-- **THE DECIDING CELL OBLIGATION, ON THE CURRENT LIST.**  This is the statement
of `Skeleton.obligationThresholdCellHingeRankFourAndUp` verbatim, on five
residuals: the stress-free arm, the recut mass-gap arm, the selection, the
partial-support arm and the hyperplane cover.  No predecessor cell of either
kind enters. -/
theorem thresholdCellHingeRankFourAndUp_of_currentList
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (htieFree : ∀ rank : ℕ, 4 ≤ rank → TieFreeMassGappedStress (thresholdSize rank) rank)
    (hselection : ∀ rank : ℕ, 4 ≤ rank →
      BalancedStratumSelectionAtRank (thresholdSize rank) rank)
    (hpartialArm : ∀ rank : ℕ, 4 ≤ rank →
      BalancedPartialSupportArmAt (thresholdSize rank) rank)
    (hcover : ∀ rank : ℕ, 4 ≤ rank → DegenerateHyperplaneCover (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  refine thresholdCellHingeRankFourAndUp_of_arms hfreeArm (fun rank hrank => ?_)
    (fun rank hrank => thresholdDegenerateArm_of_cover rank (hcover rank hrank))
  exact balancedArmAt_of_tieFreeResiduals (htieFree rank hrank) (hselection rank hrank)
    (hpartialArm rank hrank)

/-- **THE SUB-THRESHOLD BAND OBLIGATION, ON THE CURRENT LIST.**  This is the
statement of `Skeleton.obligationSubThresholdBandHinge` verbatim. -/
theorem subThresholdBandHinge_of_currentList
    (hfreeArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → StressFreeArmAt size rank)
    (htieFree : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → TieFreeMassGappedStress size rank)
    (hselection : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → BalancedStratumSelectionAtRank size rank)
    (hpartialArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → BalancedPartialSupportArmAt size rank)
    (hcover : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size < thresholdSize rank → DegenerateHyperplaneCover size rank) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design :=
  subThresholdBandHinge_of_arms hfreeArm
    (fun rank size hrank hlow hhigh =>
      balancedArmAt_of_tieFreeResiduals (htieFree rank size hrank hlow hhigh)
        (hselection rank size hrank hlow hhigh) (hpartialArm rank size hrank hlow hhigh))
    fun rank size hrank hlow hhigh =>
      degenerateArmAt_of_hyperplaneCover (hcover rank size hrank hlow hhigh)

/-- **THE WHOLE SHARP WINDOW ON THE CURRENT LIST.**  Both registry obligations
are the two ends of this window. -/
theorem sharpWindowHinge_of_currentList
    (hfreeArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → StressFreeArmAt size rank)
    (htieFree : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → TieFreeMassGappedStress size rank)
    (hselection : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → BalancedStratumSelectionAtRank size rank)
    (hpartialArm : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → BalancedPartialSupportArmAt size rank)
    (hcover : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size →
      size ≤ thresholdSize rank → DegenerateHyperplaneCover size rank) :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank :=
  sharpWindowHinge_of_arms hfreeArm
    (fun rank size hrank hlow hhigh =>
      balancedArmAt_of_tieFreeResiduals (htieFree rank size hrank hlow hhigh)
        (hselection rank size hrank hlow hhigh) (hpartialArm rank size hrank hlow hhigh))
    fun rank size hrank hlow hhigh =>
      degenerateArmAt_of_hyperplaneCover (hcover rank size hrank hlow hhigh)

/-- **THE DECIDING CELL AT RANK THREE, ON THE CURRENT LIST.**  Weighted GTZ at
`(6,3)` from the stress-free arm and the hyperplane cover alone: the recut
mass-gap arm and the selection are closed at rank three, and the partial-support
sub-arm is empty there. -/
theorem gtzWeighted_six_three_of_currentList (hfreeArm : ThresholdStressFreeArm 3)
    (hcover : DegenerateHyperplaneCover 6 3) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_tieFreeResiduals hfreeArm
    (thresholdDegenerateArm_of_cover 3 hcover)

/-! ## Part 8: the frame layer, and the gift to the atom-ceiling program

Nothing in Part 3 reads `weight_sum_one`.  The stage law needs only the frame
law `Sum_c scale_c * atomMatrix (atom c) = 1`, thus it holds verbatim for a
family whose scales add up to anything at all.  That is exactly the shape the
atom-energy ceiling works in: atoms `a_y` with `Sum_y a_y a_yᵀ = 1`, scales
`s_y` with `sigma := Sum_y s_y < 1`, and the dominating family `a_y / sqrt s_y`.
This part states the laws in that shape, so the two programs share one object.

The headline of this part: **at a frame whose total scale is less than one, the
FULL slot set always spares a slot**, at every rank and every slot count above
the rank.  No cap on the largest scale, no spectral hypothesis. -/

/-- The gap of a subset of a bare atom family. -/
noncomputable def frameGap {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (base : Finset (Fin atomCount)) : Matrix (Fin rank) (Fin rank) ℝ :=
  (∑ c ∈ base, atomMatrix (atomFamily c)) - 1

/-- The pivot value of a bare atom family.  Every label has one, inside the base
or outside it. -/
noncomputable def framePivot {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (base : Finset (Fin atomCount)) (label : Fin atomCount) : ℝ :=
  Matrix.trace ((frameGap atomFamily base)⁻¹ * atomMatrix (atomFamily label))

/-- The frame gap of a design is the design gap. -/
theorem frameGap_design (design : WeightedDesign size rank) (base : Finset (Fin size)) :
    frameGap design.atom base = subsetSum design base - 1 := rfl

/-- The frame pivot of a design is the design pivot. -/
theorem framePivot_design (design : WeightedDesign size rank) (base : Finset (Fin size))
    (label : Fin size) : framePivot design.atom base label = pivot design base label := rfl

/-- The frame pivot is the inverse form of the atom. -/
theorem framePivot_eq_inverseForm {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (base : Finset (Fin atomCount)) (label : Fin atomCount) :
    framePivot atomFamily base label
      = atomFamily label ⬝ᵥ ((frameGap atomFamily base)⁻¹ *ᵥ atomFamily label) :=
  trace_mul_atomMatrix _ _

/-- The frame pivot against a strictly dominating base is nonnegative. -/
theorem framePivot_nonneg {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    {base : Finset (Fin atomCount)} (hposDef : (frameGap atomFamily base).PosDef)
    (label : Fin atomCount) : 0 ≤ framePivot atomFamily base label := by
  rw [framePivot_eq_inverseForm]
  exact inverseForm_nonneg hposDef _

/-- **THE PIVOT BUDGET AT A BARE FAMILY.**  The pivot values of a strictly
dominating slot set add up to the rank plus the inverse gap trace. -/
theorem frame_sum_pivot_eq_rank_add_trace_inv {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (base : Finset (Fin atomCount))
    (hposDef : (frameGap atomFamily base).PosDef) :
    ∑ c ∈ base, framePivot atomFamily base c
      = (rank : ℝ) + Matrix.trace ((frameGap atomFamily base)⁻¹) := by
  classical
  have hunit : IsUnit (frameGap atomFamily base).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hsum : ∑ c ∈ base, framePivot atomFamily base c
      = Matrix.trace ((frameGap atomFamily base)⁻¹ * ∑ c ∈ base, atomMatrix (atomFamily c)) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have hsplit : ∑ c ∈ base, atomMatrix (atomFamily c) = frameGap atomFamily base + 1 := by
    rw [frameGap]; abel
  rw [hsum, hsplit, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add,
    Matrix.nonsing_inv_mul _ hunit, Matrix.trace_one, Fintype.card_fin]

/-- **THE FRAME LAW, CONTRACTED AT A BARE FAMILY.**  With a resolution of the
identity in hand, the scale-averaged pivot values of ALL slots against ANY base
equal the trace of that base's inverse gap.  No hypothesis on the total scale
and none on the base. -/
theorem frame_sum_scale_pivot_eq_trace_inv {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1)
    (base : Finset (Fin atomCount)) :
    ∑ c, scale c * framePivot atomFamily base c
      = Matrix.trace ((frameGap atomFamily base)⁻¹) := by
  classical
  have hterm : ∀ c : Fin atomCount, scale c * framePivot atomFamily base c
      = Matrix.trace ((frameGap atomFamily base)⁻¹ * (scale c • atomMatrix (atomFamily c))) := by
    intro c
    simp only [framePivot, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Matrix.trace_sum, ← Matrix.mul_sum, hframe,
    Matrix.mul_one]

/-- **THE STAGE LAW AT A BARE FAMILY.**  At every base the free-scale-averaged
pivot values of the base equal the rank plus the leak of the slots outside it.
This is the monotone replacement the bare pigeonhole lacks: the criterion holds
at every stage of a descent and not only at the full slot set. -/
theorem frame_stage_law {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (scale : Fin atomCount → ℝ) (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1)
    (base : Finset (Fin atomCount)) (hposDef : (frameGap atomFamily base).PosDef) :
    ∑ c ∈ base, (1 - scale c) * framePivot atomFamily base c
      = (rank : ℝ) + ∑ c ∈ baseᶜ, scale c * framePivot atomFamily base c := by
  classical
  have hall : ∑ c ∈ base, scale c * framePivot atomFamily base c
      + ∑ c ∈ baseᶜ, scale c * framePivot atomFamily base c
      = Matrix.trace ((frameGap atomFamily base)⁻¹) := by
    rw [Finset.sum_add_sum_compl]
    exact frame_sum_scale_pivot_eq_trace_inv atomFamily scale hframe base
  have hbudget := frame_sum_pivot_eq_rank_add_trace_inv atomFamily base hposDef
  have hsplit : ∑ c ∈ base, (1 - scale c) * framePivot atomFamily base c
      = ∑ c ∈ base, framePivot atomFamily base c
        - ∑ c ∈ base, scale c * framePivot atomFamily base c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hbudget]
  linarith

/-- **THE STAGE LAW READ AS A DROP, AT A BARE FAMILY.** -/
theorem frame_exists_pivot_lt_one_of_leak {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) {base : Finset (Fin atomCount)}
    (hposDef : (frameGap atomFamily base).PosDef) (hscale : ∀ c, scale c ≤ 1)
    (hleak : ∑ c ∈ baseᶜ, scale c * framePivot atomFamily base c
      < ∑ c ∈ base, (1 - scale c) - rank) :
    ∃ label ∈ base, framePivot atomFamily base label < 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hlower : ∑ c ∈ base, (1 - scale c)
      ≤ ∑ c ∈ base, (1 - scale c) * framePivot atomFamily base c := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hfree : 0 ≤ 1 - scale c := by linarith [hscale c]
    nlinarith [hnone c hc, hfree]
  rw [frame_stage_law atomFamily scale hframe base hposDef] at hlower
  linarith

/-- **THE FULL SLOT SET ALWAYS SPARES A SLOT.**  At a frame whose total scale is
strictly less than the excess of the slot count over the rank, the full slot set
carries a slot the domination can spare.  With `Sum_c scale_c < 1` and more than
`rank` slots the hypothesis is automatic.

This is the design-free form of `Gtz.exists_pivot_lt_one_univ`, and it is the
first drop of the atom-ceiling descent, free at EVERY total scale below one. -/
theorem frame_exists_pivot_lt_one_univ {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1)
    (hposDef : (frameGap atomFamily Finset.univ).PosDef) (hscale : ∀ c, scale c ≤ 1)
    (hsmall : (rank : ℝ) + ∑ c, scale c < atomCount) :
    ∃ label, framePivot atomFamily Finset.univ label < 1 := by
  classical
  have hsum : ∑ c ∈ (Finset.univ : Finset (Fin atomCount)), (1 - scale c)
      = (atomCount : ℝ) - ∑ c, scale c := by
    rw [Finset.sum_sub_distrib]
    simp
  have hleak : ∑ c ∈ (Finset.univ : Finset (Fin atomCount))ᶜ,
      scale c * framePivot atomFamily Finset.univ c
      < ∑ c ∈ (Finset.univ : Finset (Fin atomCount)), (1 - scale c) - rank := by
    rw [Finset.compl_univ, Finset.sum_empty, hsum]
    linarith
  obtain ⟨label, -, hlabel⟩ :=
    frame_exists_pivot_lt_one_of_leak atomFamily scale hframe hposDef hscale hleak
  exact ⟨label, hlabel⟩

/-- **THE ATOM-CEILING READING.**  A frame of more than `rank` slots whose scales
are positive and add up to less than one spares a slot of its full set.  This is
the exact hypothesis package of the atom-energy ceiling, and the conclusion is
the first step of its descent. -/
theorem frame_exists_pivot_lt_one_of_totalScale_lt_one {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1)
    (hposDef : (frameGap atomFamily Finset.univ).PosDef) (hpos : ∀ c, 0 < scale c)
    (htotal : ∑ c, scale c < 1) (hbig : rank + 1 ≤ atomCount) :
    ∃ label, framePivot atomFamily Finset.univ label < 1 := by
  classical
  have hscale : ∀ c, scale c ≤ 1 := by
    intro c
    have hsingle : scale c ≤ ∑ d, scale d :=
      Finset.single_le_sum (fun d _ => (hpos d).le) (Finset.mem_univ c)
    linarith
  refine frame_exists_pivot_lt_one_univ atomFamily scale hframe hposDef hscale ?_
  have hcast : (rank : ℝ) + 1 ≤ (atomCount : ℝ) := by exact_mod_cast hbig
  linarith

/-! ### The block drop at a bare family -/

/-- The gap of a bare family is symmetric. -/
theorem transpose_frameGap {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (base : Finset (Fin atomCount)) :
    (frameGap atomFamily base)ᵀ = frameGap atomFamily base := by
  rw [frameGap, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_sum]
  refine congrArg (fun mat => mat - (1 : Matrix (Fin rank) (Fin rank) ℝ)) ?_
  exact Finset.sum_congr rfl fun c _ =>
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (atomFamily c)).1

/-- **THE BLOCK DROP IS A LOEWNER STEP, AT A BARE FAMILY.** -/
theorem frame_gap_form_sdiff_ge_of_pivotSum {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) {base dropped : Finset (Fin atomCount)}
    (hsub : dropped ⊆ base) (hposDef : (frameGap atomFamily base).PosDef)
    (probe : Fin rank → ℝ) :
    (1 - ∑ c ∈ dropped, framePivot atomFamily base c)
        * (probe ⬝ᵥ (frameGap atomFamily base *ᵥ probe))
      ≤ probe ⬝ᵥ (frameGap atomFamily (base \ dropped) *ᵥ probe) := by
  classical
  have hsplit : (∑ c ∈ base \ dropped, atomMatrix (atomFamily c))
      + ∑ c ∈ dropped, atomMatrix (atomFamily c)
      = ∑ c ∈ base, atomMatrix (atomFamily c) := Finset.sum_sdiff hsub
  have hmatrix : frameGap atomFamily (base \ dropped)
      = frameGap atomFamily base - ∑ c ∈ dropped, atomMatrix (atomFamily c) := by
    rw [frameGap, frameGap, ← hsplit]; abel
  have hcap : ∀ c ∈ dropped,
      (atomFamily c ⬝ᵥ probe) ^ 2
        ≤ framePivot atomFamily base c * (probe ⬝ᵥ (frameGap atomFamily base *ᵥ probe)) := by
    intro c _
    rw [framePivot_eq_inverseForm]
    exact dotProduct_sq_le_inverseForm_mul_form hposDef (atomFamily c) probe
  have hsum : ∑ c ∈ dropped, (atomFamily c ⬝ᵥ probe) ^ 2
      ≤ (∑ c ∈ dropped, framePivot atomFamily base c)
        * (probe ⬝ᵥ (frameGap atomFamily base *ᵥ probe)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hcap
  have hform : probe ⬝ᵥ (frameGap atomFamily (base \ dropped) *ᵥ probe)
      = probe ⬝ᵥ (frameGap atomFamily base *ᵥ probe)
        - ∑ c ∈ dropped, (atomFamily c ⬝ᵥ probe) ^ 2 := by
    rw [hmatrix, Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum]
    refine congrArg (fun value => probe ⬝ᵥ (frameGap atomFamily base *ᵥ probe) - value) ?_
    exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq (atomFamily c) probe
  rw [hform]
  linarith

/-- **THE BLOCK DROP, AT A BARE FAMILY.** -/
theorem frame_posDef_sdiff_of_pivotSum_lt_one {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) {base dropped : Finset (Fin atomCount)}
    (hsub : dropped ⊆ base) (hposDef : (frameGap atomFamily base).PosDef)
    (hsum : ∑ c ∈ dropped, framePivot atomFamily base c < 1) :
    (frameGap atomFamily (base \ dropped)).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_frameGap atomFamily (base \ dropped)),
      fun probe hprobe => ?_⟩
  have hbase : 0 < probe ⬝ᵥ (frameGap atomFamily base *ᵥ probe) := by
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rwa [star_trivial] at hstep
  have hstep := frame_gap_form_sdiff_ge_of_pivotSum atomFamily hsub hposDef probe
  rw [star_trivial]
  nlinarith [hstep, hbase, hsum]

/-- **THE PRICE OF A STAGE, AT A BARE FAMILY.**  After a block drop the pivot
values grow by at most the inverted slack of the dropped mass.  With the stage
law this bounds the leak of the next stage, and the descent continues. -/
theorem frame_pivot_sdiff_le_of_pivotSum {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) {base dropped : Finset (Fin atomCount)}
    (hsub : dropped ⊆ base) (hposDef : (frameGap atomFamily base).PosDef)
    (hsum : ∑ c ∈ dropped, framePivot atomFamily base c < 1) (label : Fin atomCount) :
    framePivot atomFamily (base \ dropped) label
      ≤ (1 - ∑ c ∈ dropped, framePivot atomFamily base c)⁻¹
        * framePivot atomFamily base label := by
  classical
  have hslack : 0 < 1 - ∑ c ∈ dropped, framePivot atomFamily base c := by linarith
  have hsmall : (frameGap atomFamily (base \ dropped)).PosDef :=
    frame_posDef_sdiff_of_pivotSum_lt_one atomFamily hsub hposDef hsum
  have hbound := inverseForm_le_of_form_le_smul hsmall hposDef hslack
    (fun probe => frame_gap_form_sdiff_ge_of_pivotSum atomFamily hsub hposDef probe)
    (atomFamily label)
  rw [framePivot_eq_inverseForm, framePivot_eq_inverseForm]
  exact hbound

/-- **THE DESCENT CONTINUES, AT A BARE FAMILY.**  A dropped set whose every
member stays under the slack of the dropped mass leaves a base that still spares
a slot, provided the base carries more than the rank in free scale. -/
theorem frame_exists_pivot_lt_one_of_dropBudget {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) (hpos : ∀ c, 0 < scale c)
    (htotal : ∑ c, scale c < 1)
    (hposDef : (frameGap atomFamily Finset.univ).PosDef)
    {dropped : Finset (Fin atomCount)} (hne : dropped.Nonempty)
    (hbudget : ∀ c ∈ dropped, framePivot atomFamily Finset.univ c
      < 1 - ∑ d ∈ dropped, framePivot atomFamily Finset.univ d)
    (hcard : rank + 1 ≤ (Finset.univ \ dropped).card) :
    ∃ label ∈ Finset.univ \ dropped,
      framePivot atomFamily (Finset.univ \ dropped) label < 1 := by
  classical
  set base := (Finset.univ : Finset (Fin atomCount)) \ dropped with hbase
  obtain ⟨witness, hwitness⟩ := hne
  have hscale : ∀ c, scale c ≤ 1 := by
    intro c
    have hsingle : scale c ≤ ∑ d, scale d :=
      Finset.single_le_sum (fun d _ => (hpos d).le) (Finset.mem_univ c)
    linarith
  have hmass : ∑ d ∈ dropped, framePivot atomFamily Finset.univ d < 1 := by
    have hstep := hbudget witness hwitness
    have hnonneg := framePivot_nonneg atomFamily hposDef witness
    linarith
  have hslack : 0 < 1 - ∑ d ∈ dropped, framePivot atomFamily Finset.univ d := by linarith
  have hbasePosDef : (frameGap atomFamily base).PosDef :=
    frame_posDef_sdiff_of_pivotSum_lt_one atomFamily (Finset.subset_univ dropped) hposDef hmass
  have houtside : ∀ c ∈ dropped, framePivot atomFamily base c < 1 := by
    intro c hc
    have hstep := frame_pivot_sdiff_le_of_pivotSum atomFamily (Finset.subset_univ dropped)
      hposDef hmass c
    have hscaled : (1 - ∑ d ∈ dropped, framePivot atomFamily Finset.univ d)⁻¹
        * framePivot atomFamily Finset.univ c < 1 := by
      rw [inv_mul_lt_iff₀ hslack, mul_one]
      exact hbudget c hc
    exact lt_of_le_of_lt hstep hscaled
  have hcompl : baseᶜ = dropped := by
    rw [hbase]; ext c; simp
  have hleak : ∑ c ∈ baseᶜ, scale c * framePivot atomFamily base c
      < ∑ c ∈ base, (1 - scale c) - rank := by
    have hstrict : ∑ c ∈ baseᶜ, scale c * framePivot atomFamily base c
        < ∑ c ∈ baseᶜ, scale c := by
      rw [hcompl]
      refine Finset.sum_lt_sum_of_nonempty ⟨witness, hwitness⟩ fun c hc => ?_
      nlinarith [houtside c hc, hpos c]
    have hcapScale : ∑ c ∈ baseᶜ, scale c ≤ ∑ c, scale c := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
      exact fun c _ _ => (hpos c).le
    have hfree : ∑ c ∈ base, (1 - scale c)
        = (base.card : ℝ) - ∑ c ∈ base, scale c := by
      rw [Finset.sum_sub_distrib]; simp
    have hsplitScale : ∑ c ∈ base, scale c + ∑ c ∈ baseᶜ, scale c = ∑ c, scale c :=
      Finset.sum_add_sum_compl base scale
    have hcardBound : (rank : ℝ) + 1 ≤ (base.card : ℝ) := by exact_mod_cast hcard
    linarith
  exact frame_exists_pivot_lt_one_of_leak atomFamily scale hframe hbasePosDef hscale hleak

/-! ## Part 9: the exact pivot update, and two free drops

The Loewner price of a stage is an inequality.  At a single dropped label it is
an EQUALITY, and the equality is elementary: the dual vector of the smaller gap
is an eigenvector of the rank-one update.  With it the second drop of a design is
free at every cell whose size is at least `2 * rank + 1`, and the deciding cell
of rank four and up is such a cell. -/

/-- **THE EXACT RANK-ONE PIVOT UPDATE.**  Adding one atom to a positive definite
matrix divides that atom's inverse form by one plus itself.  The proof solves one
linear system and never inverts a sum. -/
theorem inverseForm_add_atomMatrix {baseMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hposDef : baseMat.PosDef) (source : Fin rank → ℝ) :
    (source ⬝ᵥ ((baseMat + atomMatrix source)⁻¹ *ᵥ source))
        * (1 + source ⬝ᵥ (baseMat⁻¹ *ᵥ source))
      = source ⬝ᵥ (baseMat⁻¹ *ᵥ source) := by
  have hunit : IsUnit baseMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hbigSymm : (baseMat + atomMatrix source)ᵀ = baseMat + atomMatrix source := by
    rw [Matrix.transpose_add, PosDef.transpose_eq hposDef,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix source).1]
  have hbig : (baseMat + atomMatrix source).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hbigSymm, fun probe hprobe => ?_⟩
    have hbase := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rw [star_trivial] at hbase ⊢
    rw [Matrix.add_mulVec, dotProduct_add, atom_form_eq_sq]
    nlinarith [hbase, sq_nonneg (source ⬝ᵥ probe)]
  have hbigUnit : IsUnit (baseMat + atomMatrix source).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hbig.det_pos)
  set dual : Fin rank → ℝ := baseMat⁻¹ *ᵥ source with hdual
  have hmulDual : baseMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv baseMat hunit, Matrix.one_mulVec]
  have hatom : atomMatrix source *ᵥ dual = (source ⬝ᵥ dual) • source := by
    rw [atomMatrix, vecMulVec_mulVec_eq]
  have hbigMul : (baseMat + atomMatrix source) *ᵥ dual = (1 + source ⬝ᵥ dual) • source := by
    rw [Matrix.add_mulVec, hmulDual, hatom, add_smul, one_smul]
  have hstep : (baseMat + atomMatrix source)⁻¹ *ᵥ ((baseMat + atomMatrix source) *ᵥ dual)
      = dual := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hbigUnit, Matrix.one_mulVec]
  have hsolve : (1 + source ⬝ᵥ dual) • ((baseMat + atomMatrix source)⁻¹ *ᵥ source) = dual := by
    rw [← Matrix.mulVec_smul, ← hbigMul, hstep]
  have hpair : source ⬝ᵥ ((1 + source ⬝ᵥ dual)
      • ((baseMat + atomMatrix source)⁻¹ *ᵥ source)) = source ⬝ᵥ dual := by rw [hsolve]
  rw [dotProduct_smul, smul_eq_mul] at hpair
  rw [mul_comm]
  exact hpair

/-- **THE EXACT PIVOT UPDATE OF ONE ERASED LABEL.**  Against the smaller base the
erased label's pivot value is its old value divided by the old slack. -/
theorem framePivot_erase_eq {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    {base : Finset (Fin atomCount)} {label : Fin atomCount} (hmem : label ∈ base)
    (hposDef : (frameGap atomFamily (base.erase label)).PosDef) :
    framePivot atomFamily base label
        * (1 + framePivot atomFamily (base.erase label) label)
      = framePivot atomFamily (base.erase label) label := by
  classical
  have hsum : (∑ c ∈ base.erase label, atomMatrix (atomFamily c)) + atomMatrix (atomFamily label)
      = ∑ c ∈ base, atomMatrix (atomFamily c) :=
    Finset.sum_erase_add base _ hmem
  have hgap : frameGap atomFamily (base.erase label) + atomMatrix (atomFamily label)
      = frameGap atomFamily base := by
    rw [frameGap, frameGap, ← hsum]; abel
  have hstep := inverseForm_add_atomMatrix hposDef (atomFamily label)
  rw [hgap] at hstep
  rw [framePivot_eq_inverseForm, framePivot_eq_inverseForm]
  exact hstep

/-- **THE ERASED PIVOT AT A HALF-SPENT LABEL.**  A label whose pivot value is at
most one half has pivot value at most one against the erased base. -/
theorem framePivot_erase_le_one {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    {base : Finset (Fin atomCount)} {label : Fin atomCount} (hmem : label ∈ base)
    (hposDef : (frameGap atomFamily base).PosDef)
    (hhalf : framePivot atomFamily base label ≤ 1 / 2) :
    framePivot atomFamily (base.erase label) label ≤ 1 := by
  classical
  have herase : base.erase label = base \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsub : ({label} : Finset (Fin atomCount)) ⊆ base := by
    simpa using hmem
  have hsingle : ∑ c ∈ ({label} : Finset (Fin atomCount)), framePivot atomFamily base c
      = framePivot atomFamily base label := by simp
  have hsmall : ∑ c ∈ ({label} : Finset (Fin atomCount)), framePivot atomFamily base c < 1 := by
    rw [hsingle]; linarith
  have hsmallPosDef : (frameGap atomFamily (base.erase label)).PosDef := by
    rw [herase]
    exact frame_posDef_sdiff_of_pivotSum_lt_one atomFamily hsub hposDef hsmall
  have hexact := framePivot_erase_eq atomFamily hmem hsmallPosDef
  have hnonneg := framePivot_nonneg atomFamily hsmallPosDef label
  nlinarith [hexact, hnonneg, hhalf]

/-- **THE SECOND DROP IS FREE.**  After erasing a label whose pivot value is at
most one half, a design of size beyond `rank + 2` still spares a label.  The leak
of the stage law is one term, and the exact pivot update caps it. -/
theorem exists_pivot_lt_one_erase (design : WeightedDesign size rank) (htwo : 2 ≤ size)
    (hbig : rank + 2 < size) {label : Fin size}
    (hhalf : pivot design Finset.univ label ≤ 1 / 2) :
    ∃ second ∈ Finset.univ.erase label,
      pivot design (Finset.univ.erase label) second < 1 := by
  classical
  have hunivPosDef := posDef_gap_univ design htwo
  have hframeUniv : (frameGap design.atom Finset.univ).PosDef := hunivPosDef
  have herased : framePivot design.atom (Finset.univ.erase label) label ≤ 1 :=
    framePivot_erase_le_one design.atom (Finset.mem_univ label) hframeUniv hhalf
  have herase : (Finset.univ : Finset (Fin size)).erase label = Finset.univ \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsub : ({label} : Finset (Fin size)) ⊆ Finset.univ := Finset.subset_univ _
  have hsmall : ∑ c ∈ ({label} : Finset (Fin size)), pivot design Finset.univ c < 1 := by
    simp only [Finset.sum_singleton]
    linarith
  have hbasePosDef : (subsetSum design (Finset.univ.erase label) - 1).PosDef := by
    rw [herase]
    exact posDef_sdiff_of_pivotSum_lt_one design hsub hunivPosDef hsmall
  have hcompl : ((Finset.univ : Finset (Fin size)).erase label)ᶜ = {label} := by
    ext c; simp
  have hcard : ((Finset.univ : Finset (Fin size)).erase label).card = size - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ, Fintype.card_fin]
  have hfree : ∑ c ∈ (Finset.univ : Finset (Fin size)).erase label, (1 - design.weight c)
      = ((size : ℝ) - 1) - (1 - design.weight label) := by
    have hsplit : design.weight label
        + ∑ c ∈ Finset.univ.erase label, design.weight c = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ label)]
      exact design.weight_sum_one
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    have hcast : ((size - 1 : ℕ) : ℝ) = (size : ℝ) - 1 := by
      have : 1 ≤ size := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
    linarith
  have hleak : ∑ c ∈ ((Finset.univ : Finset (Fin size)).erase label)ᶜ,
      design.weight c * pivot design (Finset.univ.erase label) c
      < ∑ c ∈ (Finset.univ : Finset (Fin size)).erase label, (1 - design.weight c) - rank := by
    rw [hcompl, Finset.sum_singleton, hfree]
    have hweight := design.weight_pos label
    have hcast : (rank : ℝ) + 2 < (size : ℝ) := by exact_mod_cast hbig
    have hbound : design.weight label * pivot design (Finset.univ.erase label) label
        ≤ design.weight label := by
      have hpivotErase : pivot design (Finset.univ.erase label) label ≤ 1 := herased
      nlinarith [hpivotErase, hweight]
    linarith
  exact exists_pivot_lt_one_of_leak design hbasePosDef hleak

/-- **TWO FREE DROPS.**  A design whose size is at least `2 * rank + 1` and beyond
`rank + 2` carries a strictly dominating subset of card `size - 2`, with no
weight hypothesis and no stress.  The deciding cell of every rank four and up is
such a cell, because `2 * rank + 1 <= rank * (rank + 1) / 2` there. -/
theorem exists_two_erase_posDef (design : WeightedDesign size rank) (hbig : rank + 2 < size)
    (hhalf : 2 * rank + 1 ≤ size) :
    ∃ selected : Finset (Fin size), selected.card = size - 2
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  have htwo : 2 ≤ size := by omega
  obtain ⟨label, hlabel⟩ := exists_pivot_univ_le_mediant design htwo
  have hsizeCast : (2 : ℝ) * rank + 1 ≤ (size : ℝ) := by exact_mod_cast hhalf
  have hsizeTwo : (2 : ℝ) ≤ (size : ℝ) := by exact_mod_cast htwo
  have hpivotHalf : pivot design Finset.univ label ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < (size : ℝ) - 1 := by linarith
    nlinarith [hlabel, hpos, pivot_nonneg design Finset.univ (posDef_gap_univ design htwo) label]
  obtain ⟨second, hsecondMem, hsecond⟩ := exists_pivot_lt_one_erase design htwo hbig hpivotHalf
  have hunivPosDef := posDef_gap_univ design htwo
  have herase : (Finset.univ : Finset (Fin size)).erase label = Finset.univ \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsmall : ∑ c ∈ ({label} : Finset (Fin size)), pivot design Finset.univ c < 1 := by
    simp only [Finset.sum_singleton]
    linarith
  have hbasePosDef : (subsetSum design (Finset.univ.erase label) - 1).PosDef := by
    rw [herase]
    exact posDef_sdiff_of_pivotSum_lt_one design (Finset.subset_univ _) hunivPosDef hsmall
  refine ⟨((Finset.univ : Finset (Fin size)).erase label).erase second, ?_,
    posDef_erase_of_pivot_lt_one design hsecondMem hbasePosDef hsecond⟩
  rw [Finset.card_erase_of_mem hsecondMem,
    Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ, Fintype.card_fin]
  omega

/-- The deciding cell of rank four and up admits two free drops: the arithmetic
side condition holds there. -/
theorem thresholdSize_two_mul_le (rank : ℕ) (hrank : 4 ≤ rank) :
    2 * rank + 1 ≤ thresholdSize rank := by
  obtain ⟨shift, hshift⟩ : ∃ shift, rank = shift + 4 := ⟨rank - 4, by omega⟩
  subst hshift
  have hdouble := two_mul_thresholdSize (shift + 4)
  have hexpand : (shift + 4) * (shift + 4 + 1) = shift * shift + 9 * shift + 20 := by ring
  rw [hexpand] at hdouble
  omega


/-! ## Part 10: the frame layer with no domination hypothesis

The frame law alone makes the full slot set dominate strictly, thus every
statement of Part 8 loses its positive definiteness hypothesis.  What is left is
a closed package: a family of atoms resolving the identity with scales below
one, and the descent that package supports. -/

/-- **A FRAME SPANS.**  A family resolving the identity has no common orthogonal
direction. -/
theorem frame_atoms_span {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (scale : Fin atomCount → ℝ) (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1)
    {probe : Fin rank → ℝ} (horth : ∀ c, atomFamily c ⬝ᵥ probe = 0) : probe = 0 := by
  classical
  by_contra hne
  have hpos : 0 < probe ⬝ᵥ probe := selfDotProduct_pos hne
  have hform : probe ⬝ᵥ probe = ∑ c, scale c * (atomFamily c ⬝ᵥ probe) ^ 2 := by
    rw [← weighted_atomForm_eq_on Finset.univ scale atomFamily probe, hframe, Matrix.one_mulVec]
  rw [hform, Finset.sum_eq_zero fun c _ => by rw [horth c]; ring] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **THE FULL SLOT SET OF A FRAME DOMINATES STRICTLY.**  With every scale below
one the gap of the full slot set is the free-scale matrix, which is positive
definite because the frame spans.  No total-scale hypothesis is needed beyond
the pointwise one. -/
theorem frame_posDef_gap_univ {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (scale : Fin atomCount → ℝ) (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1)
    (hlt : ∀ c, scale c < 1) : (frameGap atomFamily Finset.univ).PosDef := by
  classical
  have hmatrix : frameGap atomFamily Finset.univ
      = ∑ c, (1 - scale c) • atomMatrix (atomFamily c) := by
    have hsplit : ∑ c, (1 - scale c) • atomMatrix (atomFamily c)
        = (∑ c, atomMatrix (atomFamily c)) - ∑ c, scale c • atomMatrix (atomFamily c) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
    rw [hsplit, hframe, frameGap]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_frameGap atomFamily Finset.univ),
      fun probe hprobe => ?_⟩
  rw [star_trivial, hmatrix, weighted_atomForm_eq_on]
  obtain ⟨badLabel, hbad⟩ : ∃ c, atomFamily c ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hprobe (frame_atoms_span atomFamily scale hframe hall)
  refine Finset.sum_pos' (fun c _ => ?_) ⟨badLabel, Finset.mem_univ badLabel, ?_⟩
  · exact mul_nonneg (by linarith [hlt c]) (sq_nonneg _)
  · exact mul_pos (by linarith [hlt badLabel]) (by positivity)

/-- **THE FIRST DROP OF A SUB-UNIT FRAME, WITH NO HYPOTHESIS BEYOND THE FRAME.**
A family of more than `rank` atoms resolving the identity with positive scales of
total less than one spares one of its atoms.  Compare the bare pigeonhole, whose
firing needs the total scale below `(size - rank) / size`: this criterion holds
at EVERY total scale below one. -/
theorem frame_exists_drop_of_subUnit {atomCount : ℕ} (atomFamily : Fin atomCount → Fin rank → ℝ)
    (scale : Fin atomCount → ℝ) (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1)
    (hpos : ∀ c, 0 < scale c) (htotal : ∑ c, scale c < 1) (hbig : rank + 1 ≤ atomCount) :
    ∃ label, framePivot atomFamily Finset.univ label < 1
      ∧ (frameGap atomFamily (Finset.univ.erase label)).PosDef := by
  classical
  have hlt : ∀ c, scale c < 1 := by
    intro c
    have hsingle : scale c ≤ ∑ d, scale d :=
      Finset.single_le_sum (fun d _ => (hpos d).le) (Finset.mem_univ c)
    linarith
  have hposDef := frame_posDef_gap_univ atomFamily scale hframe hlt
  obtain ⟨label, hlabel⟩ := frame_exists_pivot_lt_one_of_totalScale_lt_one atomFamily scale
    hframe hposDef hpos htotal hbig
  refine ⟨label, hlabel, ?_⟩
  have herase : (Finset.univ : Finset (Fin atomCount)).erase label = Finset.univ \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsmall : ∑ c ∈ ({label} : Finset (Fin atomCount)), framePivot atomFamily Finset.univ c
      < 1 := by
    simp only [Finset.sum_singleton]
    exact hlabel
  rw [herase]
  exact frame_posDef_sdiff_of_pivotSum_lt_one atomFamily (Finset.subset_univ _) hposDef hsmall

/-- **THE DEEPEST DROP OF A SUB-UNIT FRAME.**  A dropped set of card
`atomCount - rank - 1` whose members all stay under the slack of the dropped mass
carries the descent to a strictly dominating slot set of card exactly `rank`.

At `atomCount = 6` and `rank = 3` the conclusion is the atom triple ceiling, and
the hypothesis is a two-slot pivot budget against the FULL slot set. -/
theorem frame_exists_rankSized_of_dropBudget {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) (hpos : ∀ c, 0 < scale c)
    (htotal : ∑ c, scale c < 1) (hrank : rank + 2 ≤ atomCount)
    {dropped : Finset (Fin atomCount)} (hcard : dropped.card = atomCount - rank - 1)
    (hbudget : ∀ c ∈ dropped, framePivot atomFamily Finset.univ c
      < 1 - ∑ d ∈ dropped, framePivot atomFamily Finset.univ d) :
    ∃ selected : Finset (Fin atomCount), selected.card = rank
      ∧ (frameGap atomFamily selected).PosDef := by
  classical
  have hlt : ∀ c, scale c < 1 := by
    intro c
    have hsingle : scale c ≤ ∑ d, scale d :=
      Finset.single_le_sum (fun d _ => (hpos d).le) (Finset.mem_univ c)
    linarith
  have hposDef := frame_posDef_gap_univ atomFamily scale hframe hlt
  have hne : dropped.Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have hbaseCard : ((Finset.univ : Finset (Fin atomCount)) \ dropped).card = rank + 1 := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin, hcard]
    omega
  obtain ⟨label, hmem, hlabel⟩ := frame_exists_pivot_lt_one_of_dropBudget atomFamily scale
    hframe hpos htotal hposDef hne hbudget (by omega)
  obtain ⟨witness, hwitness⟩ := hne
  have hmass : ∑ d ∈ dropped, framePivot atomFamily Finset.univ d < 1 := by
    have hstep := hbudget witness hwitness
    have hnonneg := framePivot_nonneg atomFamily hposDef witness
    linarith
  have hbasePosDef :
      (frameGap atomFamily ((Finset.univ : Finset (Fin atomCount)) \ dropped)).PosDef :=
    frame_posDef_sdiff_of_pivotSum_lt_one atomFamily (Finset.subset_univ dropped) hposDef hmass
  have herase : ((Finset.univ : Finset (Fin atomCount)) \ dropped).erase label
      = ((Finset.univ : Finset (Fin atomCount)) \ dropped) \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsingletonSub : ({label} : Finset (Fin atomCount))
      ⊆ (Finset.univ : Finset (Fin atomCount)) \ dropped := by simpa using hmem
  have hsmall : ∑ c ∈ ({label} : Finset (Fin atomCount)),
      framePivot atomFamily ((Finset.univ : Finset (Fin atomCount)) \ dropped) c < 1 := by
    simp only [Finset.sum_singleton]
    exact hlabel
  refine ⟨(((Finset.univ : Finset (Fin atomCount)) \ dropped).erase label), ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hmem, hbaseCard]
    omega
  · rw [herase]
    exact frame_posDef_sdiff_of_pivotSum_lt_one atomFamily hsingletonSub hbasePosDef hsmall

/-! ## Part 11: two free drops at the deciding cell -/

/-- The deciding cell of rank four and up outgrows `rank + 2`. -/
theorem thresholdSize_gt_rank_add_two (rank : ℕ) (hrank : 4 ≤ rank) :
    rank + 2 < thresholdSize rank := by
  obtain ⟨shift, hshift⟩ : ∃ shift, rank = shift + 4 := ⟨rank - 4, by omega⟩
  subst hshift
  have hdouble := two_mul_thresholdSize (shift + 4)
  have hexpand : (shift + 4) * (shift + 4 + 1) = shift * shift + 9 * shift + 20 := by ring
  rw [hexpand] at hdouble
  omega

/-- **TWO FREE DROPS AT THE DECIDING CELL.**  Every design at the deciding cell of
a rank four or more carries a strictly dominating subset of card two below the
cell.  The tie of the hinge therefore never stalls in the first two stages, and
whatever obstructs it lives strictly deeper in the descent. -/
theorem exists_two_erase_posDef_thresholdCell (rank : ℕ) (hrank : 4 ≤ rank)
    (design : WeightedDesign (thresholdSize rank) rank) :
    ∃ selected : Finset (Fin (thresholdSize rank)),
      selected.card = thresholdSize rank - 2 ∧ (subsetSum design selected - 1).PosDef :=
  exists_two_erase_posDef design (thresholdSize_gt_rank_add_two rank hrank)
    (thresholdSize_two_mul_le rank hrank)

/-- The rank-four instance: every `(10,4)` design carries a strictly dominating
subset of card eight. -/
theorem exists_card_eight_posDef_ten_four (design : WeightedDesign 10 4) :
    ∃ selected : Finset (Fin 10), selected.card = 8
      ∧ (subsetSum design selected - 1).PosDef :=
  exists_two_erase_posDef design (by omega) (by omega)


/-! ## Part 12: the sharp second drop, and the whole sharp window

`Gtz.exists_pivot_lt_one_erase` asks the first pivot value to be at most one
half, which the mediant supplies only when the size reaches `2 * rank + 1`.  The
deciding cell of rank three misses that by one.  The leak of the stage law is a
SINGLE term, thus the exact pivot update prices it without any rounding, and the
sharp criterion reaches every cell of the sharp window at every rank three and
up -- the deciding cell of rank three included. -/

/-- **THE SECOND DROP, PRICED EXACTLY.**  The leak of the once-erased base is one
term.  When that term stays under the free excess, the base spares a label. -/
theorem exists_pivot_lt_one_erase_of_leak (design : WeightedDesign size rank)
    (htwo : 2 ≤ size) {label : Fin size} (hlabel : pivot design Finset.univ label < 1)
    (hleak : design.weight label * (pivot design (Finset.univ.erase label) label - 1)
      < (size : ℝ) - 2 - rank) :
    ∃ second ∈ Finset.univ.erase label,
      pivot design (Finset.univ.erase label) second < 1 := by
  classical
  have hunivPosDef := posDef_gap_univ design htwo
  have herase : (Finset.univ : Finset (Fin size)).erase label = Finset.univ \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsmall : ∑ c ∈ ({label} : Finset (Fin size)), pivot design Finset.univ c < 1 := by
    simp only [Finset.sum_singleton]
    exact hlabel
  have hbasePosDef : (subsetSum design (Finset.univ.erase label) - 1).PosDef := by
    rw [herase]
    exact posDef_sdiff_of_pivotSum_lt_one design (Finset.subset_univ _) hunivPosDef hsmall
  have hcompl : ((Finset.univ : Finset (Fin size)).erase label)ᶜ = {label} := by
    ext c; simp
  have hcard : ((Finset.univ : Finset (Fin size)).erase label).card = size - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ, Fintype.card_fin]
  have hfree : ∑ c ∈ (Finset.univ : Finset (Fin size)).erase label, (1 - design.weight c)
      = ((size : ℝ) - 1) - (1 - design.weight label) := by
    have hsplit : design.weight label
        + ∑ c ∈ Finset.univ.erase label, design.weight c = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ label)]
      exact design.weight_sum_one
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    have hcast : ((size - 1 : ℕ) : ℝ) = (size : ℝ) - 1 := by
      have hone : 1 ≤ size := by omega
      push_cast [Nat.cast_sub hone]
      ring
    rw [hcast]
    linarith
  refine exists_pivot_lt_one_of_leak design hbasePosDef ?_
  rw [hcompl, Finset.sum_singleton, hfree]
  linarith

/-- **THE SHARP SECOND DROP.**  With the arithmetic side condition
`2 * rank - (size - 1) < (size - 2 - rank) * (size - 1 - rank)` the second drop
of a design is free.  The condition holds at every cell of the sharp window at
every rank three and up, the deciding cell of rank three included, where the
crude half-pivot criterion fails by exactly one label. -/
theorem exists_two_erase_posDef_sharp (design : WeightedDesign size rank)
    (hbig : rank + 2 < size)
    (hsharp : 2 * (rank : ℝ) - ((size : ℝ) - 1)
      < ((size : ℝ) - 2 - rank) * ((size : ℝ) - 1 - rank)) :
    ∃ selected : Finset (Fin size), selected.card = size - 2
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  have htwo : 2 ≤ size := by omega
  have hcast : (rank : ℝ) + 2 < (size : ℝ) := by exact_mod_cast hbig
  have hunivPosDef := posDef_gap_univ design htwo
  obtain ⟨label, hlabel⟩ := exists_pivot_univ_le_mediant design htwo
  set first : ℝ := pivot design Finset.univ label with hfirst
  have hfirstNonneg : 0 ≤ first := pivot_nonneg design Finset.univ hunivPosDef label
  have hgapPos : (0 : ℝ) < (size : ℝ) - 1 - rank := by linarith
  have hfirstLt : first < 1 := by nlinarith [hlabel, hgapPos, hfirstNonneg]
  have herase : (Finset.univ : Finset (Fin size)).erase label = Finset.univ \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsingle : ∑ c ∈ ({label} : Finset (Fin size)), pivot design Finset.univ c < 1 := by
    simp only [Finset.sum_singleton]
    exact hfirstLt
  have hbasePosDef : (subsetSum design (Finset.univ.erase label) - 1).PosDef := by
    rw [herase]
    exact posDef_sdiff_of_pivotSum_lt_one design (Finset.subset_univ _) hunivPosDef hsingle
  have hframeErase : (frameGap design.atom (Finset.univ.erase label)).PosDef := hbasePosDef
  have hupdate : first * (1 + pivot design (Finset.univ.erase label) label)
      = pivot design (Finset.univ.erase label) label :=
    framePivot_erase_eq design.atom (Finset.mem_univ label) hframeErase
  set second : ℝ := pivot design (Finset.univ.erase label) label with hsecond
  have hweightPos := design.weight_pos label
  have hweightLe := weight_le_one design label
  have hslack : (0 : ℝ) < 1 - first := by linarith
  have hcross : design.weight label * (2 * first - 1)
      < ((size : ℝ) - 2 - rank) * (1 - first) := by
    have hkey : design.weight label * (2 * (rank : ℝ) - ((size : ℝ) - 1))
        < ((size : ℝ) - 2 - rank) * (((size : ℝ) - 1) - rank) := by
      by_cases hsign : 0 ≤ 2 * (rank : ℝ) - ((size : ℝ) - 1)
      · nlinarith [hsharp, hweightLe, hsign]
      · have hneg : 2 * (rank : ℝ) - ((size : ℝ) - 1) < 0 := not_le.mp hsign
        nlinarith [hgapPos, hneg, hweightPos]
    nlinarith [hkey, hlabel, hfirstNonneg, hweightPos, hgapPos, hslack]
  have hleak : design.weight label * (second - 1) < (size : ℝ) - 2 - rank := by
    have hscaled : design.weight label * (second - 1) * (1 - first)
        < ((size : ℝ) - 2 - rank) * (1 - first) := by
      have hrewrite : (second - 1) * (1 - first) = 2 * first - 1 := by nlinarith [hupdate]
      nlinarith [hcross, hrewrite]
    exact lt_of_mul_lt_mul_right (by nlinarith [hscaled]) hslack.le
  obtain ⟨secondLabel, hsecondMem, hsecondLt⟩ :=
    exists_pivot_lt_one_erase_of_leak design htwo hfirstLt hleak
  refine ⟨((Finset.univ : Finset (Fin size)).erase label).erase secondLabel, ?_,
    posDef_erase_of_pivot_lt_one design hsecondMem hbasePosDef hsecondLt⟩
  rw [Finset.card_erase_of_mem hsecondMem,
    Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ, Fintype.card_fin]
  omega

/-- The sharp arithmetic condition holds at every cell of the sharp window at
rank three and up. -/
theorem sharp_two_drop_arith (rank size : ℕ) (hrank : 3 ≤ rank) (hlow : 2 * rank ≤ size) :
    2 * (rank : ℝ) - ((size : ℝ) - 1)
      < ((size : ℝ) - 2 - rank) * ((size : ℝ) - 1 - rank) := by
  have hrankCast : (3 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  have hlowCast : 2 * (rank : ℝ) ≤ (size : ℝ) := by exact_mod_cast hlow
  nlinarith [hrankCast, hlowCast]

/-- **TWO FREE DROPS AT EVERY CELL OF THE SHARP WINDOW.**  Every design of a rank
three or more, at a size of at least twice the rank, carries a strictly
dominating subset of card two below its size.  No weight hypothesis, no stress,
no predecessor cell.  At `(6,3)` the conclusion is a strictly dominating
QUADRUPLE, one label above the triple the conjecture asks for. -/
theorem exists_two_erase_posDef_window (design : WeightedDesign size rank)
    (hrank : 3 ≤ rank) (hlow : 2 * rank ≤ size) :
    ∃ selected : Finset (Fin size), selected.card = size - 2
      ∧ (subsetSum design selected - 1).PosDef :=
  exists_two_erase_posDef_sharp design (by omega) (sharp_two_drop_arith rank size hrank hlow)

/-- **THE DECIDING CELL OF RANK THREE CARRIES A STRICTLY DOMINATING QUADRUPLE.**
Every `(6,3)` design does, unconditionally.  The gap between this and weighted
GTZ at `(6,3)` is exactly one more drop. -/
theorem exists_card_four_posDef_six_three (design : WeightedDesign 6 3) :
    ∃ selected : Finset (Fin 6), selected.card = 4
      ∧ (subsetSum design selected - 1).PosDef :=
  exists_two_erase_posDef_window design (by omega) (by omega)

/-- **A TIE OF THE SHARP WINDOW STALLS ONLY AT THE LAST STAGE OR NEAR IT.**  The
descent of a tie reaches card `size - 2` for free, thus every obstruction to the
hinge lives strictly below that card. -/
theorem tie_stalls_below_card_sub_two (design : WeightedDesign size rank)
    (hrank : 3 ≤ rank) (hlow : 2 * rank ≤ size) (htie : IsTie design) :
    ∃ selected : Finset (Fin size), selected.card = size - 2
      ∧ (subsetSum design selected - 1).PosDef
      ∧ ∀ dominating : Finset (Fin size), dominating.card = rank →
          ¬ (subsetSum design dominating - 1).PosDef := by
  obtain ⟨selected, hcard, hposDef⟩ := exists_two_erase_posDef_window design hrank hlow
  exact ⟨selected, hcard, hposDef, htie.2⟩


/-! ## Part 13: the residue the descent leaves at the deciding cell of rank three

At rank three the deciding cell has six labels and the two free drops reach card
four, which is exactly `rank + 1`.  The stage law at a region of card `rank + 1`
is an identity with a leak of two terms, and a tie makes every pivot value inside
the region at least one.  Thus the whole obstruction collapses to ONE scalar
inequality at ONE label outside the region. -/

/-- **A TIE PUTS THE WHOLE LEAK OUTSIDE.**  At a strictly dominating region of
card `rank + 1` of a tied design, the outside labels carry pivot mass at least
their own weight.  Hence some label outside the region has pivot value at least
one against it. -/
theorem tie_exists_outside_pivot_ge_one (design : WeightedDesign size rank)
    (htie : IsTie design) {base : Finset (Fin size)} (hcard : base.card = rank + 1)
    (hposDef : (subsetSum design base - 1).PosDef) (hne : baseᶜ.Nonempty) :
    ∃ label ∈ baseᶜ, 1 ≤ pivot design base label := by
  classical
  by_contra hnone
  push Not at hnone
  have hinside : ∀ c ∈ base, 1 ≤ pivot design base c := by
    intro c hc
    by_contra hlt
    push Not at hlt
    refine htie.2 (base.erase c) ?_ (posDef_erase_of_pivot_lt_one design hc hposDef hlt)
    rw [Finset.card_erase_of_mem hc, hcard]
    omega
  have hlower : ∑ c ∈ base, (1 - design.weight c)
      ≤ ∑ c ∈ base, (1 - design.weight c) * pivot design base c := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hfree : 0 ≤ 1 - design.weight c := by linarith [weight_le_one design c]
    nlinarith [hinside c hc, hfree]
  have hstage := sum_freeWeight_pivot_eq_rank_add_outside design base hposDef
  have hleakSmall : ∑ c ∈ baseᶜ, design.weight c * pivot design base c
      < ∑ c ∈ baseᶜ, design.weight c := by
    refine Finset.sum_lt_sum_of_nonempty hne fun c hc => ?_
    nlinarith [hnone c hc, design.weight_pos c]
  have hsplit : ∑ c ∈ base, design.weight c + ∑ c ∈ baseᶜ, design.weight c = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact design.weight_sum_one
  have hfree : ∑ c ∈ base, (1 - design.weight c)
      = (base.card : ℝ) - ∑ c ∈ base, design.weight c := by
    rw [Finset.sum_sub_distrib]; simp
  have hcardCast : (base.card : ℝ) = (rank : ℝ) + 1 := by
    rw [hcard]; push_cast; ring
  rw [hfree, hcardCast] at hlower
  rw [hstage] at hlower
  linarith

/-- **THE EXACT RESIDUE AT THE DECIDING CELL OF RANK THREE.**  A `(6,3)` tie
carries a strictly dominating QUADRUPLE, and one of the two labels outside that
quadruple has pivot value at least one against it.  Everything else about the
tie is discharged: the two drops that reach the quadruple are free, and the
obstruction is this single scalar inequality.

Weighted GTZ at `(6,3)` on the tie branch is therefore exactly the statement that
this cannot happen. -/
theorem sixThree_tie_quadruple_residue (design : WeightedDesign 6 3) (htie : IsTie design) :
    ∃ (quadruple : Finset (Fin 6)) (outside : Fin 6),
      quadruple.card = 4 ∧ (subsetSum design quadruple - 1).PosDef
        ∧ outside ∉ quadruple ∧ 1 ≤ pivot design quadruple outside := by
  classical
  obtain ⟨quadruple, hcard, hposDef⟩ := exists_card_four_posDef_six_three design
  have hcompl : quadrupleᶜ.card = 2 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  have hne : quadrupleᶜ.Nonempty := by
    rw [← Finset.card_pos, hcompl]
    omega
  obtain ⟨outside, hmem, hpivot⟩ :=
    tie_exists_outside_pivot_ge_one design htie (by omega) hposDef hne
  exact ⟨quadruple, outside, hcard, hposDef, Finset.mem_compl.mp hmem, hpivot⟩

/-- **THE SAME RESIDUE, AS A CLOSURE.**  If no `(6,3)` design carries a strictly
dominating quadruple with an outside label of pivot value at least one, then
weighted GTZ holds at `(6,3)` on the tie branch, and every `(6,3)` tie has a
parallel pair for the trivial reason that no tie exists. -/
theorem not_isTie_of_no_quadruple_residue_six_three
    (hclosed : ∀ (design : WeightedDesign 6 3) (quadruple : Finset (Fin 6)) (outside : Fin 6),
      quadruple.card = 4 → (subsetSum design quadruple - 1).PosDef → outside ∉ quadruple →
        pivot design quadruple outside < 1)
    (design : WeightedDesign 6 3) : ¬ IsTie design := by
  intro htie
  obtain ⟨quadruple, outside, hcard, hposDef, hnotMem, hpivot⟩ :=
    sixThree_tie_quadruple_residue design htie
  exact absurd (hclosed design quadruple outside hcard hposDef hnotMem) (not_lt.mpr hpivot)


/-! ## Part 14: the arm-free route to the deciding cell of rank three

The two free drops carry every `(6,3)` design to a strictly dominating quadruple.
A quadruple is a set of card `rank + 1` at rank three, thus the whole deciding
cell reduces to ONE statement about card-`rank + 1` sets, and the three-arm
trichotomy is bypassed entirely.

The reduction is FAITHFUL and not a strengthening: at `(6,3)` the named Prop is
equivalent to the absence of a tie, because every design carries the quadruple
the Prop speaks about. -/

/-- **THE LAST STAGE, NAMED.**  A strictly dominating set of card `rank + 1`
yields a strictly dominating set of card `rank`.  The witness is not asked to sit
inside the given set, thus this is the weakest form of the last drop. -/
def RankSuccShrinks (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (base : Finset (Fin size)),
    base.card = rank + 1 → (subsetSum design base - 1).PosDef →
      ∃ selected : Finset (Fin size), selected.card = rank
        ∧ (subsetSum design selected - 1).PosDef

/-- A design that reaches a strictly dominating set of card `rank + 1` is not a
tie, once the last stage is available. -/
theorem not_isTie_of_rankSuccShrinks (hshrink : RankSuccShrinks size rank)
    (design : WeightedDesign size rank) {base : Finset (Fin size)}
    (hcard : base.card = rank + 1) (hposDef : (subsetSum design base - 1).PosDef) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hselectedCard, hselectedPosDef⟩ := hshrink design base hcard hposDef
  exact htie.2 selected hselectedCard hselectedPosDef

/-- **NO `(6,3)` TIE, FROM THE LAST STAGE ALONE.**  The quadruple is a theorem,
thus the last stage is the only input. -/
theorem not_isTie_six_three_of_rankSuccShrinks (hshrink : RankSuccShrinks 6 3)
    (design : WeightedDesign 6 3) : ¬ IsTie design := by
  obtain ⟨quadruple, hcard, hposDef⟩ := exists_card_four_posDef_six_three design
  exact not_isTie_of_rankSuccShrinks hshrink design (by omega) hposDef

/-- **THE HINGE AT `(6,3)` FROM THE LAST STAGE ALONE.**  With no tie the hinge is
vacuous, thus the three-arm trichotomy is not used at all. -/
theorem hingeHoldsAtSize_six_three_of_rankSuccShrinks (hshrink : RankSuccShrinks 6 3) :
    HingeHoldsAtSize 6 3 := fun design htie =>
  absurd htie (not_isTie_six_three_of_rankSuccShrinks hshrink design)

/-- **WEIGHTED GTZ AT `(6,3)` FROM THE LAST STAGE ALONE.**  No stress-free arm, no
balanced arm, no degenerate arm, no reach, no anchor, no icosahedron: one
statement about strictly dominating quadruples. -/
theorem gtzWeighted_six_three_of_rankSuccShrinks (hshrink : RankSuccShrinks 6 3) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_hinge (hingeHoldsAtSize_six_three_of_rankSuccShrinks hshrink)

/-- **ALL OF RANK THREE FROM THE LAST STAGE ALONE.** -/
theorem gtzWeightedAll_three_of_rankSuccShrinks (hshrink : RankSuccShrinks 6 3) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (hingeHoldsAtSize_six_three_of_rankSuccShrinks hshrink)

/-- **THE REDUCTION IS FAITHFUL.**  The named Prop follows from the conjecture it
is used to prove, together with the absence of a tie.  Thus it asserts nothing
beyond the deciding cell, and the trade is a change of formula and not a change
of strength. -/
theorem rankSuccShrinks_six_three_of_gtz_of_noTie (hgtz : GtzWeighted 6 3)
    (hnoTie : ∀ design : WeightedDesign 6 3, ¬ IsTie design) : RankSuccShrinks 6 3 := by
  classical
  intro design _base _hcard _hposDef
  obtain ⟨weakDominator, hweakCard, hweakDominates⟩ := hgtz design
  by_contra hnone
  push Not at hnone
  exact hnoTie design ⟨⟨weakDominator, hweakCard, hweakDominates⟩,
    fun selected hcard hposDef => hnone selected hcard hposDef⟩

/-- **THE `(6,3)` EQUIVALENCE.**  At the deciding cell of rank three the last
stage and the absence of a tie are the same statement, because the quadruple the
last stage speaks about always exists. -/
theorem rankSuccShrinks_six_three_iff_noTie :
    RankSuccShrinks 6 3 ↔ ∀ design : WeightedDesign 6 3, ¬ IsTie design := by
  refine ⟨fun hshrink design => not_isTie_six_three_of_rankSuccShrinks hshrink design,
    fun hnoTie => ?_⟩
  exact rankSuccShrinks_six_three_of_gtz_of_noTie
    (gtzWeighted_six_three_of_hinge fun design htie => absurd htie (hnoTie design)) hnoTie

/-- **THE GENERAL-RANK SHAPE.**  A cell whose designs all reach a strictly
dominating set of card `rank + 1` reduces its hinge to the last stage.  Rank
three reaches it unconditionally; at rank four and up the free drops of Part 12
reach card `size - 2`, which is above `rank + 1` at the deciding cell, and the
gap is exactly `size - rank - 3` more drops. -/
theorem hingeHoldsAtSize_of_rankSuccShrinks_of_reach (hshrink : RankSuccShrinks size rank)
    (hreach : ∀ design : WeightedDesign size rank, ∃ base : Finset (Fin size),
      base.card = rank + 1 ∧ (subsetSum design base - 1).PosDef) :
    HingeHoldsAtSize size rank := by
  intro design htie
  obtain ⟨base, hcard, hposDef⟩ := hreach design
  exact absurd htie (not_isTie_of_rankSuccShrinks hshrink design hcard hposDef)

/-- The deciding cell of rank three reaches card `rank + 1` unconditionally. -/
theorem reach_rankSucc_six_three (design : WeightedDesign 6 3) :
    ∃ base : Finset (Fin 6), base.card = 3 + 1
      ∧ (subsetSum design base - 1).PosDef := by
  obtain ⟨quadruple, hcard, hposDef⟩ := exists_card_four_posDef_six_three design
  exact ⟨quadruple, by omega, hposDef⟩

/-- **THE RESIDUE, IN ITS SMALLEST SHAPE.**  At `(6,3)` the last stage is exactly
this: a strictly dominating quadruple with every pivot value at least one cannot
occur.  The stage law turns that into one label outside the quadruple, and
`Gtz.sixThree_tie_quadruple_residue` is the reading a certificate must refute. -/
theorem rankSuccShrinks_six_three_of_insideDrop
    (hdrop : ∀ (design : WeightedDesign 6 3) (base : Finset (Fin 6)),
      base.card = 4 → (subsetSum design base - 1).PosDef →
        ∃ label ∈ base, pivot design base label < 1) :
    RankSuccShrinks 6 3 := by
  classical
  intro design base hcard hposDef
  obtain ⟨label, hmem, hlabel⟩ := hdrop design base (by omega) hposDef
  refine ⟨base.erase label, ?_, posDef_erase_of_pivot_lt_one design hmem hposDef hlabel⟩
  rw [Finset.card_erase_of_mem hmem, hcard]


/-! ## Part 15: the sharp descent at a bare frame, and the ceiling reduction

Everything of Parts 12 and 14 transports to a bare frame with a total scale below
one, and it transports with ROOM TO SPARE, because the free excess of a bare
frame is `atomCount - sigma` and not `atomCount - 1`.  At six atoms in rank three
the conclusion is a strictly dominating QUADRUPLE at every total scale below one,
thus the atom triple ceiling reduces to the last stage exactly as the deciding
cell of rank three does. -/

/-- **THE MEDIANT AT A BARE FRAME.** -/
theorem frame_exists_pivot_univ_le_mediant {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) (hlt : ∀ c, scale c < 1)
    (hne : 0 < atomCount) :
    ∃ label : Fin atomCount,
      framePivot atomFamily Finset.univ label * ((atomCount : ℝ) - ∑ c, scale c)
        ≤ rank := by
  classical
  have hposDef := frame_posDef_gap_univ atomFamily scale hframe hlt
  have hstage := frame_stage_law atomFamily scale hframe Finset.univ hposDef
  rw [Finset.compl_univ, Finset.sum_empty, add_zero] at hstage
  have hsum : ∑ c ∈ (Finset.univ : Finset (Fin atomCount)), (1 - scale c)
      = (atomCount : ℝ) - ∑ c, scale c := by
    rw [Finset.sum_sub_distrib]; simp
  by_contra hnone
  push Not at hnone
  have hbig : ∑ c, (1 - scale c) * (rank : ℝ)
      < ∑ c, (1 - scale c)
        * (framePivot atomFamily Finset.univ c * ((atomCount : ℝ) - ∑ d, scale d)) := by
    refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, hne⟩, Finset.mem_univ _⟩ fun c _ => ?_
    exact mul_lt_mul_of_pos_left (hnone c) (by linarith [hlt c])
  rw [← Finset.sum_mul, hsum] at hbig
  have hrewrite : ∑ c, (1 - scale c)
      * (framePivot atomFamily Finset.univ c * ((atomCount : ℝ) - ∑ d, scale d))
      = (∑ c, (1 - scale c) * framePivot atomFamily Finset.univ c)
        * ((atomCount : ℝ) - ∑ d, scale d) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hrewrite, hstage] at hbig
  linarith

/-- **THE SECOND DROP AT A BARE FRAME, PRICED EXACTLY.** -/
theorem frame_exists_pivot_lt_one_erase_of_leak {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) (hlt : ∀ c, scale c < 1)
    {label : Fin atomCount} (hlabel : framePivot atomFamily Finset.univ label < 1)
    (hleak : scale label
        * (framePivot atomFamily (Finset.univ.erase label) label - 1)
      < (atomCount : ℝ) - 1 - (∑ c, scale c) - rank) :
    ∃ second ∈ Finset.univ.erase label,
      framePivot atomFamily (Finset.univ.erase label) second < 1 := by
  classical
  have hposDef := frame_posDef_gap_univ atomFamily scale hframe hlt
  have herase : (Finset.univ : Finset (Fin atomCount)).erase label = Finset.univ \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsingle : ∑ c ∈ ({label} : Finset (Fin atomCount)),
      framePivot atomFamily Finset.univ c < 1 := by
    simp only [Finset.sum_singleton]
    exact hlabel
  have hbasePosDef : (frameGap atomFamily (Finset.univ.erase label)).PosDef := by
    rw [herase]
    exact frame_posDef_sdiff_of_pivotSum_lt_one atomFamily (Finset.subset_univ _) hposDef hsingle
  have hcompl : ((Finset.univ : Finset (Fin atomCount)).erase label)ᶜ = {label} := by
    ext c; simp
  have hcard : ((Finset.univ : Finset (Fin atomCount)).erase label).card = atomCount - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ, Fintype.card_fin]
  have hone : 1 ≤ atomCount := Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    exact absurd (Finset.mem_univ label) (by simp [hzero] at label ⊢; exact label.elim0))
  have hfree : ∑ c ∈ (Finset.univ : Finset (Fin atomCount)).erase label, (1 - scale c)
      = ((atomCount : ℝ) - 1) - ((∑ c, scale c) - scale label) := by
    have hsplit : scale label + ∑ c ∈ Finset.univ.erase label, scale c = ∑ c, scale c := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ label)]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    have hcast : ((atomCount - 1 : ℕ) : ℝ) = (atomCount : ℝ) - 1 := by
      push_cast [Nat.cast_sub hone]
      ring
    rw [hcast]
    linarith
  refine frame_exists_pivot_lt_one_of_leak atomFamily scale hframe hbasePosDef
    (fun c => (hlt c).le) ?_
  rw [hcompl, Finset.sum_singleton, hfree]
  linarith

/-- **TWO FREE DROPS AT A BARE FRAME.**  The sharp arithmetic condition is stated
against the total scale, thus the free excess `atomCount - sigma` replaces the
design's `size - 1` everywhere. -/
theorem frame_exists_two_erase_posDef_sharp {atomCount : ℕ}
    (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) (hpos : ∀ c, 0 < scale c)
    (htotal : ∑ c, scale c < 1) (hbig : rank + 2 < atomCount)
    (hsharp : (∑ c, scale c) * (2 * (rank : ℝ) - ((atomCount : ℝ) - ∑ c, scale c))
      < ((atomCount : ℝ) - (∑ c, scale c) - 1 - rank)
        * (((atomCount : ℝ) - ∑ c, scale c) - rank)) :
    ∃ selected : Finset (Fin atomCount), selected.card = atomCount - 2
      ∧ (frameGap atomFamily selected).PosDef := by
  classical
  have hlt : ∀ c, scale c < 1 := by
    intro c
    have hsingle : scale c ≤ ∑ d, scale d :=
      Finset.single_le_sum (fun d _ => (hpos d).le) (Finset.mem_univ c)
    linarith
  have hposDef := frame_posDef_gap_univ atomFamily scale hframe hlt
  have hcast : (rank : ℝ) + 2 < (atomCount : ℝ) := by exact_mod_cast hbig
  have htotalPos : 0 < ∑ c, scale c := by
    refine Finset.sum_pos (fun c _ => hpos c) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨label, hlabel⟩ := frame_exists_pivot_univ_le_mediant atomFamily scale hframe hlt
    (by omega)
  set total : ℝ := ∑ c, scale c with htotalDef
  set first : ℝ := framePivot atomFamily Finset.univ label with hfirst
  have hfirstNonneg : 0 ≤ first := framePivot_nonneg atomFamily hposDef label
  have hgapPos : (0 : ℝ) < (atomCount : ℝ) - total - rank := by linarith
  have hfirstLt : first < 1 := by nlinarith [hlabel, hgapPos, hfirstNonneg, htotalPos]
  have herase : (Finset.univ : Finset (Fin atomCount)).erase label = Finset.univ \ {label} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  have hsingle : ∑ c ∈ ({label} : Finset (Fin atomCount)),
      framePivot atomFamily Finset.univ c < 1 := by
    simp only [Finset.sum_singleton]
    exact hfirstLt
  have hbasePosDef : (frameGap atomFamily (Finset.univ.erase label)).PosDef := by
    rw [herase]
    exact frame_posDef_sdiff_of_pivotSum_lt_one atomFamily (Finset.subset_univ _) hposDef hsingle
  have hupdate : first * (1 + framePivot atomFamily (Finset.univ.erase label) label)
      = framePivot atomFamily (Finset.univ.erase label) label :=
    framePivot_erase_eq atomFamily (Finset.mem_univ label) hbasePosDef
  set second : ℝ := framePivot atomFamily (Finset.univ.erase label) label with hsecondDef
  have hscaleLe : scale label ≤ total :=
    Finset.single_le_sum (fun d _ => (hpos d).le) (Finset.mem_univ label)
  have hslack : (0 : ℝ) < 1 - first := by linarith
  have hcross : scale label * (2 * first - 1)
      < ((atomCount : ℝ) - total - 1 - rank) * (1 - first) := by
    have hkey : scale label * (2 * (rank : ℝ) - ((atomCount : ℝ) - total))
        < ((atomCount : ℝ) - total - 1 - rank) * (((atomCount : ℝ) - total) - rank) := by
      by_cases hsign : 0 ≤ 2 * (rank : ℝ) - ((atomCount : ℝ) - total)
      · nlinarith [hsharp, hscaleLe, hsign]
      · have hneg : 2 * (rank : ℝ) - ((atomCount : ℝ) - total) < 0 := not_le.mp hsign
        nlinarith [hgapPos, hneg, hpos label, hcast, htotal]
    nlinarith [hkey, hlabel, hfirstNonneg, hpos label, hgapPos, hslack, htotalPos]
  have hleak : scale label * (second - 1) < (atomCount : ℝ) - 1 - total - rank := by
    have hscaled : scale label * (second - 1) * (1 - first)
        < ((atomCount : ℝ) - total - 1 - rank) * (1 - first) := by
      have hrewrite : (second - 1) * (1 - first) = 2 * first - 1 := by nlinarith [hupdate]
      nlinarith [hcross, hrewrite]
    have hfinal : scale label * (second - 1) < (atomCount : ℝ) - total - 1 - rank :=
      lt_of_mul_lt_mul_right (by nlinarith [hscaled]) hslack.le
    linarith
  obtain ⟨secondLabel, hsecondMem, hsecondLt⟩ :=
    frame_exists_pivot_lt_one_erase_of_leak atomFamily scale hframe hlt hfirstLt hleak
  have hsecondSingle : ∑ c ∈ ({secondLabel} : Finset (Fin atomCount)),
      framePivot atomFamily (Finset.univ.erase label) c < 1 := by
    simp only [Finset.sum_singleton]
    exact hsecondLt
  have hsecondErase : ((Finset.univ : Finset (Fin atomCount)).erase label).erase secondLabel
      = ((Finset.univ : Finset (Fin atomCount)).erase label) \ {secondLabel} := by
    ext c; simp [Finset.mem_erase, Finset.mem_sdiff, and_comm]
  refine ⟨((Finset.univ : Finset (Fin atomCount)).erase label).erase secondLabel, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hsecondMem,
      Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ, Fintype.card_fin]
    omega
  · rw [hsecondErase]
    exact frame_posDef_sdiff_of_pivotSum_lt_one atomFamily
      (by simpa using hsecondMem) hbasePosDef hsecondSingle

/-- The sharp arithmetic condition at six atoms in rank three, at every total
scale below one. -/
theorem frame_sharp_six_three (total : ℝ) (hpos : 0 < total) (hlt : total < 1) :
    total * (2 * (3 : ℝ) - ((6 : ℝ) - total))
      < ((6 : ℝ) - total - 1 - 3) * (((6 : ℝ) - total) - 3) := by
  nlinarith [hpos, hlt]

/-- **A STRICTLY DOMINATING QUADRUPLE AT EVERY SIX-ATOM FRAME OF RANK THREE.**
This is the design-free twin of `Gtz.exists_card_four_posDef_six_three`, and it
is the first two stages of the atom-ceiling descent, free at every total scale
below one. -/
theorem frame_exists_card_four_posDef_six_three
    (atomFamily : Fin 6 → Fin 3 → ℝ) (scale : Fin 6 → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) (hpos : ∀ c, 0 < scale c)
    (htotal : ∑ c, scale c < 1) :
    ∃ selected : Finset (Fin 6), selected.card = 4
      ∧ (frameGap atomFamily selected).PosDef := by
  have htotalPos : 0 < ∑ c, scale c :=
    Finset.sum_pos (fun c _ => hpos c) ⟨0, Finset.mem_univ 0⟩
  have hstep := frame_exists_two_erase_posDef_sharp atomFamily scale hframe hpos htotal
    (by omega) (frame_sharp_six_three _ htotalPos htotal)
  simpa using hstep

/-- **THE LAST STAGE AT A BARE FRAME, NAMED.** -/
def FrameRankSuccShrinks (atomCount rank : ℕ) : Prop :=
  ∀ (atomFamily : Fin atomCount → Fin rank → ℝ) (scale : Fin atomCount → ℝ),
    (∑ c, scale c • atomMatrix (atomFamily c)) = 1 → (∀ c, 0 < scale c) →
    (∑ c, scale c) < 1 →
    ∀ base : Finset (Fin atomCount), base.card = rank + 1 →
      (frameGap atomFamily base).PosDef →
        ∃ selected : Finset (Fin atomCount), selected.card = rank
          ∧ (frameGap atomFamily selected).PosDef

/-- **THE ATOM TRIPLE CEILING FROM THE LAST STAGE ALONE.**  Six atoms resolving
the identity with positive scales of total below one carry a strictly dominating
TRIPLE, provided the last stage of the descent is available.  The two stages
above it are theorems, thus the whole ceiling is one statement about strictly
dominating quadruples -- the same statement the deciding cell of rank three
reduces to on the design side. -/
theorem frame_exists_card_three_posDef_six_three (hshrink : FrameRankSuccShrinks 6 3)
    (atomFamily : Fin 6 → Fin 3 → ℝ) (scale : Fin 6 → ℝ)
    (hframe : ∑ c, scale c • atomMatrix (atomFamily c) = 1) (hpos : ∀ c, 0 < scale c)
    (htotal : ∑ c, scale c < 1) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (frameGap atomFamily selected).PosDef := by
  obtain ⟨quadruple, hcard, hposDef⟩ :=
    frame_exists_card_four_posDef_six_three atomFamily scale hframe hpos htotal
  exact hshrink atomFamily scale hframe hpos htotal quadruple (by omega) hposDef


end Gtz
