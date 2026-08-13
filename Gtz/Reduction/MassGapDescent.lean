/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.ThresholdCellHingeMap
import Gtz.Uniform.WindowInductionStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The mass-gap descent, and the tie-carrying recut of the deepest hinge arm

`Gtz.MassGapSideIsRankSized` is the deepest of the three arms the threshold-cell
hinge map leaves open.  The mass-gap firing hands back the WHOLE positive side,
whose card lies in `[rank, thresholdSize rank - rank]`, while a tie forbids
strict domination at card `rank` ONLY.  At rank three the two coincide.  At rank
four and up the window is a genuine interval and the firing yields nothing.

This module does four things.

## 1. The descent engine

A strictly dominating set shrinks by one label exactly when that label's PIVOT
value is less than one (`Gtz.posDef_erase_of_pivot_lt_one`).  The pivot values of
a strictly dominating set add up to `rank` plus the trace of the inverse gap
(`Gtz.sum_pivot_eq_rank_add_trace_inv`), thus a small inverse gap forces a
droppable label (`Gtz.exists_pivot_lt_one_of_trace_inv_lt`).  Iterating the drop
carries any strictly dominating set down to card `rank`
(`Gtz.exists_rankSized_posDef_of_pivotDrop`).

## 2. What the mass gap buys, quantitatively

The mass gap is a Loewner bound and nothing else: the gap of the positive side
majorizes the middle matrix scaled by the level difference
(`Gtz.massGap_gap_form_ge`).  Two exact identities turn that bound into a pivot
estimate.  The inverse form is antitone in the form
(`Gtz.inverseForm_le_of_form_le_smul`), and the stress-weighted inverse forms of
the middle matrix add up to the rank
(`Gtz.sum_stress_middleInverseForm_eq_rank`).  Together they give the firing
`Gtz.exists_pivot_lt_one_of_massGap`: when the level difference times the
positive-side stress mass exceeds the rank, the positive side drops a label.

## 3. The obstruction is real, and it is exact

`Gtz.exists_posDef_without_rankSized_posDef_subset` builds three explicit
rational atoms in two dimensions whose sum dominates STRICTLY while every pair
among them fails to dominate strictly.  Thus the naive route -- shrink the
returned side to card `rank` -- is not merely unproved.  It is FALSE as a
statement about sets, at every rank of two or more.  The witness is the rational
cousin of the tight-frame configuration, and it is the same convexity gap the
atom-energy ceiling meets on the wave side.

## 4. The recut

`Gtz.MassGapSideIsRankSized` is used at exactly one place, and at that place the
design is a TIE and is PRIMITIVE.  Both hypotheses are free.  The recut arm
`Gtz.TieFreeMassGappedStress` carries them, is implied by the shipped arm
(`Gtz.tieFreeMassGappedStress_of_massGapSideIsRankSized`), and rebuilds the whole
chain: the balanced arm (`Gtz.balancedArmAt_of_tieFreeResiduals`), the rank-three
instance (`Gtz.thresholdBalancedArm_three_of_tieFreeResiduals`), the deciding
cell (`Gtz.gtzWeighted_six_three_of_tieFreeResiduals`) and the rank-four-and-up
hinge obligation (`Gtz.thresholdCellHingeRankFourAndUp_of_tieFreeResiduals`).

A successor thus starts from a strictly weaker statement, with a tie and a
primitive design in hand, and with the descent engine already built.
-/

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1: the pivot is the inverse form, and it prices a single drop -/

/-- The trace pairing of a matrix against an atom is the atom's form in that
matrix.  This is the dictionary entry that turns `Gtz.pivot`, which is stated
through the trace, into a quadratic form. -/
theorem trace_mul_atomMatrix (gramMat : Matrix (Fin rank) (Fin rank) ℝ)
    (atomVec : Fin rank → ℝ) :
    Matrix.trace (gramMat * atomMatrix atomVec) = atomVec ⬝ᵥ (gramMat *ᵥ atomVec) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The pivot value of a label against a base set is the atom's form in the
inverse gap. -/
theorem pivot_eq_inverseForm (design : WeightedDesign size rank)
    (base : Finset (Fin size)) (label : Fin size) :
    pivot design base label
      = design.atom label ⬝ᵥ ((subsetSum design base - 1)⁻¹ *ᵥ design.atom label) :=
  trace_mul_atomMatrix _ _

/-- Erasing a label from a subset removes exactly that label's atom. -/
theorem subsetSum_erase (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∈ selected) :
    subsetSum design (selected.erase label)
      = subsetSum design selected - atomMatrix (design.atom label) := by
  classical
  rw [subsetSum, subsetSum, Finset.sum_erase_eq_sub hmem]

/-- **THE DROP, AS A RANK-ONE SCHUR STEP.**  A positive definite matrix stays
positive definite after one rank-one subtraction exactly when the subtracted
vector's inverse form is less than one.  The proof is Cauchy-Schwarz in the
matrix metric and nothing else, thus it carries no size and no rank hypothesis.
-/
theorem posDef_sub_atomMatrix_of_inverseForm_lt_one
    {gramMat : Matrix (Fin rank) (Fin rank) ℝ} (hposDef : gramMat.PosDef)
    {source : Fin rank → ℝ} (hform : source ⬝ᵥ (gramMat⁻¹ *ᵥ source) < 1) :
    (gramMat - atomMatrix source).PosDef := by
  have hsymm : (gramMat - atomMatrix source)ᵀ = gramMat - atomMatrix source := by
    rw [Matrix.transpose_sub, PosDef.transpose_eq hposDef,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix source).1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  have hbase : 0 < probe ⬝ᵥ (gramMat *ᵥ probe) := by
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rwa [star_trivial] at hstep
  have hcauchy := dotProduct_sq_le_inverseForm_mul_form hposDef source probe
  have hpair : (source ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ (gramMat *ᵥ probe) := by
    nlinarith [hcauchy, hbase, hform, sq_nonneg (source ⬝ᵥ probe)]
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, atom_form_eq_sq]
  linarith

/-- **THE DROP AT THE DESIGN LEVEL.**  A strictly dominating subset that carries
a label of pivot value less than one stays strictly dominating after that label
is erased. -/
theorem posDef_erase_of_pivot_lt_one (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∈ selected)
    (hposDef : (subsetSum design selected - 1).PosDef)
    (hpivot : pivot design selected label < 1) :
    (subsetSum design (selected.erase label) - 1).PosDef := by
  have hstep := posDef_sub_atomMatrix_of_inverseForm_lt_one hposDef
    (source := design.atom label) (by rwa [← pivot_eq_inverseForm])
  rw [subsetSum_erase design hmem]
  have hrearrange : subsetSum design selected - atomMatrix (design.atom label) - 1
      = subsetSum design selected - 1 - atomMatrix (design.atom label) := by
    abel
  rwa [hrearrange]

/-! ## Part 2: the pivot budget of a strictly dominating set -/

/-- **THE PIVOT BUDGET.**  The pivot values of a strictly dominating subset add
up to the rank plus the trace of the inverse gap.  No stress, no mass gap and no
size hypothesis appear: this is Parseval-free bookkeeping on the gap matrix. -/
theorem sum_pivot_eq_rank_add_trace_inv (design : WeightedDesign size rank)
    (selected : Finset (Fin size))
    (hposDef : (subsetSum design selected - 1).PosDef) :
    ∑ c ∈ selected, pivot design selected c
      = (rank : ℝ) + Matrix.trace ((subsetSum design selected - 1)⁻¹) := by
  classical
  set gapMat : Matrix (Fin rank) (Fin rank) ℝ := subsetSum design selected - 1 with hgap
  have hunit : IsUnit gapMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hsum : ∑ c ∈ selected, pivot design selected c
      = Matrix.trace (gapMat⁻¹ * subsetSum design selected) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have hsplit : subsetSum design selected = gapMat + 1 := by rw [hgap]; abel
  rw [hsum, hsplit, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add,
    Matrix.nonsing_inv_mul gapMat hunit, Matrix.trace_one, Fintype.card_fin]

/-- **THE PIGEONHOLE FORM OF THE BUDGET.**  A strictly dominating subset whose
inverse gap has trace below the excess card carries a droppable label. -/
theorem exists_pivot_lt_one_of_trace_inv_lt (design : WeightedDesign size rank)
    (selected : Finset (Fin size))
    (hposDef : (subsetSum design selected - 1).PosDef)
    (htrace : Matrix.trace ((subsetSum design selected - 1)⁻¹)
      < (selected.card : ℝ) - rank) :
    ∃ label ∈ selected, pivot design selected label < 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hlower : (selected.card : ℝ) ≤ ∑ c ∈ selected, pivot design selected c := by
    have hbound : ∑ c ∈ selected, (1 : ℝ) ≤ ∑ c ∈ selected, pivot design selected c :=
      Finset.sum_le_sum fun c hc => hnone c hc
    simpa using hbound
  rw [sum_pivot_eq_rank_add_trace_inv design selected hposDef] at hlower
  linarith

/-! ## Part 3: the descent to card `rank` -/

/-- **THE DESCENT.**  A strictly dominating subset contracts to a strictly
dominating subset of card exactly `rank`, provided every strictly dominating
subset above that card carries a droppable label.  The induction runs on the
excess card and drops one label at a time. -/
theorem exists_rankSized_posDef_of_pivotDrop (design : WeightedDesign size rank)
    (base : Finset (Fin size))
    (hdrop : ∀ probeSet ⊆ base, rank < probeSet.card →
      (subsetSum design probeSet - 1).PosDef →
        ∃ label ∈ probeSet, pivot design probeSet label < 1)
    (excess : ℕ) :
    ∀ selected ⊆ base, selected.card = rank + excess →
      (subsetSum design selected - 1).PosDef →
        ∃ dominating ⊆ selected, dominating.card = rank
          ∧ (subsetSum design dominating - 1).PosDef := by
  classical
  induction excess with
  | zero =>
      intro selected _hsubset hcard hposDef
      exact ⟨selected, Finset.Subset.refl selected, by omega, hposDef⟩
  | succ excess ih =>
      intro selected hsubset hcard hposDef
      obtain ⟨label, hmem, hpivot⟩ := hdrop selected hsubset (by omega) hposDef
      have hsmaller : (selected.erase label).card = rank + excess := by
        rw [Finset.card_erase_of_mem hmem, hcard]
        omega
      obtain ⟨dominating, hdominatingSubset, hdominatingCard, hdominatingPosDef⟩ :=
        ih (selected.erase label)
          ((Finset.erase_subset label selected).trans hsubset) hsmaller
          (posDef_erase_of_pivot_lt_one design hmem hposDef hpivot)
      exact ⟨dominating, hdominatingSubset.trans (Finset.erase_subset label selected),
        hdominatingCard, hdominatingPosDef⟩

/-- The descent, stated against a card inequality, with the drop asked for only
inside the starting set. -/
theorem exists_rankSized_posDef_of_pivotDrop' (design : WeightedDesign size rank)
    {selected : Finset (Fin size)}
    (hdrop : ∀ probeSet ⊆ selected, rank < probeSet.card →
      (subsetSum design probeSet - 1).PosDef →
        ∃ label ∈ probeSet, pivot design probeSet label < 1)
    (hcard : rank ≤ selected.card)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    ∃ dominating ⊆ selected, dominating.card = rank
      ∧ (subsetSum design dominating - 1).PosDef :=
  exists_rankSized_posDef_of_pivotDrop design selected hdrop (selected.card - rank)
    selected (Finset.Subset.refl selected) (by omega) hposDef

/-! ### What a tie blocks

The descent turns the tie into a POSITIVE statement about pivot values.  A tie
forbids every rank-sized strict domination, thus every strictly dominating set of
a tied design hides a stage at which the descent stalls, and at that stage every
pivot value is at least one and the inverse gap carries at least the excess card
in trace.  These two are new quantitative consequences of a tie, and neither
mentions a stress. -/

/-- **A TIE BLOCKS THE DESCENT.**  Inside every strictly dominating set of a tied
design sits a strictly dominating subset, still above card `rank`, whose every
pivot value is at least one. -/
theorem exists_pivotBlocked_of_tie (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)} (hcard : rank ≤ selected.card)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    ∃ blocked ⊆ selected, rank < blocked.card
      ∧ (subsetSum design blocked - 1).PosDef
      ∧ ∀ label ∈ blocked, 1 ≤ pivot design blocked label := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨dominating, -, hdominatingCard, hdominatingPosDef⟩ :=
    exists_rankSized_posDef_of_pivotDrop' design
      (fun probeSet hsubset hbig hprobePosDef => hnone probeSet hsubset hbig hprobePosDef)
      hcard hposDef
  exact htie.2 dominating hdominatingCard hdominatingPosDef

/-- **A TIE COSTS TRACE.**  At the stalled stage the inverse gap carries at least
the excess card in trace.  This is the pivot budget read against the block. -/
theorem exists_traceBlocked_of_tie (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)} (hcard : rank ≤ selected.card)
    (hposDef : (subsetSum design selected - 1).PosDef) :
    ∃ blocked ⊆ selected, rank < blocked.card
      ∧ (subsetSum design blocked - 1).PosDef
      ∧ (blocked.card : ℝ) - rank
        ≤ Matrix.trace ((subsetSum design blocked - 1)⁻¹) := by
  classical
  obtain ⟨blocked, hsubset, hbig, hblockedPosDef, hpivots⟩ :=
    exists_pivotBlocked_of_tie design htie hcard hposDef
  refine ⟨blocked, hsubset, hbig, hblockedPosDef, ?_⟩
  have hlower : (blocked.card : ℝ) ≤ ∑ c ∈ blocked, pivot design blocked c := by
    have hbound : ∑ c ∈ blocked, (1 : ℝ) ≤ ∑ c ∈ blocked, pivot design blocked c :=
      Finset.sum_le_sum fun c hc => hpivots c hc
    simpa using hbound
  rw [sum_pivot_eq_rank_add_trace_inv design blocked hblockedPosDef] at hlower
  linarith

/-- **THE DROP CONDITION, NAMED.**  The single statement that turns every
strictly dominating set of a design into a rank-sized one.  It is a SUFFICIENT
residue and not a necessary one: Part 6 exhibits three atoms for which it fails
outright. -/
def PivotDropAtRank (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (probeSet : Finset (Fin size)),
    rank < probeSet.card → (subsetSum design probeSet - 1).PosDef →
      ∃ label ∈ probeSet, pivot design probeSet label < 1

/-- **THE ARM FROM THE DROP CONDITION.**  With the drop available, the whole
positive side of a mass-gapped stress contracts to card `rank` and the deepest
arm closes. -/
theorem massGapSideIsRankSized_of_pivotDrop (hdrop : PivotDropAtRank size rank) :
    MassGapSideIsRankSized size rank := by
  classical
  intro design stressCoeff hstress hfull hgap
  obtain ⟨dominating, -, hcard, hposDef⟩ :=
    exists_rankSized_posDef_of_pivotDrop' design
      (fun probeSet _hsubset hbig hprobePosDef => hdrop design probeSet hbig hprobePosDef)
      (rank_le_posSideCard_of_spans design
        (pos_side_spans design.atom
          (fun _probe hprobe => weightedDesign_atoms_span design hprobe) hstress hfull))
      (posDef_gap_posSide_of_massGap design hstress hfull hgap)
  exact ⟨dominating, hcard, hposDef⟩

/-! ## Part 4: what the mass gap buys, quantitatively

The mass gap is one Loewner bound.  Read against a probe it says the gap form of
the positive side majorizes the middle form scaled by the level difference. -/

/-- The complement of the positive side of a full-support stress is its negative
side. -/
theorem compl_posSide_eq_negSide {stressCoeff : Fin size → ℝ}
    (hfull : ∀ c, stressCoeff c ≠ 0) :
    (Finset.univ.filter fun c => 0 < stressCoeff c)ᶜ
      = Finset.univ.filter fun c => stressCoeff c < 0 := by
  classical
  ext c
  simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  exact ⟨fun hle => lt_of_le_of_ne hle (hfull c), fun hlt => hlt.le⟩

/-- **THE MASS GAP IS A LOEWNER BOUND.**  Along every probe the gap form of the
positive side is at least the level difference times the middle form.  Both
hypotheses of `Gtz.HasStressMassGap` enter once, and Parseval enters through the
free-minus-bound split. -/
theorem massGap_gap_form_ge (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (probe : Fin rank → ℝ) :
    (freeFloor - boundCeiling)
        * (probe ⬝ᵥ ((∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
            stressCoeff c • atomMatrix (design.atom c)) *ᵥ probe))
      ≤ probe ⬝ᵥ ((subsetSum design
          (Finset.univ.filter fun c => 0 < stressCoeff c) - 1) *ᵥ probe) := by
  classical
  set posSide := Finset.univ.filter (fun c => 0 < stressCoeff c) with hposSide
  set negSide := Finset.univ.filter (fun c => stressCoeff c < 0) with hnegSide
  set middleForm : ℝ := ∑ c ∈ posSide, stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2
    with hmiddleForm
  have hmiddleMatrix : probe ⬝ᵥ ((∑ c ∈ posSide,
      stressCoeff c • atomMatrix (design.atom c)) *ᵥ probe) = middleForm :=
    weighted_atomForm_eq_on posSide stressCoeff design.atom probe
  have htwoFrames : middleForm
      = ∑ c ∈ negSide, (-stressCoeff c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [hmiddleForm, ← weighted_atomForm_eq_on posSide stressCoeff design.atom probe,
      posSideSum_eq_negSideSum design.atom hstress,
      weighted_atomForm_eq_on negSide (fun c => -stressCoeff c) design.atom probe]
  have hfreeSide : freeFloor * middleForm
      ≤ ∑ c ∈ posSide, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [hmiddleForm, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hsign : 0 < stressCoeff c := (Finset.mem_filter.mp hc).2
    have hstep := hfree c hsign
    have hsq : (0 : ℝ) ≤ (design.atom c ⬝ᵥ probe) ^ 2 := sq_nonneg _
    nlinarith [hstep, hsq]
  have hboundSide : ∑ c ∈ negSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      ≤ boundCeiling * middleForm := by
    rw [htwoFrames, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hsign : stressCoeff c < 0 := (Finset.mem_filter.mp hc).2
    have hstep := hbound c hsign
    have hsq : (0 : ℝ) ≤ (design.atom c ⬝ᵥ probe) ^ 2 := sq_nonneg _
    nlinarith [hstep, hsq]
  have hsplit : probe ⬝ᵥ ((subsetSum design posSide - 1) *ᵥ probe)
      = (∑ c ∈ posSide, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2)
        - ∑ c ∈ negSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [subsetSum_sub_one_eq_freeMass_sub_boundMass, Matrix.sub_mulVec, dotProduct_sub,
      weighted_atomForm_eq_on, weighted_atomForm_eq_on, compl_posSide_eq_negSide hfull]
  rw [hmiddleMatrix, hsplit]
  linarith

/-! ### The inverse form is antitone, and the middle inverse forms add to the rank -/

/-- The inverse form of a positive definite matrix is nonnegative. -/
theorem inverseForm_nonneg {gramMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hposDef : gramMat.PosDef) (source : Fin rank → ℝ) :
    0 ≤ source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
  have hunit : IsUnit gramMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  set dual : Fin rank → ℝ := gramMat⁻¹ *ᵥ source with hdual
  have hmulDual : gramMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gramMat hunit,
      Matrix.one_mulVec]
  have hform : source ⬝ᵥ dual = dual ⬝ᵥ (gramMat *ᵥ dual) := by
    rw [hmulDual, dotProduct_comm]
  rw [hform]
  have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposDef.posSemidef).2 dual
  rwa [star_trivial] at hstep

/-- **THE INVERSE FORM IS ANTITONE IN THE FORM.**  If the form of a scaled
positive definite matrix sits below the form of another, the inverse forms
reverse, with the scale inverted.  The proof is one Cauchy-Schwarz step in the
smaller metric, thus it never mentions eigenvalues and it never inverts a scaled
matrix. -/
theorem inverseForm_le_of_form_le_smul
    {bigMat middleMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hbig : bigMat.PosDef) (hmiddle : middleMat.PosDef) {level : ℝ} (hlevel : 0 < level)
    (hform : ∀ probe : Fin rank → ℝ,
      level * (probe ⬝ᵥ (middleMat *ᵥ probe)) ≤ probe ⬝ᵥ (bigMat *ᵥ probe))
    (source : Fin rank → ℝ) :
    source ⬝ᵥ (bigMat⁻¹ *ᵥ source)
      ≤ level⁻¹ * (source ⬝ᵥ (middleMat⁻¹ *ᵥ source)) := by
  have hunit : IsUnit bigMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hbig.det_pos)
  set dual : Fin rank → ℝ := bigMat⁻¹ *ᵥ source with hdual
  set bigForm : ℝ := source ⬝ᵥ (bigMat⁻¹ *ᵥ source) with hbigForm
  set middleInv : ℝ := source ⬝ᵥ (middleMat⁻¹ *ᵥ source) with hmiddleInv
  have hmulDual : bigMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv bigMat hunit,
      Matrix.one_mulVec]
  have hdualForm : dual ⬝ᵥ (bigMat *ᵥ dual) = bigForm := by
    rw [hmulDual, hbigForm, hdual, dotProduct_comm]
  have hpairing : source ⬝ᵥ dual = bigForm := rfl
  have hmiddleSmall : level * (dual ⬝ᵥ (middleMat *ᵥ dual)) ≤ bigForm := by
    rw [← hdualForm]; exact hform dual
  have hcauchy := dotProduct_sq_le_inverseForm_mul_form hmiddle source dual
  rw [hpairing, ← hmiddleInv] at hcauchy
  have hmiddleNonneg : 0 ≤ middleInv := inverseForm_nonneg hmiddle source
  by_cases hpos : 0 < bigForm
  case neg =>
    push Not at hpos
    have hnonneg : 0 ≤ level⁻¹ * middleInv :=
      mul_nonneg (le_of_lt (inv_pos.mpr hlevel)) hmiddleNonneg
    linarith
  case pos =>
    have hdualMiddle : 0 ≤ dual ⬝ᵥ (middleMat *ᵥ dual) := by
      have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hmiddle.posSemidef).2 dual
      rwa [star_trivial] at hstep
    have hchain : level * bigForm ^ 2 ≤ middleInv * bigForm := by
      nlinarith [hcauchy, hmiddleSmall, hmiddleNonneg, hlevel, hdualMiddle]
    have hcancel : level * bigForm ≤ middleInv :=
      le_of_mul_le_mul_right (by nlinarith [hchain]) hpos
    have hscaled : level⁻¹ * (level * bigForm) ≤ level⁻¹ * middleInv :=
      mul_le_mul_of_nonneg_left hcancel (inv_pos.mpr hlevel).le
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlevel), one_mul] at hscaled

/-- **THE MIDDLE BUDGET.**  The stress-weighted inverse forms of the middle
matrix, summed over the positive side, equal the rank exactly.  This is the
trace of the identity, read through the middle matrix, and it is the one exact
identity the mass gap can be measured against. -/
theorem sum_stress_middleInverseForm_eq_rank (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hmiddle : (∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
      stressCoeff c • atomMatrix (design.atom c)).PosDef) :
    ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c * (design.atom c ⬝ᵥ ((∑ d ∈ Finset.univ.filter
          fun d => 0 < stressCoeff d,
            stressCoeff d • atomMatrix (design.atom d))⁻¹ *ᵥ design.atom c))
      = (rank : ℝ) := by
  classical
  set posSide := Finset.univ.filter (fun c => 0 < stressCoeff c) with hposSide
  set middleMat : Matrix (Fin rank) (Fin rank) ℝ :=
    ∑ c ∈ posSide, stressCoeff c • atomMatrix (design.atom c) with hmiddleMat
  have hunit : IsUnit middleMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hmiddle.det_pos)
  have hterm : ∀ c ∈ posSide,
      stressCoeff c * (design.atom c ⬝ᵥ (middleMat⁻¹ *ᵥ design.atom c))
        = Matrix.trace (middleMat⁻¹ * (stressCoeff c • atomMatrix (design.atom c))) := by
    intro c _
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  rw [Finset.sum_congr rfl hterm, ← Matrix.trace_sum, ← Matrix.mul_sum, ← hmiddleMat,
    Matrix.nonsing_inv_mul middleMat hunit, Matrix.trace_one, Fintype.card_fin]

/-- **THE MASS-GAP FIRING OF THE DROP.**  When the level difference times the
positive side's stress mass exceeds the rank, the positive side carries a label
of pivot value less than one, thus it shrinks.

The three ingredients are exactly the three of Part 4: the Loewner bound, the
antitone inverse form, and the middle budget.  Nothing else about the design is
used, and the estimate is scale invariant, because rescaling the stress divides
the levels and multiplies the mass by the same factor. -/
theorem exists_pivot_lt_one_of_massGap (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (hlevel : boundCeiling < freeFloor)
    (hmass : (rank : ℝ) < (freeFloor - boundCeiling)
      * ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c), stressCoeff c) :
    ∃ label ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      pivot design (Finset.univ.filter fun c => 0 < stressCoeff c) label < 1 := by
  classical
  set posSide := Finset.univ.filter (fun c => 0 < stressCoeff c) with hposSide
  set middleMat : Matrix (Fin rank) (Fin rank) ℝ :=
    ∑ c ∈ posSide, stressCoeff c • atomMatrix (design.atom c) with hmiddleMat
  set levelGap : ℝ := freeFloor - boundCeiling with hlevelGap
  have hlevelPos : 0 < levelGap := by rw [hlevelGap]; linarith
  have hspans : ∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
    pos_side_spans design.atom
      (fun _probe hprobe => weightedDesign_atoms_span design hprobe) hstress hfull
  have hmiddlePosDef : middleMat.PosDef := posDef_posSideSum_of_spans design.atom hspans
  have hgapPosDef : (subsetSum design posSide - 1).PosDef :=
    posDef_gap_posSide_of_massGap design hstress hfull
      ⟨freeFloor, boundCeiling, hfree, hbound, hlevel⟩
  have hloewner : ∀ probe : Fin rank → ℝ,
      levelGap * (probe ⬝ᵥ (middleMat *ᵥ probe))
        ≤ probe ⬝ᵥ ((subsetSum design posSide - 1) *ᵥ probe) := fun probe =>
    massGap_gap_form_ge design hstress hfull hfree hbound probe
  have hpivotBound : ∀ c ∈ posSide,
      pivot design posSide c
        ≤ levelGap⁻¹ * (design.atom c ⬝ᵥ (middleMat⁻¹ *ᵥ design.atom c)) := by
    intro c _
    rw [pivot_eq_inverseForm]
    exact inverseForm_le_of_form_le_smul hgapPosDef hmiddlePosDef hlevelPos hloewner
      (design.atom c)
  have hbudget := sum_stress_middleInverseForm_eq_rank design (stressCoeff := stressCoeff)
    hmiddlePosDef
  by_contra hnone
  push Not at hnone
  have hbig : ∑ c ∈ posSide, stressCoeff c
      ≤ ∑ c ∈ posSide,
          stressCoeff c * (levelGap⁻¹
            * (design.atom c ⬝ᵥ (middleMat⁻¹ *ᵥ design.atom c))) := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hsign : 0 < stressCoeff c := (Finset.mem_filter.mp hc).2
    have hone : (1 : ℝ) ≤ pivot design posSide c := hnone c hc
    nlinarith [hpivotBound c hc, hsign, hone]
  have hrewrite : ∑ c ∈ posSide,
      stressCoeff c * (levelGap⁻¹
        * (design.atom c ⬝ᵥ (middleMat⁻¹ *ᵥ design.atom c)))
      = levelGap⁻¹ * (rank : ℝ) := by
    rw [← hbudget, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hrewrite] at hbig
  have hfinal : levelGap * ∑ c ∈ posSide, stressCoeff c ≤ (rank : ℝ) := by
    have hstep := mul_le_mul_of_nonneg_left hbig hlevelPos.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlevelPos), one_mul] at hstep
    exact hstep
  linarith

/-! ### The trace reading of the same bound

The pivot estimate is one axis of a stronger statement: the whole inverse gap is
priced by the middle matrix.  Summing the antitone inverse form over the standard
axes gives the trace bound, and the trace bound feeds the pigeonhole of Part 2
directly. -/

/-- The form of a matrix against a standard axis is its diagonal entry. -/
theorem axisForm_eq_diag (gramMat : Matrix (Fin rank) (Fin rank) ℝ)
    (index : Fin rank) :
    (Pi.single index (1 : ℝ)) ⬝ᵥ (gramMat *ᵥ Pi.single index (1 : ℝ))
      = gramMat index index := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']

/-- The trace is the sum of the axis forms. -/
theorem trace_eq_sum_axisForm (gramMat : Matrix (Fin rank) (Fin rank) ℝ) :
    Matrix.trace gramMat
      = ∑ index, (Pi.single index (1 : ℝ)) ⬝ᵥ (gramMat *ᵥ Pi.single index (1 : ℝ)) := by
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun index _ => (axisForm_eq_diag gramMat index).symm

/-- **THE INVERSE TRACE IS ANTITONE IN THE FORM.**  The axiswise antitone bound,
summed.  This is the tool the pigeonhole of Part 2 consumes. -/
theorem trace_inv_le_of_form_le_smul
    {bigMat middleMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hbig : bigMat.PosDef) (hmiddle : middleMat.PosDef) {level : ℝ} (hlevel : 0 < level)
    (hform : ∀ probe : Fin rank → ℝ,
      level * (probe ⬝ᵥ (middleMat *ᵥ probe)) ≤ probe ⬝ᵥ (bigMat *ᵥ probe)) :
    Matrix.trace bigMat⁻¹ ≤ level⁻¹ * Matrix.trace middleMat⁻¹ := by
  rw [trace_eq_sum_axisForm bigMat⁻¹, trace_eq_sum_axisForm middleMat⁻¹,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun index _ =>
    inverseForm_le_of_form_le_smul hbig hmiddle hlevel hform (Pi.single index (1 : ℝ))

/-- **THE SECOND MASS-GAP FIRING.**  When the middle matrix has small inverse
trace relative to the level difference and the positive side's excess card, the
positive side drops a label.  This criterion is independent of
`Gtz.exists_pivot_lt_one_of_massGap`: the first reads the stress mass, the second
reads the middle spectrum. -/
theorem exists_pivot_lt_one_of_massGap_trace (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (hlevel : boundCeiling < freeFloor)
    (htrace : (freeFloor - boundCeiling)⁻¹
        * Matrix.trace (∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
            stressCoeff c • atomMatrix (design.atom c))⁻¹
      < ((Finset.univ.filter fun c => 0 < stressCoeff c).card : ℝ) - rank) :
    ∃ label ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      pivot design (Finset.univ.filter fun c => 0 < stressCoeff c) label < 1 := by
  classical
  set posSide := Finset.univ.filter (fun c => 0 < stressCoeff c) with hposSide
  set middleMat : Matrix (Fin rank) (Fin rank) ℝ :=
    ∑ c ∈ posSide, stressCoeff c • atomMatrix (design.atom c) with hmiddleMat
  have hlevelPos : 0 < freeFloor - boundCeiling := by linarith
  have hspans : ∀ probe : Fin rank → ℝ,
      (∀ c, 0 < stressCoeff c → design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
    pos_side_spans design.atom
      (fun _probe hprobe => weightedDesign_atoms_span design hprobe) hstress hfull
  have hmiddlePosDef : middleMat.PosDef := posDef_posSideSum_of_spans design.atom hspans
  have hgapPosDef : (subsetSum design posSide - 1).PosDef :=
    posDef_gap_posSide_of_massGap design hstress hfull
      ⟨freeFloor, boundCeiling, hfree, hbound, hlevel⟩
  refine exists_pivot_lt_one_of_trace_inv_lt design posSide hgapPosDef ?_
  refine lt_of_le_of_lt (trace_inv_le_of_form_le_smul hgapPosDef hmiddlePosDef
    hlevelPos (fun probe => massGap_gap_form_ge design hstress hfull hfree hbound probe))
    htrace

/-! ### The ratio criterion

The mass gap is a separation of two families of ratios.  Cross-multiplied it is
division free, and in that shape it is what a numeric probe checks. -/

/-- **THE MASS GAP SEPARATES THE RATIOS.**  Every bound-mass ratio on the
negative side sits strictly below every free-mass ratio on the positive side.
The statement is cross-multiplied, thus no division and no positivity side
condition appears. -/
theorem crossRatio_lt_of_hasStressMassGap (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} (hgap : HasStressMassGap design stressCoeff)
    {boundLabel freeLabel : Fin size} (hbound : stressCoeff boundLabel < 0)
    (hfree : 0 < stressCoeff freeLabel) :
    design.weight boundLabel * stressCoeff freeLabel
      < (1 - design.weight freeLabel) * (-stressCoeff boundLabel) := by
  obtain ⟨freeFloor, boundCeiling, hfreeBound, hboundBound, hlevel⟩ := hgap
  have hboundStep := hboundBound boundLabel hbound
  have hfreeStep := hfreeBound freeLabel hfree
  have hnegPos : 0 < -stressCoeff boundLabel := by linarith
  have hprod : 0 < stressCoeff freeLabel * (-stressCoeff boundLabel) :=
    mul_pos hfree hnegPos
  have hlower : design.weight boundLabel * stressCoeff freeLabel
      ≤ boundCeiling * (-stressCoeff boundLabel) * stressCoeff freeLabel :=
    mul_le_mul_of_nonneg_right hboundStep hfree.le
  have hupper : freeFloor * stressCoeff freeLabel * (-stressCoeff boundLabel)
      ≤ (1 - design.weight freeLabel) * (-stressCoeff boundLabel) :=
    mul_le_mul_of_nonneg_right hfreeStep hnegPos.le
  have hmiddle : boundCeiling * (-stressCoeff boundLabel) * stressCoeff freeLabel
      < freeFloor * stressCoeff freeLabel * (-stressCoeff boundLabel) := by
    nlinarith [hprod, sub_pos.mpr hlevel]
  linarith

/-- The mass gap forces a positive level pair: the ceiling is positive, because a
negative-side weight is positive. -/
theorem boundCeiling_pos_of_hasStressMassGap (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {boundCeiling : ℝ}
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    {boundLabel : Fin size} (hnegative : stressCoeff boundLabel < 0) :
    0 < boundCeiling := by
  have hstep := hbound boundLabel hnegative
  have hweight := design.weight_pos boundLabel
  nlinarith [hstep, hweight, neg_pos.mpr hnegative]

/-! ## Part 5: the tie-carrying recut of the arm -/

/-- **THE RECUT ARM.**  The shipped `Gtz.MassGapSideIsRankSized` asks for a
rank-sized strictly dominating subset out of thin air.  Its ONLY consumer holds a
TIE and a PRIMITIVE design at the moment of use, and it uses the returned subset
for one purpose: to contradict the tie.  This Prop carries both hypotheses and
asks only for the contradiction. -/
def TieFreeMassGappedStress (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
    (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 →
    (∀ c, stressCoeff c ≠ 0) →
    IsPrimitiveDesign design →
    IsTie design →
    HasStressMassGap design stressCoeff → False

/-- **THE RECUT IS WEAKER.**  Anything the shipped arm proves, the recut arm
proves, because a tie forbids exactly the subset the shipped arm returns. -/
theorem tieFreeMassGappedStress_of_massGapSideIsRankSized
    (hmassGap : MassGapSideIsRankSized size rank) : TieFreeMassGappedStress size rank := by
  intro design stressCoeff hstress hfull _hprimitive htie hgap
  obtain ⟨dominating, hcard, hposDef⟩ := hmassGap design stressCoeff hstress hfull hgap
  exact htie.2 dominating hcard hposDef

/-- The rank-three instance of the recut arm, from the shipped rank-three
theorem. -/
theorem tieFreeMassGappedStress_six_three : TieFreeMassGappedStress 6 3 :=
  tieFreeMassGappedStress_of_massGapSideIsRankSized massGapSideIsRankSized_sixThree

/-! ### What closes the recut arm, and where the rank-four residue lives -/

/-- **THE RANK-THREE MECHANISM, AT EVERY RANK.**  When the positive side of the
mass-gapped stress is already rank-sized, the firing contradicts the tie on the
spot.  This is exactly what happens at the rank-three deciding cell, where the
split is forced to be three and three. -/
theorem false_of_tie_of_massGap_of_posSideCard (design : WeightedDesign size rank)
    (htie : IsTie design) {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) (hgap : HasStressMassGap design stressCoeff)
    (hcard : (Finset.univ.filter fun c => 0 < stressCoeff c).card = rank) : False :=
  htie.2 _ hcard (posDef_gap_posSide_of_massGap design hstress hfull hgap)

/-- The recut arm at a cell where every full-support stress splits evenly. -/
theorem tieFreeMassGappedStress_of_posSideCard
    (hcard : ∀ (design : WeightedDesign size rank) (stressCoeff : Fin size → ℝ),
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → (∀ c, stressCoeff c ≠ 0) →
        (Finset.univ.filter fun c => 0 < stressCoeff c).card = rank) :
    TieFreeMassGappedStress size rank :=
  fun design stressCoeff hstress hfull _hprimitive htie hgap =>
    false_of_tie_of_massGap_of_posSideCard design htie hstress hfull hgap
      (hcard design stressCoeff hstress hfull)

/-- The recut arm from the drop condition. -/
theorem tieFreeMassGappedStress_of_pivotDrop (hdrop : PivotDropAtRank size rank) :
    TieFreeMassGappedStress size rank :=
  tieFreeMassGappedStress_of_massGapSideIsRankSized
    (massGapSideIsRankSized_of_pivotDrop hdrop)

/-- **THE SHARP INEQUALITY A TIE FORCES ON A ONE-OVER SIDE.**  When the positive
side carries exactly one label more than the rank, one drop reaches card `rank`,
thus the tie caps the mass product by the rank.  This is a NEW quantitative
constraint on a tied design: it is not a domination statement, it is a bound on
the levels of every mass-gapped stress the design can carry. -/
theorem massProduct_le_rank_of_tie_of_posSideCard_succ (design : WeightedDesign size rank)
    (htie : IsTie design) {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (hlevel : boundCeiling < freeFloor)
    (hcard : (Finset.univ.filter fun c => 0 < stressCoeff c).card = rank + 1) :
    (freeFloor - boundCeiling)
        * ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c), stressCoeff c
      ≤ (rank : ℝ) := by
  classical
  by_contra hbig
  push Not at hbig
  obtain ⟨label, hmem, hpivot⟩ := exists_pivot_lt_one_of_massGap design hstress hfull
    hfree hbound hlevel hbig
  refine htie.2 ((Finset.univ.filter fun c => 0 < stressCoeff c).erase label) ?_
    (posDef_erase_of_pivot_lt_one design hmem
      (posDef_gap_posSide_of_massGap design hstress hfull
        ⟨freeFloor, boundCeiling, hfree, hbound, hlevel⟩) hpivot)
  rw [Finset.card_erase_of_mem hmem, hcard]
  omega

/-- **THE TRACE COUNTERPART.**  The same one-over side forces the middle matrix
to carry at least the level difference in inverse trace. -/
theorem traceMiddle_ge_of_tie_of_posSideCard_succ (design : WeightedDesign size rank)
    (htie : IsTie design) {stressCoeff : Fin size → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (hlevel : boundCeiling < freeFloor)
    (hcard : (Finset.univ.filter fun c => 0 < stressCoeff c).card = rank + 1) :
    (1 : ℝ) ≤ (freeFloor - boundCeiling)⁻¹
      * Matrix.trace (∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
          stressCoeff c • atomMatrix (design.atom c))⁻¹ := by
  classical
  by_contra hsmall
  push Not at hsmall
  have hwindow : (freeFloor - boundCeiling)⁻¹
      * Matrix.trace (∑ c ∈ Finset.univ.filter fun c => 0 < stressCoeff c,
          stressCoeff c • atomMatrix (design.atom c))⁻¹
      < ((Finset.univ.filter fun c => 0 < stressCoeff c).card : ℝ) - rank := by
    rw [hcard]
    push_cast
    linarith
  obtain ⟨label, hmem, hpivot⟩ := exists_pivot_lt_one_of_massGap_trace design hstress
    hfull hfree hbound hlevel hwindow
  refine htie.2 ((Finset.univ.filter fun c => 0 < stressCoeff c).erase label) ?_
    (posDef_erase_of_pivot_lt_one design hmem
      (posDef_gap_posSide_of_massGap design hstress hfull
        ⟨freeFloor, boundCeiling, hfree, hbound, hlevel⟩) hpivot)
  rw [Finset.card_erase_of_mem hmem, hcard]
  omega

/-! ### The rank-four residue, enumerated

At the rank-four deciding cell the admissible split window is `[4,6]`, thus the
positive side carries four, five or six labels.  The card-four case closes on the
spot.  Everything the recut arm still owes at rank four is therefore the two
cards five and six. -/

/-- The positive side of a full-support stress of a `(10,4)` design carries four,
five or six labels. -/
theorem posSideCard_ten_four (design : WeightedDesign 10 4) {stressCoeff : Fin 10 → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) :
    (Finset.univ.filter fun c => 0 < stressCoeff c).card = 4
      ∨ (Finset.univ.filter fun c => 0 < stressCoeff c).card = 5
      ∨ (Finset.univ.filter fun c => 0 < stressCoeff c).card = 6 := by
  classical
  obtain ⟨hposCard, hnegCard⟩ := design_rank_le_card_sides design hstress hfull
  have hsum := sideCards_add_le (n := 10) stressCoeff
  omega

/-- **THE RANK-FOUR RESIDUE.**  The recut arm at the rank-four deciding cell
reduces to the two big cards.  A successor never has to look at a rank-sized
positive side. -/
theorem tieFreeMassGappedStress_ten_four_of_bigSide
    (hbigSide : ∀ (design : WeightedDesign 10 4) (stressCoeff : Fin 10 → ℝ),
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → (∀ c, stressCoeff c ≠ 0) →
        IsPrimitiveDesign design → IsTie design → HasStressMassGap design stressCoeff →
          4 < (Finset.univ.filter fun c => 0 < stressCoeff c).card → False) :
    TieFreeMassGappedStress 10 4 := by
  classical
  intro design stressCoeff hstress hfull hprimitive htie hgap
  rcases posSideCard_ten_four design hstress hfull with hfour | hfive | hsix
  · exact false_of_tie_of_massGap_of_posSideCard design htie hstress hfull hgap hfour
  · exact hbigSide design stressCoeff hstress hfull hprimitive htie hgap (by omega)
  · exact hbigSide design stressCoeff hstress hfull hprimitive htie hgap (by omega)

/-- **SUB-ARM (ii-a) FROM THE RECUT.**  The verbatim replay of
`Gtz.balancedFullSupportArmAt_of_selection` with the recut arm in place of the
shipped one.  The two mass-gap orientations both discharge through the recut,
because the negated stress is a stress and the design and the tie are the same.
-/
theorem balancedFullSupportArmAt_of_tieFree
    (htieFree : TieFreeMassGappedStress size rank)
    (hselection : BalancedStratumSelectionAtRank size rank) :
    BalancedFullSupportArmAt size rank := by
  classical
  intro design stressCoeff hstress hfull htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have hnostrict := htie.2
  by_cases hgapPos : HasStressMassGap design stressCoeff
  · exact htieFree design stressCoeff hstress hfull hprimitive htie hgapPos
  by_cases hgapNeg : HasStressMassGap design (-stressCoeff)
  · exact htieFree design (-stressCoeff) (stress_of_neg_stress hstress)
      (fun c => by simp only [Pi.neg_apply]; exact neg_ne_zero.mpr (hfull c))
      hprimitive htie hgapNeg
  by_cases hbudget : ∀ selected : Finset (Fin size), selected.card = rank →
      ¬ HasFreeMassBudget design selected
  · obtain ⟨dominating, hcard, hposDef⟩ := hselection design stressCoeff hstress hfull
      hprimitive hgapPos hgapNeg hbudget
    exact hnostrict dominating hcard hposDef
  · push Not at hbudget
    obtain ⟨selected, hcard, hbudgetFires⟩ := hbudget
    exact hnostrict selected hcard
      (posDef_gap_of_freeMassBudget design selected hbudgetFires.1 hbudgetFires.2)

/-- **ARM (ii) FROM THE RECUT RESIDUALS.**  The balanced arm at general rank,
with the deepest residual replaced by its tie-carrying form. -/
theorem balancedArmAt_of_tieFreeResiduals
    (htieFree : TieFreeMassGappedStress size rank)
    (hselection : BalancedStratumSelectionAtRank size rank)
    (hpartialArm : BalancedPartialSupportArmAt size rank) :
    BalancedArmAt size rank :=
  balancedArmAt_of_split (balancedFullSupportArmAt_of_tieFree htieFree hselection)
    hpartialArm

/-- **THE RECUT CHAIN IS THE RIGHT ONE: ITS RANK-THREE INSTANCE IS CLOSED.**  The
rank-three balanced arm comes out of the recut residuals with no appeal to the
rank-three capstone, exactly as it did before the recut. -/
theorem thresholdBalancedArm_three_of_tieFreeResiduals : ThresholdBalancedArm 3 :=
  balancedArmAt_of_tieFreeResiduals tieFreeMassGappedStress_six_three
    ((balancedStratumSelectionAtRank_three 6).mpr balancedStratumSelection_six_holds)
    balancedPartialSupportArm_sixThree

/-- **THE DECIDING CELL FROM THE RECUT RESIDUALS.**  Weighted GTZ at `(6,3)` on
the stress-free arm, the degenerate arm, the closed rank-three selection, and the
recut mass-gap arm.  No reach, no anchor, no icosahedron. -/
theorem gtzWeighted_six_three_of_tieFreeResiduals (hfreeArm : ThresholdStressFreeArm 3)
    (hdegenerateArm : ThresholdDegenerateArm 3) : GtzWeighted 6 3 :=
  GeneralRankReach.gtzWeighted_six_three_of_arms hfreeArm
    thresholdBalancedArm_three_of_tieFreeResiduals hdegenerateArm

/-- **THE THRESHOLD OBLIGATION ON THE RECUT LIST.**  The exact list a successor
must close at rank four and up, with the deepest arm now carrying a tie and a
primitive design. -/
theorem thresholdCellHingeRankFourAndUp_of_tieFreeResiduals
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (htieFree : ∀ rank : ℕ, 4 ≤ rank → TieFreeMassGappedStress (thresholdSize rank) rank)
    (hselection : ∀ rank : ℕ, 4 ≤ rank →
      BalancedStratumSelectionAtRank (thresholdSize rank) rank)
    (hpartialArm : ∀ rank : ℕ, 4 ≤ rank →
      BalancedPartialSupportArmAt (thresholdSize rank) rank)
    (hdegenerateArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdDegenerateArm rank) :
    ∀ rank : ℕ, 4 ≤ rank →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  refine thresholdCellHingeRankFourAndUp_of_arms hfreeArm (fun rank hrank => ?_)
    hdegenerateArm
  exact balancedArmAt_of_tieFreeResiduals (htieFree rank hrank) (hselection rank hrank)
    (hpartialArm rank hrank)

/-- **THE RECUT UNDER THE LADDER'S OWN INDUCTION HYPOTHESIS.**  The degenerate arm
is spent through the previous rank, exactly as in the shipped map, and the
balanced arm runs on the recut list. -/
theorem thresholdCellHinge_of_tieFreeResiduals_withPredecessorRank
    (hfreeArm : ∀ rank : ℕ, 4 ≤ rank → ThresholdStressFreeArm rank)
    (htieFree : ∀ rank : ℕ, 4 ≤ rank → TieFreeMassGappedStress (thresholdSize rank) rank)
    (hselection : ∀ rank : ℕ, 4 ≤ rank →
      BalancedStratumSelectionAtRank (thresholdSize rank) rank)
    (hpartialArm : ∀ rank : ℕ, 4 ≤ rank →
      BalancedPartialSupportArmAt (thresholdSize rank) rank)
    (hframe : ∀ rank : ℕ, 4 ≤ rank → HyperplaneFrameExists rank)
    (haugment : ∀ rank : ℕ, 4 ≤ rank →
      DegeneratePoleAugmentation (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
        IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor design htie
  refine thresholdCellHinge_of_arms rank (hfreeArm rank hrank) ?_ ?_ design htie
  · exact balancedArmAt_of_tieFreeResiduals (htieFree rank hrank) (hselection rank hrank)
      (hpartialArm rank hrank)
  · exact degenerateArmAt_of_predecessorRank hpredecessor (hframe rank hrank)
      (haugment rank hrank)

/-! ## Part 6: the obstruction, exactly

Three rational atoms in two dimensions.  Their sum dominates STRICTLY, and every
pair among them fails to dominate strictly.  Thus no argument that only reads
"the returned set dominates strictly" can shrink that set to card `rank`.

This is the rational cousin of the tight-frame configuration -- four unit vectors
in three dimensions with `subsetSum = (4/3) * 1` and every triple at smallest
eigenvalue `1/3`.  The witness below has the same shape and exact arithmetic. -/

/-- The three obstruction atoms: one along the first axis, two symmetric about
it. -/
noncomputable def obstructionAtom : Fin 3 → Fin 2 → ℝ :=
  ![![1, 0], ![1 / 2, 1], ![1 / 2, -1]]

/-- The gap of every pair of obstruction atoms has nonpositive determinant, thus
no pair dominates strictly. -/
theorem det_obstruction_pair_nonpos (firstLabel secondLabel : Fin 3)
    (hdistinct : firstLabel ≠ secondLabel) :
    (atomMatrix (obstructionAtom firstLabel)
        + atomMatrix (obstructionAtom secondLabel) - 1).det ≤ 0 := by
  fin_cases firstLabel <;> fin_cases secondLabel <;>
    simp_all [obstructionAtom, atomMatrix, Matrix.det_fin_two, Matrix.sub_apply] <;>
    norm_num

/-- The three obstruction atoms dominate strictly. -/
theorem posDef_obstruction_total :
    ((∑ c, atomMatrix (obstructionAtom c)) - 1).PosDef := by
  have hentry : (∑ c, atomMatrix (obstructionAtom c)) - 1
      = Matrix.of ![![1 / 2, 0], ![0, 1]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [obstructionAtom, atomMatrix, Fin.sum_univ_three]
    all_goals norm_num
  rw [hentry]
  have hsymm : (Matrix.of ![![(1 : ℝ) / 2, 0], ![0, 1]])ᵀ
      = Matrix.of ![![(1 : ℝ) / 2, 0], ![0, 1]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  have hform : star probe ⬝ᵥ (Matrix.of ![![(1 : ℝ) / 2, 0], ![0, 1]] *ᵥ probe)
      = (1 / 2) * probe 0 ^ 2 + probe 1 ^ 2 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply]
    ring
  rw [hform]
  have hne : probe 0 ≠ 0 ∨ probe 1 ≠ 0 := by
    by_contra hboth
    push Not at hboth
    exact hprobe (funext fun i => by fin_cases i <;> simp [hboth.1, hboth.2])
  rcases hne with hzero | hone
  · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 1),
      lt_of_le_of_ne (sq_nonneg (probe 0)) (pow_ne_zero 2 hzero).symm]
  · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 1),
      lt_of_le_of_ne (sq_nonneg (probe 1)) (pow_ne_zero 2 hone).symm]

/-- **THE SHRINK ROUTE IS FALSE, NOT MERELY UNPROVED.**  Three atoms in two
dimensions whose total dominates strictly while no rank-sized subset of them
does.  Thus `Gtz.MassGapSideIsRankSized` cannot be reached from the mass-gap
firing by any argument that forgets the design and reads only the returned set.
-/
theorem exists_posDef_without_rankSized_posDef_subset :
    ∃ atomFamily : Fin 3 → Fin 2 → ℝ,
      ((∑ c, atomMatrix (atomFamily c)) - 1).PosDef
        ∧ ∀ selected : Finset (Fin 3), selected.card = 2 →
            ¬ ((∑ c ∈ selected, atomMatrix (atomFamily c)) - 1).PosDef := by
  classical
  refine ⟨obstructionAtom, posDef_obstruction_total, fun selected hcard hposDef => ?_⟩
  obtain ⟨firstLabel, secondLabel, hdistinct, hpair⟩ := Finset.card_eq_two.mp hcard
  rw [hpair, Finset.sum_pair hdistinct] at hposDef
  exact absurd hposDef.det_pos
    (not_lt.mpr (det_obstruction_pair_nonpos firstLabel secondLabel hdistinct))

/-- **THE SAME OBSTRUCTION, READ THROUGH THE PIVOT.**  At the obstruction the
pivot values of a strictly dominating set are all at least one, thus
`Gtz.PivotDropAtRank` is not a law about sets.  It is a statement about designs,
and the design is what a successor must use. -/
theorem obstruction_pivot_ge_one (label : Fin 3) :
    (1 : ℝ) ≤ obstructionAtom label
      ⬝ᵥ (((∑ c, atomMatrix (obstructionAtom c)) - 1)⁻¹ *ᵥ obstructionAtom label) := by
  have hinv : ((∑ c, atomMatrix (obstructionAtom c)) - 1)⁻¹
      = Matrix.of ![![2, 0], ![0, 1]] := by
    have hentry : (∑ c, atomMatrix (obstructionAtom c)) - 1
        = Matrix.of ![![1 / 2, 0], ![0, 1]] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [obstructionAtom, atomMatrix, Fin.sum_univ_three]
      all_goals norm_num
    rw [hentry]
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hinv]
  fin_cases label <;>
    simp [obstructionAtom, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

end Gtz
