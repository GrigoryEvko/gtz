import Gtz.Wave.SharedPrivateKernelChain
import Gtz.Wave.SharedPrivateCaptureLeak

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The confinement kill — the confined kernel, the dead propagation and
the parallel columns

The kernel chain kills a chain that is **longer** than the complementary
trace.  One member of that chain is always spent on an escape: the
residual of an atom, whose only certified pivot is its own carrier.

This module removes that member.  A chain of kernel witnesses that all
vanish at ONE slot spans the whole kernel there, thus the axis of that
slot sits in the image of the read idempotent and the diagonal entry is
one.  A symmetric idempotent with a diagonal entry one has a zero row
off that slot, thus it reads every vector at that slot exactly.  The
carrier read then asks for the shifted weight one, which the negative
chart value refuses.  **Thus a confined chain kills at the length of
the complementary trace, one member below the plain chain.**

Three more laws come from the same column calculus.

* **The dead propagation.**  A boundary read is a kernel vector, thus
  the columns of its carrier carry a relation with every coefficient
  nonzero.  If every carrier slot except one has a vanishing column,
  the last column vanishes too.  An interior atom cannot carry a slot
  with a vanishing column, thus **a boundary carrier never holds
  exactly one live slot**.
* **The interior leak.**  The fixed part of an interior read has the
  shifted weight over six as its energy, and the carrier holds only the
  square of that weight.  The difference is positive, thus the fixed
  part is nonzero off the carrier, and a vanishing column kills it at a
  dead slot.  **Thus every interior atom misses a live slot.**
* **The parallel columns.**  A boundary atom with a two-slot carrier
  makes the two columns proportional.  If every column is a multiple of
  one column, the trace is one or zero, which the trace two refuses.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.offDiag_eq_zero_of_diag_eq_one`,
  `Gtz.mulVec_apply_of_diag_eq_one` — **THE DIAGONAL-ONE ROW LAW.**
* `Gtz.false_of_diag_eq_one_of_read` — the read refuses a diagonal one.
* `Gtz.diag_eq_zero_of_confined_family` — **THE CONFINEMENT LAW.**
* `Gtz.trace_eq_one_or_zero_of_parallel_columns`,
  `Gtz.false_of_parallel_columns` — **THE PARALLEL COLUMN COLLAPSE.**
* `Gtz.witnessVector`, `Gtz.SharedPrivateData.exists_witness_family` —
  the shared skeleton of the two chain kills.
* `Gtz.SharedPrivateData.false_of_confined_chain` — **THE CONFINEMENT
  KILL**, at every basis count and at every trace.
* `Gtz.SharedPrivateData.false_of_confined_private_pair`,
  `Gtz.SharedPrivateData.false_of_confined_boundary_triple` — the two
  corollaries the basis-count-five census consumes.
* `Gtz.SharedPrivateData.column_eq_zero_of_dead_slot`,
  `Gtz.SharedPrivateData.false_of_boundary_dead_cocarrier`,
  `Gtz.SharedPrivateData.exists_live_cocarrier` — **THE DEAD
  PROPAGATION.**
* `Gtz.SharedPrivateData.exists_live_slot_offCarrier` — **THE INTERIOR
  LEAK.**
* `Gtz.SharedPrivateData.liveSlots`,
  `Gtz.SharedPrivateData.multiplicity_lt_liveSlots_card` — **THE
  INTERIOR MULTIPLICITY CAP.**
* `Gtz.SharedPrivateData.two_le_live_cocarrier_card` — the cocarrier
  pair.
* `Gtz.SharedPrivateData.column_smul_of_boundary_pair`,
  `Gtz.SharedPrivateData.false_of_boundary_pair_star` — the star kill.
* `Gtz.SharedPrivateBoundaryFiveConfinedClosed` with
  `Gtz.sharedPrivateBoundaryFiveCoreClosed_of_confined` — the residue
  after the confinement layer.
* `Gtz.sharedPrivateKilled_of_confined_strata`,
  `Gtz.rankFourSharedPrivateClosed_of_confined_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_confined_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_confined_strata` — the dispatches,
  with the deficit stratum discharged.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the diagonal-one row law -/

/-- **THE DIAGONAL-ONE ROW LAW.**  A symmetric idempotent with a
diagonal entry one has a vanishing row off that slot.  The idempotence
prices the row energy by the diagonal entry, and the diagonal entry
alone already exhausts it. -/
theorem offDiag_eq_zero_of_diag_eq_one {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {pivotSlot : Fin slotCount}
    (hone : S pivotSlot pivotSlot = 1) {otherSlot : Fin slotCount}
    (hne : otherSlot ≠ pivotSlot) : S pivotSlot otherSlot = 0 := by
  classical
  have hsymmEntry : ∀ rowIdx colIdx : Fin slotCount, S colIdx rowIdx = S rowIdx colIdx := by
    intro rowIdx colIdx
    have hentry := congrFun (congrFun hsymm rowIdx) colIdx
    rwa [Matrix.transpose_apply] at hentry
  have hentry := congrFun (congrFun hidem pivotSlot) pivotSlot
  rw [Matrix.mul_apply] at hentry
  have hsq : (∑ midSlot, S pivotSlot midSlot * S pivotSlot midSlot) = 1 := by
    rw [← hone, ← hentry]
    exact Finset.sum_congr rfl fun midSlot _ => by rw [hsymmEntry midSlot pivotSlot]
  have hsplit : S pivotSlot pivotSlot * S pivotSlot pivotSlot
      + ∑ midSlot ∈ (Finset.univ : Finset (Fin slotCount)).erase pivotSlot,
          S pivotSlot midSlot * S pivotSlot midSlot
      = ∑ midSlot, S pivotSlot midSlot * S pivotSlot midSlot :=
    Finset.add_sum_erase _ (fun midSlot => S pivotSlot midSlot * S pivotSlot midSlot)
      (Finset.mem_univ pivotSlot)
  have hrest : (∑ midSlot ∈ (Finset.univ : Finset (Fin slotCount)).erase pivotSlot,
      S pivotSlot midSlot * S pivotSlot midSlot) = 0 := by
    rw [hone] at hsplit
    linarith [hsq, hsplit]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun midSlot (_ : midSlot ∈ (Finset.univ : Finset (Fin slotCount)).erase pivotSlot) =>
      mul_self_nonneg (S pivotSlot midSlot))).mp hrest otherSlot
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ otherSlot⟩)
  exact mul_self_eq_zero.mp hterm

/-- **THE EXACT READ.**  A symmetric idempotent with a diagonal entry
one reads every vector at that slot exactly. -/
theorem mulVec_apply_of_diag_eq_one {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {pivotSlot : Fin slotCount}
    (hone : S pivotSlot pivotSlot = 1) (vec : Fin slotCount → ℝ) :
    (S *ᵥ vec) pivotSlot = vec pivotSlot := by
  classical
  calc (S *ᵥ vec) pivotSlot = ∑ midSlot, S pivotSlot midSlot * vec midSlot := rfl
    _ = ∑ midSlot, (if midSlot = pivotSlot then vec midSlot else 0) := by
        refine Finset.sum_congr rfl fun midSlot _ => ?_
        by_cases hmid : midSlot = pivotSlot
        · rw [if_pos hmid, hmid, hone, one_mul]
        · rw [if_neg hmid, offDiag_eq_zero_of_diag_eq_one hsymm hidem hone hmid, zero_mul]
    _ = vec pivotSlot := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **THE READ REFUSES A DIAGONAL ONE.**  A carrier read at a slot with
diagonal entry one asks for the read value one.  Every shifted weight
sits below one, thus the slot cannot carry a read. -/
theorem false_of_diag_eq_one_of_read {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) {pivotSlot : Fin slotCount}
    (hone : S pivotSlot pivotSlot = 1) {readVec : Fin slotCount → ℝ} {readVal : ℝ}
    (hread : (S *ᵥ readVec) pivotSlot = readVal * readVec pivotSlot)
    (hnz : readVec pivotSlot ≠ 0) (hlt : readVal < 1) : False := by
  have hexact := mulVec_apply_of_diag_eq_one hsymm hidem hone readVec
  rw [hread] at hexact
  have hzero : (1 - readVal) * readVec pivotSlot = 0 := by linarith [hexact]
  rcases mul_eq_zero.mp hzero with hcase | hcase
  · linarith
  · exact hnz hcase

/-- **THE CONFINEMENT LAW.**  A triangular family fixed by a symmetric
idempotent, of size the trace or more, whose members all vanish at one
slot, forces the diagonal entry of that slot to vanish.  The column of
the slot is fixed, it is nonzero at the slot, and every family member
vanishes there, thus the column extends the triangular family.  The
trace floor then caps the longer family and the count refuses it. -/
theorem diag_eq_zero_of_confined_family {famSize slotCount : ℕ}
    {K : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Kᵀ = K) (hidem : K * K = K)
    (family : Fin famSize → Fin slotCount → ℝ)
    (hfix : ∀ i, K *ᵥ family i = family i)
    (slots : Fin famSize → Fin slotCount)
    (hpivot : ∀ i, family i (slots i) ≠ 0)
    (hlower : ∀ i k : Fin famSize, i < k → family i (slots k) = 0)
    (confineSlot : Fin slotCount)
    (hvanish : ∀ i, family i confineSlot = 0)
    (hcount : Matrix.trace K < (famSize : ℝ) + 1) :
    K confineSlot confineSlot = 0 := by
  classical
  by_contra hne
  set bigFamily : Fin (famSize + 1) → Fin slotCount → ℝ := fun i =>
    if hlt : (i : ℕ) < famSize then family ⟨(i : ℕ), hlt⟩
    else kernelColumn K confineSlot with hbigFamily
  set bigSlots : Fin (famSize + 1) → Fin slotCount := fun i =>
    if hlt : (i : ℕ) < famSize then slots ⟨(i : ℕ), hlt⟩ else confineSlot
    with hbigSlots
  have hbigApply : ∀ i : Fin (famSize + 1),
      bigFamily i = if hlt : (i : ℕ) < famSize then family ⟨(i : ℕ), hlt⟩
        else kernelColumn K confineSlot := fun _ => rfl
  have hbigSlot : ∀ i : Fin (famSize + 1),
      bigSlots i = if hlt : (i : ℕ) < famSize then slots ⟨(i : ℕ), hlt⟩
        else confineSlot := fun _ => rfl
  have hbigFix : ∀ i, K *ᵥ bigFamily i = bigFamily i := by
    intro i
    rw [hbigApply i]
    by_cases hlt : (i : ℕ) < famSize
    · rw [dif_pos hlt]
      exact hfix _
    · rw [dif_neg hlt]
      exact kernelColumn_fixed hidem confineSlot
  have hbigPivot : ∀ i, bigFamily i (bigSlots i) ≠ 0 := by
    intro i
    rw [hbigApply i, hbigSlot i]
    by_cases hlt : (i : ℕ) < famSize
    · rw [dif_pos hlt, dif_pos hlt]
      exact hpivot _
    · rw [dif_neg hlt, dif_neg hlt]
      exact hne
  have hbigLower : ∀ i k : Fin (famSize + 1), i < k → bigFamily i (bigSlots k) = 0 := by
    intro i k hik
    have hiklt : (i : ℕ) < (k : ℕ) := hik
    rw [hbigApply i, hbigSlot k]
    by_cases hklt : (k : ℕ) < famSize
    · have hilt : (i : ℕ) < famSize := by omega
      rw [dif_pos hklt, dif_pos hilt]
      exact hlower _ _ (by exact hiklt)
    · rw [dif_neg hklt]
      have hilt : (i : ℕ) < famSize := by
        have hkle : (k : ℕ) ≤ famSize := by omega
        omega
      rw [dif_pos hilt]
      exact hvanish _
  have hfloor := false_of_triangular_fixed_family hsymm hidem bigFamily hbigFix
    bigSlots hbigPivot hbigLower
  have hcast : ((famSize + 1 : ℕ) : ℝ) = (famSize : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hfloor
  linarith

/-! ## Layer 2 — the parallel column collapse -/

/-- **THE PARALLEL COLUMN TRACE.**  If every column of a symmetric
idempotent is a multiple of one column, the trace is one or zero.  The
diagonal entry at a slot is the square of the multiplier times the base
diagonal entry, the idempotence prices the base entry by the same
square total, and the two readings cancel. -/
theorem trace_eq_one_or_zero_of_parallel_columns {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (baseSlot : Fin slotCount)
    (coeff : Fin slotCount → ℝ)
    (hpar : ∀ slot : Fin slotCount,
      kernelColumn S slot = fun rowIdx => coeff slot * kernelColumn S baseSlot rowIdx) :
    Matrix.trace S = 1 ∨ Matrix.trace S = 0 := by
  classical
  have hsymmEntry : ∀ rowIdx colIdx : Fin slotCount, S colIdx rowIdx = S rowIdx colIdx := by
    intro rowIdx colIdx
    have hentry := congrFun (congrFun hsymm rowIdx) colIdx
    rwa [Matrix.transpose_apply] at hentry
  have hcolEntry : ∀ slot rowIdx : Fin slotCount,
      S rowIdx slot = coeff slot * S rowIdx baseSlot := by
    intro slot rowIdx
    have hentry := congrFun (hpar slot) rowIdx
    exact hentry
  have hcross : ∀ slot : Fin slotCount,
      S slot baseSlot = coeff slot * S baseSlot baseSlot := by
    intro slot
    rw [← hsymmEntry slot baseSlot, hcolEntry slot baseSlot, hsymmEntry baseSlot baseSlot]
  have hdiag : ∀ slot : Fin slotCount,
      S slot slot = coeff slot * coeff slot * S baseSlot baseSlot := by
    intro slot
    rw [hcolEntry slot slot, hcross slot]
    ring
  set sqTotal := ∑ slot : Fin slotCount, coeff slot * coeff slot with hsqTotal
  have htrace : Matrix.trace S = sqTotal * S baseSlot baseSlot := by
    rw [Matrix.trace, hsqTotal, Finset.sum_mul]
    refine Finset.sum_congr rfl fun slot _ => ?_
    show S slot slot = coeff slot * coeff slot * S baseSlot baseSlot
    exact hdiag slot
  have hbase : S baseSlot baseSlot
      = sqTotal * (S baseSlot baseSlot * S baseSlot baseSlot) := by
    have hentry := congrFun (congrFun hidem baseSlot) baseSlot
    rw [Matrix.mul_apply] at hentry
    have hrew : (∑ midSlot, S baseSlot midSlot * S midSlot baseSlot)
        = sqTotal * (S baseSlot baseSlot * S baseSlot baseSlot) := by
      rw [hsqTotal, Finset.sum_mul]
      refine Finset.sum_congr rfl fun slot _ => ?_
      rw [hsymmEntry slot baseSlot, hcross slot]
      ring
    exact hentry.symm.trans hrew
  by_cases hzero : S baseSlot baseSlot = 0
  · right
    rw [htrace, hzero, mul_zero]
  · left
    have hone : sqTotal * S baseSlot baseSlot = 1 := by
      have hstep : S baseSlot baseSlot * (sqTotal * S baseSlot baseSlot - 1) = 0 := by
        nlinarith [hbase]
      rcases mul_eq_zero.mp hstep with hcase | hcase
      · exact absurd hcase hzero
      · linarith
    rw [htrace, hone]

/-- **THE PARALLEL COLUMN COLLAPSE.**  A symmetric idempotent of trace
two has two independent columns, thus its columns are not all multiples
of one column. -/
theorem false_of_parallel_columns {slotCount : ℕ}
    {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (baseSlot : Fin slotCount)
    (coeff : Fin slotCount → ℝ)
    (hpar : ∀ slot : Fin slotCount,
      kernelColumn S slot = fun rowIdx => coeff slot * kernelColumn S baseSlot rowIdx)
    (htrace : Matrix.trace S = 2) : False := by
  rcases trace_eq_one_or_zero_of_parallel_columns hsymm hidem baseSlot coeff hpar with
    hcase | hcase <;> rw [htrace] at hcase <;> norm_num at hcase

/-! ## Layer 3 — the witness family and the confinement kill -/

/-- The vector of a kernel witness in a read frame. -/
noncomputable def witnessVector {basisCount : ℕ}
    (S : Matrix (Fin basisCount) (Fin basisCount) ℝ)
    (readVecs : Fin 6 → Fin basisCount → ℝ) :
    SlotWitness basisCount → Fin basisCount → ℝ
  | SlotWitness.dead deadSlot => fun slot => if slot = deadSlot then (1 : ℝ) else 0
  | SlotWitness.read atomIndex => readVecs atomIndex
  | SlotWitness.residual atomIndex => readVecs atomIndex - S *ᵥ readVecs atomIndex

theorem witnessVector_dead {basisCount : ℕ}
    (S : Matrix (Fin basisCount) (Fin basisCount) ℝ)
    (readVecs : Fin 6 → Fin basisCount → ℝ) (deadSlot : Fin basisCount) :
    witnessVector S readVecs (SlotWitness.dead deadSlot)
      = fun slot => if slot = deadSlot then (1 : ℝ) else 0 := rfl

theorem witnessVector_read {basisCount : ℕ}
    (S : Matrix (Fin basisCount) (Fin basisCount) ℝ)
    (readVecs : Fin 6 → Fin basisCount → ℝ) (atomIndex : Fin 6) :
    witnessVector S readVecs (SlotWitness.read atomIndex) = readVecs atomIndex := rfl

theorem witnessVector_residual {basisCount : ℕ}
    (S : Matrix (Fin basisCount) (Fin basisCount) ℝ)
    (readVecs : Fin 6 → Fin basisCount → ℝ) (atomIndex : Fin 6) :
    witnessVector S readVecs (SlotWitness.residual atomIndex)
      = readVecs atomIndex - S *ᵥ readVecs atomIndex := rfl

set_option maxHeartbeats 6400000 in
/-- **THE WITNESS FAMILY.**  In a read frame, a triangular chain of
kernel witnesses is a triangular family fixed by the complementary
idempotent.  A dead slot carries its own axis, a boundary atom carries
its read, and any atom carries its residual.  A residual is unknown off
the carrier, thus it sits at the end of the chain only. -/
theorem SharedPrivateData.witness_family_triangular {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ}
    {readVecs : Fin 6 → Fin data.basisCount → ℝ}
    (hSsymm : Sᵀ = S) (hSidem : S * S = S)
    (hsuppFrame : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
      readVecs atomIndex slot = 0)
    (hreadFrame : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ data.activeSubset (data.basisLabel slot) →
      (S *ᵥ readVecs atomIndex) slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex) * readVecs atomIndex slot)
    (hboundary : ∀ atomIndex : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 →
      S *ᵥ readVecs atomIndex = 0)
    (hcarrierNz : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      readVecs atomIndex slot ≠ 0)
    (hspan : ∀ x : Fin data.basisCount → ℝ,
      (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ x = 0) → x = 0)
    (hcommute : ∀ rowSlot colSlot : Fin data.basisCount,
      (∑ atomIndex : Fin 6,
          readVecs atomIndex rowSlot * (S *ᵥ readVecs atomIndex) colSlot)
        = ∑ atomIndex : Fin 6,
          (S *ᵥ readVecs atomIndex) rowSlot * readVecs atomIndex colSlot)
    {chainLength : ℕ}
    (source : Fin chainLength → SlotWitness data.basisCount)
    (slots : Fin chainLength → Fin data.basisCount)
    (hdeadSlot : ∀ (i : Fin chainLength) (deadSlot : Fin data.basisCount),
      source i = SlotWitness.dead deadSlot → slots i = deadSlot)
    (hdeadBoundary : ∀ (i : Fin chainLength) (deadSlot : Fin data.basisCount),
      source i = SlotWitness.dead deadSlot →
      ∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel deadSlot) →
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0)
    (hreadBoundary : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.read atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0)
    (hreadMem : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.read atomIndex →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel (slots i)))
    (hresidualMem : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.residual atomIndex →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel (slots i)))
    (hresidualLast : ∀ i k : Fin chainLength, i < k →
      ∀ atomIndex : Fin 6, source i ≠ SlotWitness.residual atomIndex)
    (hlowerDead : ∀ i k : Fin chainLength, i < k →
      ∀ deadSlot : Fin data.basisCount,
        source i = SlotWitness.dead deadSlot → slots k ≠ deadSlot)
    (hlowerRead : ∀ i k : Fin chainLength, i < k →
      ∀ atomIndex : Fin 6, source i = SlotWitness.read atomIndex →
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel (slots k))) :
    (∀ i, (1 - S) *ᵥ witnessVector S readVecs (source i)
        = witnessVector S readVecs (source i))
      ∧ (∀ i, witnessVector S readVecs (source i) (slots i) ≠ 0)
      ∧ (∀ i k : Fin chainLength, i < k →
          witnessVector S readVecs (source i) (slots k) = 0) := by
  classical
  set chartValue := chartObjective (chartPointOfDesign crux.design) with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hread : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      (S *ᵥ readVecs atomIndex) slot
        = (chartValue + atomWeight atomIndex) * readVecs atomIndex slot :=
    fun atomIndex slot hmem => hreadFrame atomIndex slot
      (datumTightSupport_subset data.hdata (hmemActive slot) hmem)
  have hltOne : ∀ atomIndex : Fin 6, chartValue + atomWeight atomIndex < 1 := by
    intro atomIndex
    have hwle : atomWeight atomIndex ≤ 1 := by
      have hle : atomWeight atomIndex ≤ ∑ probe, atomWeight probe :=
        Finset.single_le_sum (f := atomWeight)
          (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ atomIndex)
      rwa [data.hdata.weight_sum_one] at hle
    have hneg : chartValue < 0 := data.hvalueNeg
    linarith
  have hkApply : ∀ vec : Fin data.basisCount → ℝ,
      ((1 : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ) - S) *ᵥ vec
        = vec - S *ᵥ vec := by
    intro vec
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases hsrc : source i with deadSlot | atomIndex | atomIndex
    · have hzeroCol : S *ᵥ (fun slot => if slot = deadSlot then (1 : ℝ) else 0) = 0 := by
        refine dead_slot_column_of_frame hSsymm hSidem readVecs hcommute hspan
          deadSlot fun atomIndex => ?_
        by_cases hmem : atomIndex ∈ datumTightSupport data.tightDir
          (data.basisLabel deadSlot)
        · have hzero := hdeadBoundary i deadSlot hsrc atomIndex hmem
          rw [hread atomIndex deadSlot hmem, hzero, zero_mul, zero_mul]
        · rw [hsuppFrame atomIndex deadSlot hmem, mul_zero]
      rw [witnessVector_dead, hkApply, hzeroCol, sub_zero]
    · rw [witnessVector_read, hkApply,
        hboundary atomIndex (hreadBoundary i atomIndex hsrc), sub_zero]
    · have hkill : S *ᵥ (readVecs atomIndex - S *ᵥ readVecs atomIndex) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hSidem, sub_self]
      rw [witnessVector_residual, hkApply, hkill, sub_zero]
  · intro i
    rcases hsrc : source i with deadSlot | atomIndex | atomIndex
    · rw [witnessVector_dead, hdeadSlot i deadSlot hsrc]
      simp
    · rw [witnessVector_read]
      exact hcarrierNz atomIndex (slots i) (hreadMem i atomIndex hsrc)
    · have hmem := hresidualMem i atomIndex hsrc
      have hentry : (readVecs atomIndex - S *ᵥ readVecs atomIndex) (slots i)
          = (1 - (chartValue + atomWeight atomIndex)) * readVecs atomIndex (slots i) := by
        show readVecs atomIndex (slots i) - (S *ᵥ readVecs atomIndex) (slots i)
          = (1 - (chartValue + atomWeight atomIndex)) * readVecs atomIndex (slots i)
        rw [hread atomIndex (slots i) hmem]
        ring
      rw [witnessVector_residual, hentry]
      refine mul_ne_zero ?_ (hcarrierNz atomIndex (slots i) hmem)
      have hlt := hltOne atomIndex
      linarith
  · intro i k hik
    rcases hsrc : source i with deadSlot | atomIndex | atomIndex
    · rw [witnessVector_dead]
      exact if_neg (hlowerDead i k hik deadSlot hsrc)
    · rw [witnessVector_read]
      exact hsuppFrame atomIndex (slots k) (hlowerRead i k hik atomIndex hsrc)
    · exact absurd hsrc (hresidualLast i k hik atomIndex)

set_option maxHeartbeats 6400000 in
/-- **THE CONFINEMENT KILL.**  A triangular chain of kernel witnesses
that all vanish at one slot kills at the length of the complementary
trace, one member below the plain chain.  The chain spans the whole
kernel at the confinement slot, thus the read idempotent has diagonal
entry one there, and the carrier read of the confinement slot refuses
it.  The chain holds no residual, because a residual is unknown off its
carrier. -/
theorem SharedPrivateData.false_of_confined_chain {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {chainLength : ℕ}
    (source : Fin chainLength → SlotWitness data.basisCount)
    (slots : Fin chainLength → Fin data.basisCount)
    (hdeadSlot : ∀ (i : Fin chainLength) (deadSlot : Fin data.basisCount),
      source i = SlotWitness.dead deadSlot → slots i = deadSlot)
    (hdeadBoundary : ∀ (i : Fin chainLength) (deadSlot : Fin data.basisCount),
      source i = SlotWitness.dead deadSlot →
      ∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel deadSlot) →
        chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0)
    (hreadBoundary : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.read atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0)
    (hreadMem : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.read atomIndex →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel (slots i)))
    (hnoResidual : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i ≠ SlotWitness.residual atomIndex)
    (hlowerDead : ∀ i k : Fin chainLength, i < k →
      ∀ deadSlot : Fin data.basisCount,
        source i = SlotWitness.dead deadSlot → slots k ≠ deadSlot)
    (hlowerRead : ∀ i k : Fin chainLength, i < k →
      ∀ atomIndex : Fin 6, source i = SlotWitness.read atomIndex →
        atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel (slots k)))
    (confineSlot : Fin data.basisCount)
    (hconfineDead : ∀ (i : Fin chainLength) (deadSlot : Fin data.basisCount),
      source i = SlotWitness.dead deadSlot → confineSlot ≠ deadSlot)
    (hconfineRead : ∀ (i : Fin chainLength) (atomIndex : Fin 6),
      source i = SlotWitness.read atomIndex →
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel confineSlot))
    (hcount : (data.basisCount : ℝ) ≤ Matrix.trace data.coeff + chainLength) :
    False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hreadFrame, _hnorm,
    _hnz, hboundary, hcarrierNz, hspan, hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  obtain ⟨hfix, hpivot, hlower⟩ :=
    data.witness_family_triangular hSsymm hSidem hsuppFrame hreadFrame hboundary
      hcarrierNz hspan hcommute source slots hdeadSlot hdeadBoundary hreadBoundary
      hreadMem (fun i atomIndex hsrc => absurd hsrc (hnoResidual i atomIndex))
      (fun i _ _ atomIndex => hnoResidual i atomIndex) hlowerDead hlowerRead
  set kernelMat : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ := 1 - S
    with hkernelMat
  have hkSymm : kernelMatᵀ = kernelMat := by
    rw [hkernelMat, Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hkIdem : kernelMat * kernelMat = kernelMat := by
    rw [hkernelMat]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hSidem]
    abel
  have hvanish : ∀ i, witnessVector S readVecs (source i) confineSlot = 0 := by
    intro i
    rcases hsrc : source i with deadSlot | atomIndex | atomIndex
    · rw [witnessVector_dead]
      exact if_neg (hconfineDead i deadSlot hsrc)
    · rw [witnessVector_read]
      exact hsuppFrame atomIndex confineSlot (hconfineRead i atomIndex hsrc)
    · exact absurd hsrc (hnoResidual i atomIndex)
  have htraceCompl : Matrix.trace kernelMat
      = (data.basisCount : ℝ) - Matrix.trace data.coeff := by
    rw [hkernelMat, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hStrace]
  have hconfine := diag_eq_zero_of_confined_family hkSymm hkIdem
    (fun i => witnessVector S readVecs (source i)) hfix slots hpivot hlower confineSlot
    hvanish (by rw [htraceCompl]; linarith)
  have hone : S confineSlot confineSlot = 1 := by
    have hentry : kernelMat confineSlot confineSlot
        = 1 - S confineSlot confineSlot := by
      rw [hkernelMat]
      simp [Matrix.one_apply_eq]
    rw [hentry] at hconfine
    linarith
  -- the confinement slot carries three atoms, and each of them reads there
  obtain ⟨carrierAtom, hcarrierMem⟩ : ∃ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel confineSlot) := by
    have hcard := data.hthree confineSlot
    exact Finset.card_pos.mp (by omega)
  have hmemActive : data.basisLabel confineSlot ∈ data.activeSet := by
    have hmem := data.hmem confineSlot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hreadHere := hreadFrame carrierAtom confineSlot
    (datumTightSupport_subset data.hdata hmemActive hcarrierMem)
  have hltOne : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight carrierAtom < 1 := by
    have hwle : (chartPointOfDesign crux.design).weight carrierAtom ≤ 1 := by
      have hle : (chartPointOfDesign crux.design).weight carrierAtom
          ≤ ∑ probe, (chartPointOfDesign crux.design).weight probe :=
        Finset.single_le_sum (f := (chartPointOfDesign crux.design).weight)
          (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ carrierAtom)
      rwa [data.hdata.weight_sum_one] at hle
    have hneg : chartObjective (chartPointOfDesign crux.design) < 0 := data.hvalueNeg
    linarith
  exact false_of_diag_eq_one_of_read hSsymm hSidem hone hreadHere
    (hcarrierNz carrierAtom confineSlot hcarrierMem) hltOne

set_option maxHeartbeats 3200000 in
/-- **THE CONFINED PRIVATE PAIR.**  The private slot is always dead,
thus its axis plus two boundary reads make a confined chain of three.
The chain kills whenever the basis count is at most the trace plus
three, in particular at basis count five and trace two. -/
theorem SharedPrivateData.false_of_confined_private_pair {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {atomOne atomTwo : Fin 6} {slotOne slotTwo confineSlot : Fin data.basisCount}
    (hbndOne : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0)
    (hbndTwo : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomTwo = 0)
    (hmemOne : atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hmemTwo : atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hslotOne : slotOne ≠ data.privateSlot)
    (hslotTwo : slotTwo ≠ data.privateSlot)
    (hconfineSlot : confineSlot ≠ data.privateSlot)
    (houtTwo : atomOne ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (houtConfineOne : atomOne ∉ datumTightSupport data.tightDir
      (data.basisLabel confineSlot))
    (houtConfineTwo : atomTwo ∉ datumTightSupport data.tightDir
      (data.basisLabel confineSlot))
    (hcount : (data.basisCount : ℝ) ≤ Matrix.trace data.coeff + 3) : False := by
  classical
  refine data.false_of_confined_chain hdiag
    ![SlotWitness.dead data.privateSlot, SlotWitness.read atomOne,
      SlotWitness.read atomTwo]
    ![data.privateSlot, slotOne, slotTwo] ?_ ?_ ?_ ?_ ?_ ?_ ?_ confineSlot ?_ ?_ ?_
  · intro i deadSlot hsrc
    fin_cases i <;> simp_all
  · intro i deadSlot hsrc atomIndex hmem
    have heq : deadSlot = data.privateSlot := by
      fin_cases i <;> simp_all
    subst heq
    exact data.boundary_of_private_support hdiag hmem
  · intro i atomIndex hsrc
    fin_cases i <;> simp_all
  · intro i atomIndex hsrc
    fin_cases i <;> simp_all
  · intro i atomIndex
    fin_cases i <;> simp
  · intro i k hik deadSlot hsrc
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i k hik atomIndex hsrc
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i deadSlot hsrc
    have heq : deadSlot = data.privateSlot := by
      fin_cases i <;> simp_all
    subst heq
    exact hconfineSlot
  · intro i atomIndex hsrc
    fin_cases i <;> simp_all
  · simpa using hcount

set_option maxHeartbeats 3200000 in
/-- **THE CONFINED BOUNDARY TRIPLE.**  Three boundary reads with a
triangular slot pattern, all missing the support of one slot, die
whenever the basis count is at most the trace plus three. -/
theorem SharedPrivateData.false_of_confined_boundary_triple {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (atoms : Fin 3 → Fin 6) (slots : Fin 3 → Fin data.basisCount)
    (confineSlot : Fin data.basisCount)
    (hbnd : ∀ i, chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight (atoms i) = 0)
    (hmem : ∀ i, atoms i ∈ datumTightSupport data.tightDir (data.basisLabel (slots i)))
    (hout : ∀ i k : Fin 3, i < k →
      atoms i ∉ datumTightSupport data.tightDir (data.basisLabel (slots k)))
    (hconfine : ∀ i, atoms i ∉ datumTightSupport data.tightDir
      (data.basisLabel confineSlot))
    (hcount : (data.basisCount : ℝ) ≤ Matrix.trace data.coeff + 3) : False := by
  refine data.false_of_confined_chain hdiag (fun i => SlotWitness.read (atoms i))
    slots (fun i deadSlot hsrc => absurd hsrc (by simp))
    (fun i deadSlot hsrc => absurd hsrc (by simp)) ?_ ?_
    (fun i atomIndex hsrc => by simp at hsrc)
    (fun i k _ deadSlot hsrc => absurd hsrc (by simp)) ?_ confineSlot
    (fun i deadSlot hsrc => absurd hsrc (by simp)) ?_ (by simpa using hcount)
  · intro i atomIndex hsrc
    have heq : atoms i = atomIndex := by simpa using hsrc
    rw [← heq]
    exact hbnd i
  · intro i atomIndex hsrc
    have heq : atoms i = atomIndex := by simpa using hsrc
    rw [← heq]
    exact hmem i
  · intro i k hik atomIndex hsrc
    have heq : atoms i = atomIndex := by simpa using hsrc
    rw [← heq]
    exact hout i k hik
  · intro i atomIndex hsrc
    have heq : atoms i = atomIndex := by simpa using hsrc
    rw [← heq]
    exact hconfine i

/-! ## Layer 4 — the dead propagation -/

set_option maxHeartbeats 3200000 in
/-- **THE DEAD COLUMN.**  A slot that no interior atom carries has a
vanishing idempotent column, and thus a vanishing row.  The statement
returns the whole matrix so that a caller can reuse the frame. -/
theorem SharedPrivateData.exists_dead_read_frame {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) :
    ∃ (S : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ)
      (readVecs : Fin 6 → Fin data.basisCount → ℝ),
      Sᵀ = S ∧ S * S = S
      ∧ Matrix.trace S = Matrix.trace data.coeff
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot) →
          readVecs atomIndex slot = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          (S *ᵥ readVecs atomIndex) slot
            = (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomIndex)
              * readVecs atomIndex slot)
      ∧ (∀ atomIndex : Fin 6, readVecs atomIndex ⬝ᵥ readVecs atomIndex = (6 : ℝ)⁻¹)
      ∧ (∀ atomIndex : Fin 6,
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex = 0 →
          S *ᵥ readVecs atomIndex = 0)
      ∧ (∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          readVecs atomIndex slot ≠ 0)
      ∧ (∀ deadSlot : Fin data.basisCount,
          (∀ probe : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight probe →
            probe ∉ datumTightSupport data.tightDir (data.basisLabel deadSlot)) →
          ∀ rowSlot : Fin data.basisCount, S rowSlot deadSlot = 0) := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hreadFrame, hnorm,
    _hnz, hboundary, hcarrierNz, hspan, hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  have hread : ∀ (atomIndex : Fin 6) (slot : Fin data.basisCount),
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      (S *ᵥ readVecs atomIndex) slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * readVecs atomIndex slot :=
    fun atomIndex slot hmem => hreadFrame atomIndex slot
      (datumTightSupport_subset data.hdata (hmemActive slot) hmem)
  refine ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hread, hnorm, hboundary,
    hcarrierNz, ?_⟩
  intro deadSlot hnone rowSlot
  have hzeroCol : S *ᵥ (fun slot => if slot = deadSlot then (1 : ℝ) else 0) = 0 := by
    refine dead_slot_column_of_frame hSsymm hSidem readVecs hcommute hspan
      deadSlot fun probe => ?_
    by_cases hmem : probe ∈ datumTightSupport data.tightDir (data.basisLabel deadSlot)
    · have hnn := capture_diagonal_nonneg_of_isChartStationaryData data.hdata probe
      have hzero : chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe = 0 := by
        rcases lt_or_eq_of_le hnn with hpos | heq
        · exact absurd hmem (hnone probe hpos)
        · exact heq.symm
      rw [hread probe deadSlot hmem, hzero, zero_mul, zero_mul]
    · rw [hsuppFrame probe deadSlot hmem, mul_zero]
  have hentry := congrFun hzeroCol rowSlot
  have hexpand : (S *ᵥ fun slot => if slot = deadSlot then (1 : ℝ) else 0) rowSlot
      = S rowSlot deadSlot := by
    calc (S *ᵥ fun slot => if slot = deadSlot then (1 : ℝ) else 0) rowSlot
        = ∑ slot, S rowSlot slot * (if slot = deadSlot then (1 : ℝ) else 0) := rfl
      _ = S rowSlot deadSlot := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
  rw [hexpand] at hentry
  simpa using hentry

set_option maxHeartbeats 3200000 in
/-- **THE DEAD PROPAGATION.**  A boundary read is a kernel vector, thus
the columns of its carrier carry a relation with every coefficient
nonzero.  If every carrier slot except one has a vanishing column, the
last column vanishes too — and an interior atom cannot carry a slot
with a vanishing column.  **Thus a boundary carrier never holds exactly
one live slot.** -/
theorem SharedPrivateData.false_of_boundary_dead_cocarrier {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {boundaryAtom : Fin 6}
    (hbnd : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundaryAtom = 0)
    {liveSlot : Fin data.basisCount}
    (hmemLive : boundaryAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel liveSlot))
    (hrestDead : ∀ otherSlot : Fin data.basisCount, otherSlot ≠ liveSlot →
      boundaryAtom ∈ datumTightSupport data.tightDir (data.basisLabel otherSlot) →
      ∀ probe : Fin 6,
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe →
        probe ∉ datumTightSupport data.tightDir (data.basisLabel otherSlot))
    {interiorAtom : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight interiorAtom)
    (hmemInterior : interiorAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel liveSlot)) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, _hStrace, hsuppFrame, hread, _hnorm,
    hboundary, hcarrierNz, hdeadCol⟩ := data.exists_dead_read_frame hdiag
  have hsymmEntry : ∀ rowIdx colIdx : Fin data.basisCount,
      S colIdx rowIdx = S rowIdx colIdx := by
    intro rowIdx colIdx
    have hentry := congrFun (congrFun hSsymm rowIdx) colIdx
    rwa [Matrix.transpose_apply] at hentry
  have hzero := hboundary boundaryAtom hbnd
  -- the boundary relation collapses to the one live column
  have hcol : ∀ rowSlot : Fin data.basisCount,
      S rowSlot liveSlot * readVecs boundaryAtom liveSlot = 0 := by
    intro rowSlot
    have hentry := congrFun hzero rowSlot
    have hsingle : (∑ slot, S rowSlot slot * readVecs boundaryAtom slot)
        = S rowSlot liveSlot * readVecs boundaryAtom liveSlot := by
      refine Finset.sum_eq_single liveSlot (fun slot _ hne => ?_)
        (fun hnot => absurd (Finset.mem_univ liveSlot) hnot)
      by_cases hmem : boundaryAtom ∈ datumTightSupport data.tightDir
        (data.basisLabel slot)
      · rw [hdeadCol slot (hrestDead slot hne hmem) rowSlot, zero_mul]
      · rw [hsuppFrame boundaryAtom slot hmem, mul_zero]
    have hval : (S *ᵥ readVecs boundaryAtom) rowSlot
        = ∑ slot, S rowSlot slot * readVecs boundaryAtom slot := rfl
    rw [hval, hsingle] at hentry
    exact hentry
  have hnzLive := hcarrierNz boundaryAtom liveSlot hmemLive
  have hcolZero : ∀ rowSlot : Fin data.basisCount, S rowSlot liveSlot = 0 := by
    intro rowSlot
    rcases mul_eq_zero.mp (hcol rowSlot) with hcase | hcase
    · exact hcase
    · exact absurd hcase hnzLive
  -- the interior read then asks for a nonzero entry in a vanishing row
  have hrowZero : (S *ᵥ readVecs interiorAtom) liveSlot = 0 := by
    calc (S *ᵥ readVecs interiorAtom) liveSlot
        = ∑ slot, S liveSlot slot * readVecs interiorAtom slot := rfl
      _ = 0 := by
          refine Finset.sum_eq_zero fun slot _ => ?_
          rw [hsymmEntry slot liveSlot, hcolZero slot, zero_mul]
  have hreadHere := hread interiorAtom liveSlot hmemInterior
  rw [hrowZero] at hreadHere
  have hnzInterior := hcarrierNz interiorAtom liveSlot hmemInterior
  rcases mul_eq_zero.mp hreadHere.symm with hcase | hcase
  · linarith
  · exact hnzInterior hcase

/-- **THE LIVE COCARRIER.**  A boundary atom that carries a live slot
carries a second live slot.  The contrapositive of the dead
propagation. -/
theorem SharedPrivateData.exists_live_cocarrier {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {boundaryAtom : Fin 6}
    (hbnd : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundaryAtom = 0)
    {liveSlot : Fin data.basisCount}
    (hmemLive : boundaryAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel liveSlot))
    {interiorAtom : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight interiorAtom)
    (hmemInterior : interiorAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel liveSlot)) :
    ∃ otherSlot : Fin data.basisCount, otherSlot ≠ liveSlot
      ∧ boundaryAtom ∈ datumTightSupport data.tightDir (data.basisLabel otherSlot)
      ∧ ∃ probe : Fin 6,
          0 < chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight probe
          ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel otherSlot) := by
  classical
  by_contra hnot
  push Not at hnot
  refine data.false_of_boundary_dead_cocarrier hdiag hbnd hmemLive ?_ hpos hmemInterior
  intro otherSlot hne hmemOther probe hposProbe hmemProbe
  exact absurd hmemProbe (by
    have := hnot otherSlot hne hmemOther
    exact this probe hposProbe)

/-! ## Layer 5 — the interior leak -/

set_option maxHeartbeats 3200000 in
/-- **THE INTERIOR LEAK.**  The fixed part of an interior read has the
shifted weight over six as its energy, and the carrier holds only the
square of that weight.  The shifted weight sits below one, thus the
difference is positive and the fixed part is nonzero off the carrier.
A dead slot has a vanishing row, thus **every interior atom misses a
live slot**. -/
theorem SharedPrivateData.exists_live_slot_offCarrier {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    {interiorAtom : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight interiorAtom) :
    ∃ slot : Fin data.basisCount,
      interiorAtom ∉ datumTightSupport data.tightDir (data.basisLabel slot)
      ∧ ∃ probe : Fin 6,
          0 < chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight probe
          ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, _hStrace, hsuppFrame, hread, hnorm,
    _hboundary, _hcarrierNz, hdeadCol⟩ := data.exists_dead_read_frame hdiag
  set readVal := chartObjective (chartPointOfDesign crux.design)
    + (chartPointOfDesign crux.design).weight interiorAtom with hreadVal
  set car := Finset.univ.filter fun slot : Fin data.basisCount =>
    interiorAtom ∈ datumTightSupport data.tightDir (data.basisLabel slot) with hcar
  have hcarmem : ∀ slot : Fin data.basisCount, slot ∈ car ↔
      interiorAtom ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro slot
    simp [hcar]
  have hsupp : ∀ slot ∉ car, readVecs interiorAtom slot = 0 :=
    fun slot hslot => hsuppFrame interiorAtom slot fun hmem =>
      hslot ((hcarmem slot).mpr hmem)
  have hreadCar : ∀ slot ∈ car,
      (S *ᵥ readVecs interiorAtom) slot = readVal * readVecs interiorAtom slot :=
    fun slot hslot => hread interiorAtom slot ((hcarmem slot).mp hslot)
  have hltOne : readVal < 1 := by
    have hwle : (chartPointOfDesign crux.design).weight interiorAtom ≤ 1 := by
      have hle : (chartPointOfDesign crux.design).weight interiorAtom
          ≤ ∑ probe, (chartPointOfDesign crux.design).weight probe :=
        Finset.single_le_sum (f := (chartPointOfDesign crux.design).weight)
          (fun probe _ => (data.hdata.weight_pos probe).le) (Finset.mem_univ interiorAtom)
      rwa [data.hdata.weight_sum_one] at hle
    have hneg : chartObjective (chartPointOfDesign crux.design) < 0 := data.hvalueNeg
    rw [hreadVal]
    linarith
  -- the total fixed energy and the carrier part of it
  have hself := read_fixed_self_energy hSsymm hSidem hsupp hreadCar
  rw [hnorm interiorAtom] at hself
  have hsplit : ((S *ᵥ readVecs interiorAtom) ⬝ᵥ (S *ᵥ readVecs interiorAtom))
      = ∑ slot ∈ car, (S *ᵥ readVecs interiorAtom) slot
          * (S *ᵥ readVecs interiorAtom) slot
        + ∑ slot ∈ carᶜ, (S *ᵥ readVecs interiorAtom) slot
          * (S *ᵥ readVecs interiorAtom) slot := by
    rw [dotProduct]
    exact (Finset.sum_add_sum_compl car
      (fun slot => (S *ᵥ readVecs interiorAtom) slot
        * (S *ᵥ readVecs interiorAtom) slot)).symm
  have hcarPart : (∑ slot ∈ car, (S *ᵥ readVecs interiorAtom) slot
      * (S *ᵥ readVecs interiorAtom) slot)
      = readVal * readVal * (6 : ℝ)⁻¹ := by
    have hstep : (∑ slot ∈ car, (S *ᵥ readVecs interiorAtom) slot
        * (S *ᵥ readVecs interiorAtom) slot)
        = ∑ slot ∈ car, readVal * readVal
            * (readVecs interiorAtom slot * readVecs interiorAtom slot) :=
      Finset.sum_congr rfl fun slot hslot => by rw [hreadCar slot hslot]; ring
    have hnormCar : (∑ slot ∈ car,
        readVecs interiorAtom slot * readVecs interiorAtom slot) = (6 : ℝ)⁻¹ := by
      have hfull : (readVecs interiorAtom ⬝ᵥ readVecs interiorAtom)
          = ∑ slot, readVecs interiorAtom slot * readVecs interiorAtom slot := rfl
      have hrestrict : (∑ slot ∈ car,
          readVecs interiorAtom slot * readVecs interiorAtom slot)
          = ∑ slot, readVecs interiorAtom slot * readVecs interiorAtom slot :=
        Finset.sum_subset (Finset.subset_univ car) fun slot _ hslot => by
          rw [hsupp slot hslot, mul_zero]
      rw [hrestrict, ← hfull, hnorm interiorAtom]
    rw [hstep, ← Finset.mul_sum, hnormCar]
  have hoffPart : (∑ slot ∈ carᶜ, (S *ᵥ readVecs interiorAtom) slot
      * (S *ᵥ readVecs interiorAtom) slot) = readVal * (1 - readVal) * (6 : ℝ)⁻¹ := by
    rw [hsplit, hcarPart] at hself
    linear_combination hself
  have hoffPos : 0 < ∑ slot ∈ carᶜ, (S *ᵥ readVecs interiorAtom) slot
      * (S *ᵥ readVecs interiorAtom) slot := by
    rw [hoffPart]
    exact mul_pos (mul_pos hpos (by linarith)) (by norm_num)
  obtain ⟨leakSlot, hleakMem, hleakNz⟩ : ∃ slot ∈ carᶜ,
      (S *ᵥ readVecs interiorAtom) slot * (S *ᵥ readVecs interiorAtom) slot ≠ 0 := by
    by_contra hall
    push Not at hall
    exact absurd (Finset.sum_eq_zero fun slot hslot => hall slot hslot) (ne_of_gt hoffPos)
  refine ⟨leakSlot, fun hmem => ?_, ?_⟩
  · exact absurd ((hcarmem leakSlot).mpr hmem) (Finset.mem_compl.mp hleakMem)
  · by_contra hnone
    push Not at hnone
    have hzeroRow : (S *ᵥ readVecs interiorAtom) leakSlot = 0 := by
      have hsymmEntry : ∀ rowIdx colIdx : Fin data.basisCount,
          S colIdx rowIdx = S rowIdx colIdx := by
        intro rowIdx colIdx
        have hentry := congrFun (congrFun hSsymm rowIdx) colIdx
        rwa [Matrix.transpose_apply] at hentry
      calc (S *ᵥ readVecs interiorAtom) leakSlot
          = ∑ slot, S leakSlot slot * readVecs interiorAtom slot := rfl
        _ = 0 := by
            refine Finset.sum_eq_zero fun slot _ => ?_
            rw [hsymmEntry slot leakSlot,
              hdeadCol leakSlot (fun probe hprobe => hnone probe hprobe) slot, zero_mul]
    rw [hzeroRow, mul_zero] at hleakNz
    exact hleakNz rfl


/-! ## Layer 5b — the live slots, the multiplicity cap and the cocarrier pair -/

/-- The slots that some interior atom carries. -/
noncomputable def SharedPrivateData.liveSlots {crux : SixThreeCrux}
    (data : SharedPrivateData crux) : Finset (Fin data.basisCount) :=
  Finset.univ.filter fun slot => ∃ probe : Fin 6,
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight probe
    ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)

theorem SharedPrivateData.mem_liveSlots {crux : SixThreeCrux}
    (data : SharedPrivateData crux) (slot : Fin data.basisCount) :
    slot ∈ data.liveSlots ↔ ∃ probe : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight probe
      ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
  simp [SharedPrivateData.liveSlots]

/-- The carrier of an interior atom sits inside the live slots. -/
theorem SharedPrivateData.carrier_subset_liveSlots {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {interiorAtom : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight interiorAtom) :
    (Finset.univ.filter fun columnIndex : Fin data.basisCount =>
      interiorAtom ∈ datumTightSupport data.tightDir (data.basisLabel columnIndex))
      ⊆ data.liveSlots := by
  intro slot hslot
  exact (data.mem_liveSlots slot).mpr
    ⟨interiorAtom, hpos, (Finset.mem_filter.mp hslot).2⟩

/-- **THE INTERIOR MULTIPLICITY CAP.**  The interior leak puts a live
slot off the carrier of every interior atom, thus the multiplicity of an
interior atom is below the live slot count.  At basis count five and
trace two the private slot is dead, thus the cap reads three. -/
theorem SharedPrivateData.multiplicity_lt_liveSlots_card {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {interiorAtom : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight interiorAtom) :
    basisSupportMultiplicity data.tightDir data.basisLabel interiorAtom
      < data.liveSlots.card := by
  obtain ⟨leakSlot, hleakOff, hleakLive⟩ := data.exists_live_slot_offCarrier hdiag hpos
  refine Finset.card_lt_card ⟨data.carrier_subset_liveSlots hpos, fun hall => ?_⟩
  have hmem := hall ((data.mem_liveSlots leakSlot).mpr hleakLive)
  exact hleakOff (Finset.mem_filter.mp hmem).2

/-- **THE COCARRIER PAIR.**  A boundary atom that carries a live slot
carries two live slots.  The cardinality form of the dead
propagation. -/
theorem SharedPrivateData.two_le_live_cocarrier_card {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag) {boundaryAtom : Fin 6}
    (hbnd : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundaryAtom = 0)
    {liveSlot : Fin data.basisCount}
    (hmemLive : boundaryAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel liveSlot))
    {interiorAtom : Fin 6}
    (hpos : 0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight interiorAtom)
    (hmemInterior : interiorAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel liveSlot)) :
    2 ≤ (data.liveSlots.filter fun slot =>
      boundaryAtom ∈ datumTightSupport data.tightDir (data.basisLabel slot)).card := by
  obtain ⟨otherSlot, hne, hmemOther, hliveOther⟩ :=
    data.exists_live_cocarrier hdiag hbnd hmemLive hpos hmemInterior
  have hpairSub : ({liveSlot, otherSlot} : Finset (Fin data.basisCount))
      ⊆ data.liveSlots.filter fun slot =>
        boundaryAtom ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro slot hslot
    rcases Finset.mem_insert.mp hslot with hcase | hcase
    · rw [hcase]
      exact Finset.mem_filter.mpr
        ⟨(data.mem_liveSlots liveSlot).mpr ⟨interiorAtom, hpos, hmemInterior⟩, hmemLive⟩
    · rw [Finset.mem_singleton.mp hcase]
      exact Finset.mem_filter.mpr
        ⟨(data.mem_liveSlots otherSlot).mpr hliveOther, hmemOther⟩
  have hpairCard : ({liveSlot, otherSlot} : Finset (Fin data.basisCount)).card = 2 :=
    Finset.card_pair (Ne.symm hne)
  have := Finset.card_le_card hpairSub
  omega

/-! ## Layer 6 — the boundary pair star -/

set_option maxHeartbeats 3200000 in
/-- **THE BOUNDARY PAIR STAR.**  A boundary atom with a two-slot
carrier makes the two idempotent columns proportional.  If every slot
is dead, is the base slot, or shares a boundary pair atom with the base
slot, every column is a multiple of the base column, thus the trace is
one or zero.  The trace two refuses it. -/
theorem SharedPrivateData.false_of_boundary_pair_star {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) (baseSlot : Fin data.basisCount)
    (hstar : ∀ slot : Fin data.basisCount, slot ≠ baseSlot →
      (∀ probe : Fin 6,
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight probe →
        probe ∉ datumTightSupport data.tightDir (data.basisLabel slot))
      ∨ (∃ pairAtom : Fin 6,
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight pairAtom = 0
          ∧ pairAtom ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ ∀ otherSlot : Fin data.basisCount, otherSlot ≠ slot →
              otherSlot ≠ baseSlot →
              pairAtom ∉ datumTightSupport data.tightDir
                (data.basisLabel otherSlot))) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, _hread, _hnorm,
    hboundary, hcarrierNz, hdeadCol⟩ := data.exists_dead_read_frame hdiag
  have hpar : ∀ slot : Fin data.basisCount, ∃ scale : ℝ,
      kernelColumn S slot
        = fun rowIdx => scale * kernelColumn S baseSlot rowIdx := by
    intro slot
    by_cases hbase : slot = baseSlot
    · exact ⟨1, by rw [hbase]; funext rowIdx; ring⟩
    rcases hstar slot hbase with hdead | ⟨pairAtom, hbnd, hmemSlot, hother⟩
    · refine ⟨0, ?_⟩
      funext rowIdx
      show S rowIdx slot = 0 * kernelColumn S baseSlot rowIdx
      rw [hdeadCol slot hdead rowIdx, zero_mul]
    · have hzero := hboundary pairAtom hbnd
      have hnzSlot := hcarrierNz pairAtom slot hmemSlot
      -- the relation reads the two live columns of the pair carrier
      have hcol : ∀ rowSlot : Fin data.basisCount,
          S rowSlot slot * readVecs pairAtom slot
            + S rowSlot baseSlot * readVecs pairAtom baseSlot = 0 := by
        intro rowSlot
        have hentry := congrFun hzero rowSlot
        have hval : (S *ᵥ readVecs pairAtom) rowSlot
            = ∑ probeSlot, S rowSlot probeSlot * readVecs pairAtom probeSlot := rfl
        rw [hval] at hentry
        have hsplit : (∑ probeSlot, S rowSlot probeSlot * readVecs pairAtom probeSlot)
            = S rowSlot slot * readVecs pairAtom slot
              + S rowSlot baseSlot * readVecs pairAtom baseSlot := by
          have hpairSub : ({slot, baseSlot} : Finset (Fin data.basisCount))
              ⊆ Finset.univ := Finset.subset_univ _
          rw [← Finset.sum_subset hpairSub (fun probeSlot _ hnotMem => ?_)]
          · rw [Finset.sum_pair hbase]
          · have hne : probeSlot ≠ slot ∧ probeSlot ≠ baseSlot := by
              constructor <;> intro hcase <;>
                exact hnotMem (by rw [hcase]; simp)
            rw [hsuppFrame pairAtom probeSlot (hother probeSlot hne.1 hne.2), mul_zero]
        rw [hsplit] at hentry
        exact hentry
      refine ⟨-(readVecs pairAtom baseSlot / readVecs pairAtom slot), ?_⟩
      funext rowIdx
      show S rowIdx slot
        = -(readVecs pairAtom baseSlot / readVecs pairAtom slot) * S rowIdx baseSlot
      have hentry := hcol rowIdx
      field_simp
      linarith [hentry]
  choose scale hscale using hpar
  refine false_of_parallel_columns hSsymm hSidem baseSlot scale hscale ?_
  rw [hStrace, htrace]

/-! ## Layer 7 — the residue after the confinement layer -/

/-- **THE CONFINED BASIS-COUNT-FIVE RESIDUE.**  The narrowed
basis-count-five residue with the dead propagation and the interior
leak added: **a boundary carrier never holds exactly one live slot**,
and **every interior atom misses a live slot**. -/
def SharedPrivateBoundaryFiveConfinedClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 2 →
    data.basisCount = 5 →
    data.coeff data.privateSlot data.privateSlot = 0 →
    (∀ atomIndex : Fin 6,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1 →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) →
    (∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot) →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) →
    (∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex →
      atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot)) →
    (∀ atomIndex : Fin 6,
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex →
      2 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex) →
    2 ≤ (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card →
    (Finset.univ.filter fun atomIndex =>
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex).card ≤ 3 →
    (∃ (slot : Fin data.basisCount) (atomOne : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomOne
        ∧ atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∀ atomTwo : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atomTwo →
            atomTwo ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
            atomTwo = atomOne) →
    (∀ (boundaryAtom : Fin 6),
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight boundaryAtom = 0 →
      ∀ (liveSlot : Fin data.basisCount) (interiorAtom : Fin 6),
        boundaryAtom ∈ datumTightSupport data.tightDir (data.basisLabel liveSlot) →
        0 < chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight interiorAtom →
        interiorAtom ∈ datumTightSupport data.tightDir (data.basisLabel liveSlot) →
        ∃ otherSlot : Fin data.basisCount, otherSlot ≠ liveSlot
          ∧ boundaryAtom ∈ datumTightSupport data.tightDir
              (data.basisLabel otherSlot)
          ∧ ∃ probe : Fin 6,
              0 < chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight probe
              ∧ probe ∈ datumTightSupport data.tightDir
                  (data.basisLabel otherSlot)) →
    (∀ (interiorAtom : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight interiorAtom →
      ∃ slot : Fin data.basisCount,
        interiorAtom ∉ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∃ probe : Fin 6,
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight probe
            ∧ probe ∈ datumTightSupport data.tightDir (data.basisLabel slot)) →
    False

/-- **THE CONFINED DISPATCH.**  The confined residue closes the
narrowed basis-count-five residue: the dead propagation and the
interior leak are theorems. -/
theorem sharedPrivateBoundaryFiveCoreClosed_of_confined
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    SharedPrivateBoundaryFiveCoreClosed := by
  intro crux data gramDiag hdiag htrace hbasis hpin hmultOne hprivate hinteriorOut
    hthick hlow hhigh hsingle
  exact hconfined crux data gramDiag hdiag htrace hbasis hpin hmultOne hprivate
    hinteriorOut hthick hlow hhigh hsingle
    (fun boundaryAtom hbnd liveSlot interiorAtom hmemLive hpos hmemInterior =>
      data.exists_live_cocarrier hdiag hbnd hmemLive hpos hmemInterior)
    (fun interiorAtom hpos => data.exists_live_slot_offCarrier hdiag hpos)

/-- The confined residue closes the whole trace-two boundary residue. -/
theorem sharedPrivateBoundaryClosed_of_confined
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    SharedPrivateBoundaryClosed :=
  sharedPrivateBoundaryClosed_of_core
    (sharedPrivateBoundaryFiveCoreClosed_of_confined hconfined)

/-- **THE STRATA DISPATCH.**  The extras residue and the confined
basis-count-five residue close the generic shared-private kill: the
deficit stratum is a theorem. -/
theorem sharedPrivateKilled_of_confined_strata
    (hextras : SharedPrivateExtrasClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) : SharedPrivateKilled :=
  sharedPrivateKilled_of_core_strata hextras
    (sharedPrivateBoundaryFiveCoreClosed_of_confined hconfined)
    sharedPrivateDeficitClosed_holds

/-- The two residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_confined_strata
    (hextras : SharedPrivateExtrasClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_confined_strata hextras hconfined)

/-- The two residues discharge the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_confined_strata
    (hextras : SharedPrivateExtrasClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_confined_strata hextras hconfined)

/-- The two residues discharge the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_confined_strata
    (hextras : SharedPrivateExtrasClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_confined_strata hextras hconfined)

end Gtz
