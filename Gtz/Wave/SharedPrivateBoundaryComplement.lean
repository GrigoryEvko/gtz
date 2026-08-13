import Gtz.Wave.SharedPrivateBoundaryDispatch
import Gtz.Wave.SharedPrivateKernelMinor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-private boundary complement — the rank-four boundary is one
named shape

The boundary dispatch made the trace-two stratum rigid at basis count
four: every atom with three or more carriers has exactly three carriers.
The kernel-minor budget kills a trace-two kernel projector when every
slot pair shares a support atom.  At basis count four the coefficient
trace two gives kernel trace two, thus the two results meet and the
whole rank-four boundary stratum reduces to the shapes with a disjoint
slot pair.

The kernel frame.  The complement of the conjugated coefficient matrix
is a symmetric idempotent with trace `basisCount - trace`.  A carrier
read at the shifted weight becomes a carrier read at one minus the
shifted weight.  The shifted weights sit in the interval from zero to
one, thus the complementary reads sit in the same interval, and their
total is `5 - 6 * value`, which is more than five at a negative value.

The multiplicity cap.  The rank-four rigidity gives every atom at most
three carriers, thus the carrier cards obey the kernel-minor hypothesis
with no more work.

The disjoint pair.  Two supports of card three that miss each other
partition the six atoms.  The pin atom sits in exactly one support, thus
one member of a disjoint slot pair is the pinned slot, and the other
support is the complement of the pinned support.  As a result the
rank-four boundary residue carries a slot whose support is exactly the
complement of the private support.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SharedPrivateData.multiplicity_le_three_of_basisCount_four` — the
  carrier cap of the rank-four rigidity.
* `Gtz.SharedPrivateData.false_of_basisCount_four_shared_slots` — **THE
  RANK-FOUR MINOR KILL.**
* `Gtz.SharedPrivateData.support_card_three`,
  `Gtz.SharedPrivateData.union_eq_univ_of_disjoint_supports` — the
  partition law of a disjoint support pair.
* `Gtz.SharedPrivateData.privateSlot_mem_of_disjoint_supports` — **THE
  PIN LAW OF A DISJOINT PAIR.**
* `Gtz.SharedPrivateData.exists_complement_slot_of_not_shared` — the
  complement slot.
* `Gtz.SharedPrivateComplementSlotClosed` — **THE NARROWED RANK-FOUR
  RESIDUE.**
* `Gtz.sharedPrivateBoundaryFourClosed_of_complementSlot` — the rank-four
  bridge.
* `Gtz.sharedPrivateBoundaryClosed_of_complement`,
  `Gtz.sharedPrivateKilled_of_complement_strata` — the dispatches.
* `Gtz.rankFourSharedPrivateClosed_of_complement_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_complement_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_complement_strata` — the rung
  compositions.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the carrier cap of the rank-four rigidity -/

/-- Every atom of a rank-four trace-two datum carries at most three
slots.  The rigidity pins the three-or-more class at exactly three. -/
theorem SharedPrivateData.multiplicity_le_three_of_basisCount_four
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) (hbasis : data.basisCount = 4)
    (atomIndex : Fin 6) :
    basisSupportMultiplicity data.tightDir data.basisLabel atomIndex ≤ 3 := by
  obtain ⟨hexact, _hbnd, _hcards⟩ :=
    data.boundary_rigid_of_basisCount_four hdiag htrace hbasis
  by_cases hbig : 3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
    atomIndex
  · exact le_of_eq (hexact atomIndex hbig)
  · omega

/-! ## Layer 2 — the rank-four minor kill -/

set_option maxHeartbeats 3200000 in
/-- **THE RANK-FOUR MINOR KILL.**  A diagonal-Gram datum at basis count
four and coefficient trace two, with every slot pair sharing a support
atom, dies.  The complement of the conjugated coefficient matrix is a
symmetric idempotent of trace two, the carriers are at most three slots
wide by the rank-four rigidity, and the complementary reads total more
than five at a negative chart value. -/
theorem SharedPrivateData.false_of_basisCount_four_shared_slots
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) (hbasis : data.basisCount = 4)
    (hshare : ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
          ∧ atomIndex ∈ datumTightSupport data.tightDir
            (data.basisLabel slotTwo)) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hreadFrame,
    _hnorm, hnz, _hboundary, _hcarrierNz, _hspan, _hcommute⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design)
    with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  set car : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcar
  set kernelVal : Fin 6 → ℝ := fun atomIndex =>
    1 - (chartValue + atomWeight atomIndex) with hkernelVal
  have hcarmem : ∀ atomIndex slot, slot ∈ car atomIndex ↔
      atomIndex ∈ datumTightSupport data.tightDir
        (data.basisLabel slot) := by
    intro atomIndex slot
    simp [hcar]
  have hmemActive : ∀ slot, data.basisLabel slot ∈ data.activeSet := by
    intro slot
    have hmem := data.hmem slot
    simp only [positiveActiveSet, Finset.mem_filter] at hmem
    exact hmem.1
  -- the complementary idempotent
  set K : Matrix (Fin data.basisCount) (Fin data.basisCount) ℝ := 1 - S
    with hK
  have hKsymm : Kᵀ = K := by
    rw [hK, Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hKidem : K * K = K := by
    rw [hK]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hSidem]
    abel
  have hcast : (data.basisCount : ℝ) = 4 := by rw [hbasis]; norm_num
  have hKtrace : Matrix.trace K = 2 := by
    rw [hK, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hStrace,
      htrace, hcast]
    norm_num
  -- the carrier data
  have hcard : ∀ atomIndex, (car atomIndex).card ≤ 3 :=
    fun atomIndex =>
      data.multiplicity_le_three_of_basisCount_four hdiag htrace hbasis
        atomIndex
  have hinc : ∀ slot : Fin data.basisCount,
      (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex).card = 3 := by
    intro slot
    have hpred : (Finset.univ.filter fun atomIndex => slot ∈ car atomIndex)
        = datumTightSupport data.tightDir (data.basisLabel slot) := by
      have hcongr : (Finset.univ.filter fun atomIndex =>
          slot ∈ car atomIndex)
          = Finset.univ.filter fun atomIndex =>
              atomIndex ∈ datumTightSupport data.tightDir
                (data.basisLabel slot) :=
        Finset.filter_congr fun atomIndex _ => by rw [hcarmem]
      rw [hcongr, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hpred]
    exact data.hthree slot
  have hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    exact hsuppFrame atomIndex slot fun hmem =>
      hslot ((hcarmem atomIndex slot).mpr hmem)
  have hnzCar : ∀ atomIndex, ∃ slot ∈ car atomIndex,
      readVecs atomIndex slot ≠ 0 := by
    intro atomIndex
    obtain ⟨slot, hslot⟩ := Function.ne_iff.mp (hnz atomIndex)
    have hne : readVecs atomIndex slot ≠ 0 := by simpa using hslot
    refine ⟨slot, ?_, hne⟩
    by_contra hnot
    exact hne (hsupp atomIndex slot hnot)
  have hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (K *ᵥ readVecs atomIndex) slot
        = kernelVal atomIndex * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    have hS := hreadFrame atomIndex slot (datumTightSupport_subset data.hdata
      (hmemActive slot) ((hcarmem atomIndex slot).mp hslot))
    have hexpand : (K *ᵥ readVecs atomIndex) slot
        = readVecs atomIndex slot - (S *ᵥ readVecs atomIndex) slot := by
      rw [hK, Matrix.sub_mulVec, Matrix.one_mulVec]
      rfl
    rw [hexpand, hS]
    show readVecs atomIndex slot
        - (chartValue + atomWeight atomIndex) * readVecs atomIndex slot
      = (1 - (chartValue + atomWeight atomIndex)) * readVecs atomIndex slot
    ring
  -- the complementary window and total
  have hshiftNonneg : ∀ atomIndex : Fin 6,
      0 ≤ chartValue + atomWeight atomIndex := fun atomIndex =>
    capture_diagonal_nonneg_of_isChartStationaryData data.hdata atomIndex
  have hshiftLtOne : ∀ atomIndex : Fin 6,
      chartValue + atomWeight atomIndex < 1 := by
    intro atomIndex
    have hwle : atomWeight atomIndex ≤ 1 := by
      have hsumOne := data.hdata.weight_sum_one
      have hle : atomWeight atomIndex ≤ ∑ y, atomWeight y :=
        Finset.single_le_sum (f := atomWeight)
          (fun y _ => (data.hdata.weight_pos y).le)
          (Finset.mem_univ atomIndex)
      rwa [hsumOne] at hle
    have hneg : chartValue < 0 := data.hvalueNeg
    linarith
  have hpos : ∀ atomIndex, 0 < kernelVal atomIndex := by
    intro atomIndex
    have h := hshiftLtOne atomIndex
    show 0 < 1 - (chartValue + atomWeight atomIndex)
    linarith
  have hcap : ∀ atomIndex, kernelVal atomIndex ≤ 1 := by
    intro atomIndex
    have h := hshiftNonneg atomIndex
    show 1 - (chartValue + atomWeight atomIndex) ≤ 1
    linarith
  have hsumShift : ∑ atomIndex : Fin 6,
      (chartValue + atomWeight atomIndex) = 6 * chartValue + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, data.hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  have hsum : 5 < ∑ atomIndex, kernelVal atomIndex := by
    have hexpand : ∑ atomIndex : Fin 6, kernelVal atomIndex
        = ∑ atomIndex : Fin 6,
          (1 - (chartValue + atomWeight atomIndex)) := rfl
    rw [hexpand, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsumShift]
    have hneg : chartValue < 0 := data.hvalueNeg
    norm_num
    linarith
  -- the slot pairs share a carrier atom
  have hco : ∀ rowSlot colSlot : Fin data.basisCount, rowSlot ≠ colSlot →
      ∃ atomIndex, rowSlot ∈ car atomIndex ∧ colSlot ∈ car atomIndex := by
    intro rowSlot colSlot hne
    obtain ⟨atomIndex, hone, htwo⟩ := hshare rowSlot colSlot hne
    exact ⟨atomIndex, (hcarmem atomIndex rowSlot).mpr hone,
      (hcarmem atomIndex colSlot).mpr htwo⟩
  exact false_of_kernelMinor_budget hKsymm hKidem hKtrace car readVecs
    kernelVal hcard hinc hsupp hnzCar hread hpos hcap hco hsum

/-! ## Layer 3 — the partition law of a disjoint support pair -/

/-- Every basis support has three atoms. -/
theorem SharedPrivateData.support_card_three {crux : SixThreeCrux}
    (data : SharedPrivateData crux) (slot : Fin data.basisCount) :
    (datumTightSupport data.tightDir (data.basisLabel slot)).card = 3 :=
  data.hthree slot

/-- Two supports that miss each other partition the six atoms: the two
cards total six. -/
theorem SharedPrivateData.union_eq_univ_of_disjoint_supports
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount}
    (hdisj : ∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
      atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel slotTwo)) :
    datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∪ datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = Finset.univ := by
  classical
  have hdisjoint : Disjoint
      (datumTightSupport data.tightDir (data.basisLabel slotOne))
      (datumTightSupport data.tightDir (data.basisLabel slotTwo)) :=
    Finset.disjoint_left.mpr hdisj
  have hcard : (datumTightSupport data.tightDir (data.basisLabel slotOne)
      ∪ datumTightSupport data.tightDir (data.basisLabel slotTwo)).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisjoint, data.support_card_three,
      data.support_card_three]
  refine Finset.eq_univ_of_card _ ?_
  rw [hcard, Fintype.card_fin]

/-- **THE PIN LAW OF A DISJOINT PAIR.**  One member of a disjoint
support pair is the pinned slot.  The two supports cover every atom, the
pin atom sits in one of them, and the pin atom has multiplicity one. -/
theorem SharedPrivateData.privateSlot_mem_of_disjoint_supports
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount}
    (hdisj : ∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
      atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel slotTwo)) :
    slotOne = data.privateSlot ∨ slotTwo = data.privateSlot := by
  classical
  have hunion := data.union_eq_univ_of_disjoint_supports hdisj
  have hmem : data.pinAtom
      ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∪ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hunion]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hmem with hone | htwo
  · exact Or.inl (data.pin_only_slot hone)
  · exact Or.inr (data.pin_only_slot htwo)

/-- **THE COMPLEMENT SLOT.**  When some slot pair shares no atom, the
datum carries a slot whose support is the complement of the private
support.  The pin law names the pinned slot, and the partition law makes
the partner support the complement. -/
theorem SharedPrivateData.exists_complement_slot_of_not_shared
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    (hnot : ¬ ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
          ∧ atomIndex ∈ datumTightSupport data.tightDir
            (data.basisLabel slotTwo)) :
    ∃ slot : Fin data.basisCount, slot ≠ data.privateSlot
      ∧ datumTightSupport data.tightDir (data.basisLabel slot)
        = (datumTightSupport data.tightDir
            (data.basisLabel data.privateSlot))ᶜ := by
  classical
  push Not at hnot
  obtain ⟨slotOne, slotTwo, hne, hmiss⟩ := hnot
  have hdisj : ∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
      atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel slotTwo) := by
    intro atomIndex hone htwo
    exact hmiss atomIndex hone htwo
  have hdisjSymm : ∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) →
      atomIndex ∉ datumTightSupport data.tightDir
        (data.basisLabel slotOne) := by
    intro atomIndex htwo hone
    exact hmiss atomIndex hone htwo
  -- the complement reading of a disjoint pair with total card six
  have hcompl : ∀ slotA slotB : Fin data.basisCount,
      (∀ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotA) →
        atomIndex ∉ datumTightSupport data.tightDir
          (data.basisLabel slotB)) →
      datumTightSupport data.tightDir (data.basisLabel slotB)
        = (datumTightSupport data.tightDir (data.basisLabel slotA))ᶜ := by
    intro slotA slotB hAB
    have hunion := data.union_eq_univ_of_disjoint_supports hAB
    ext atomIndex
    rw [Finset.mem_compl]
    constructor
    · intro hB hA
      exact hAB atomIndex hA hB
    · intro hA
      have hmem : atomIndex
          ∈ datumTightSupport data.tightDir (data.basisLabel slotA)
            ∪ datumTightSupport data.tightDir (data.basisLabel slotB) := by
        rw [hunion]
        exact Finset.mem_univ _
      rcases Finset.mem_union.mp hmem with h | h
      · exact absurd h hA
      · exact h
  rcases data.privateSlot_mem_of_disjoint_supports hdisj with hone | htwo
  · refine ⟨slotTwo, ?_, ?_⟩
    · rw [← hone]
      exact fun hcontra => hne hcontra.symm
    · rw [← hone]
      exact hcompl slotOne slotTwo hdisj
  · refine ⟨slotOne, ?_, ?_⟩
    · rw [← htwo]
      exact hne
    · rw [← htwo]
      exact hcompl slotTwo slotOne hdisjSymm

/-! ## Layer 4 — the narrowed rank-four residue and the dispatches -/

/-- **THE NARROWED RANK-FOUR RESIDUE.**  A diagonal-Gram datum at basis
count four and trace two, with the rank-four rigidity and with a slot
whose support is the complement of the private support, dies.  Every
other rank-four shape falls to the minor kill, to the disjoint-family
kill, or to the boundary budget. -/
def SharedPrivateComplementSlotClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 2 →
    data.basisCount = 4 →
    (∀ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex →
      basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex = 3) →
    (∀ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0) →
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex = 1).card
      = (Finset.univ.filter fun atomIndex =>
          3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
            atomIndex).card →
    (∃ slot : Fin data.basisCount, slot ≠ data.privateSlot
      ∧ datumTightSupport data.tightDir (data.basisLabel slot)
        = (datumTightSupport data.tightDir
            (data.basisLabel data.privateSlot))ᶜ) →
    False

/-- **THE RANK-FOUR BRIDGE.**  The complement residue closes the whole
rank-four boundary residue.  A datum with every slot pair sharing an
atom dies by the minor kill, and any other datum carries the complement
slot. -/
theorem sharedPrivateBoundaryFourClosed_of_complementSlot
    (hcompl : SharedPrivateComplementSlotClosed) :
    SharedPrivateBoundaryFourClosed := by
  intro crux data gramDiag hdiag htrace hbasis hexact hbnd hcards _hco
    _atomIndex _hmult _hzero
  classical
  by_cases hshare : ∀ slotOne slotTwo : Fin data.basisCount,
    slotOne ≠ slotTwo →
    ∃ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
        ∧ atomIndex ∈ datumTightSupport data.tightDir
          (data.basisLabel slotTwo)
  · exact data.false_of_basisCount_four_shared_slots hdiag htrace hbasis
      hshare
  · exact hcompl crux data gramDiag hdiag htrace hbasis hexact hbnd hcards
      (data.exists_complement_slot_of_not_shared hshare)

/-- **THE BOUNDARY DISPATCH.**  The complement residue and the high
residue close the trace-two boundary residue. -/
theorem sharedPrivateBoundaryClosed_of_complement
    (hcompl : SharedPrivateComplementSlotClosed)
    (hhigh : SharedPrivateBoundaryHighClosed) :
    SharedPrivateBoundaryClosed :=
  sharedPrivateBoundaryClosed_of_split
    (sharedPrivateBoundaryFourClosed_of_complementSlot hcompl) hhigh

/-- **THE STRATA DISPATCH.**  The extras residue, the complement
residue, the high boundary residue, and the deficit residue close the
generic shared-private kill. -/
theorem sharedPrivateKilled_of_complement_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcompl : SharedPrivateComplementSlotClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_strata hextras
    (sharedPrivateBoundaryClosed_of_complement hcompl hhigh) hdeficit

/-- The four residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_complement_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcompl : SharedPrivateComplementSlotClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_complement_strata hextras hcompl hhigh hdeficit)

/-- The four residues discharge the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_complement_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcompl : SharedPrivateComplementSlotClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_complement_strata hextras hcompl hhigh hdeficit)

/-- The four residues discharge the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_complement_strata
    (hextras : SharedPrivateExtrasClosed)
    (hcompl : SharedPrivateComplementSlotClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_complement_strata hextras hcompl hhigh hdeficit)

end Gtz
