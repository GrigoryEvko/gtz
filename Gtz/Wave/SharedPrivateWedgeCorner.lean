import Gtz.Wave.SharedPrivateLeakBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The wedge corner — the shared pure pair closes the live wedge at basis
count four

The corner defect kill never used the identical supports: the pure pair
corner lemmas read two shared pure atoms of ANY two basis slots, and the
wedge of the value pairs is a hypothesis of the live-wedge residue.
This module generalizes the corner defect kill to two slots with
DIFFERENT supports that share two pure atoms, and dispatches the whole
shape at basis count at most four.

## The general link kill

Two basis slots share the pure atoms `Y`, `Z` with a nonzero value
wedge.  The two other slots share a live atom outside both supports.
The corner defect law fires verbatim: the pure pair pins the left
corner, the trace and the two row laws at the shared atom pin the right
corner, and the two defect determinants disagree in sign.

## The general dispatch

If every slot outside the pair keeps a private atom, the landed trace
cover kill fires.  Otherwise some slot `s` has none, its support is
forced onto the complement of the pure pair and the pin, and the pinned
slot either reaches that complement outside both supports — the link
kill — or hides inside the two foreign atoms and the pin, and then the
sixth atom is private to `s`.  Thus two shared pure atoms with a nonzero
wedge and a pinned slot outside the pair force at least five basis
slots.  The counted live-wedge residue carries that floor.

## Vacuity

The statements quantify over shared-private data, and no shared-private
datum exists if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-! ## Layer 1 — the general link kill -/

/-- **THE GENERAL LINK KILL.**  Two basis slots with two shared pure
atoms and a nonzero value wedge, and two further slots that share a live
atom outside both supports, refuse the four-slot basis.  The identical
kill is the instance `atomW1 = atomW2`. -/
theorem false_of_pureShared_offTriple_link (data : SharedPrivateData crux)
    {slotOne slotTwo slotP slotS : Fin data.basisCount}
    (hne : slotOne ≠ slotTwo)
    (hPone : slotP ≠ slotOne) (hPtwo : slotP ≠ slotTwo)
    (hSone : slotS ≠ slotOne) (hStwo : slotS ≠ slotTwo) (hPS : slotP ≠ slotS)
    (huniv : (Finset.univ : Finset (Fin data.basisCount))
      = {slotOne, slotTwo, slotP, slotS})
    {atomY atomZ atomW1 atomW2 atomX : Fin 6} (hYZ : atomY ≠ atomZ)
    (hXY : atomX ≠ atomY) (hXZ : atomX ≠ atomZ)
    (hXW1 : atomX ≠ atomW1) (hXW2 : atomX ≠ atomW2)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomY, atomZ, atomW1})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomY, atomZ, atomW2})
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0)
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hXmemP : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotP))
    (hXmemS : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotS)) :
    False := by
  classical
  have hdeadOneX : data.tightDir (data.basisLabel slotOne) atomX = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportOne]; simp [hXY, hXZ, hXW1])
  have hdeadTwoX : data.tightDir (data.basisLabel slotTwo) atomX = 0 :=
    data.basis_dead_of_notMem_support
      (by rw [hsupportTwo]; simp [hXY, hXZ, hXW2])
  have hliveP : data.tightDir (data.basisLabel slotP) atomX ≠ 0 :=
    data.basis_live_of_mem_support hXmemP
  have hliveS : data.tightDir (data.basisLabel slotS) atomX ≠ 0 :=
    data.basis_live_of_mem_support hXmemS
  have hentry : ∀ rowIdx colIdx : Fin data.basisCount,
      data.coeff rowIdx slotOne * data.coeff slotOne colIdx
        + (data.coeff rowIdx slotTwo * data.coeff slotTwo colIdx
        + (data.coeff rowIdx slotP * data.coeff slotP colIdx
        + data.coeff rowIdx slotS * data.coeff slotS colIdx)) = data.coeff rowIdx colIdx := by
    intro rowIdx colIdx
    have hmul := congrFun (congrFun data.hidempotent rowIdx) colIdx
    rw [Matrix.mul_apply, huniv,
      Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
      Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
      Finset.sum_insert (by simp [hPS]), Finset.sum_singleton] at hmul
    exact hmul
  have hrowP := data.basisRow_capture slotP hXmemP
  rw [huniv, Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
    Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
    Finset.sum_insert (by simp [hPS]), Finset.sum_singleton,
    hdeadOneX, hdeadTwoX, zero_mul, zero_mul, zero_add, zero_add] at hrowP
  have hrowS := data.basisRow_capture slotS hXmemS
  rw [huniv, Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
    Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
    Finset.sum_insert (by simp [hPS]), Finset.sum_singleton,
    hdeadOneX, hdeadTwoX, zero_mul, zero_mul, zero_add, zero_add] at hrowS
  have hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hcornerTr := data.purePair_corner_trace hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  have hcornerDet := data.purePair_corner_det hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  have htraceExpand : data.coeff slotOne slotOne + (data.coeff slotTwo slotTwo
      + (data.coeff slotP slotP + data.coeff slotS slotS)) = Matrix.trace data.coeff := by
    rw [data.trace_coeff_eq_sum, huniv,
      Finset.sum_insert (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
      Finset.sum_insert (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
      Finset.sum_insert (by simp [hPS]), Finset.sum_singleton]
  have hdYpos := crux.shifted_weight_pos atomY
  have hdZpos := crux.shifted_weight_pos atomZ
  have hdXpos := crux.shifted_weight_pos atomX
  have htriple := data.captureDiag_triple_le_total hYZ (Ne.symm hXY) (Ne.symm hXZ)
  have htotal := data.sum_captureDiag_lt_one
  exact cornerDefect_pair_kill
    (hentry slotOne slotOne) (hentry slotOne slotTwo)
    (hentry slotTwo slotOne) (hentry slotTwo slotTwo)
    (hentry slotP slotP) (hentry slotP slotS)
    (hentry slotS slotP) (hentry slotS slotS)
    hcornerTr hcornerDet htraceExpand data.two_le_trace_coeff
    hrowP hrowS hliveP hliveS hdYpos hdZpos hdXpos (by linarith)

/-! ## Layer 2 — the general dispatch at basis count at most four -/

/-- **THE SHARED PURE PAIR NEEDS FIVE SLOTS.**  Two basis slots with two
shared pure atoms and a nonzero value wedge, and a pinned slot outside
the pair, refuse every basis count up to four.  The supports of the two
slots may differ: this covers the identical branch and the live wedge
at once. -/
theorem false_of_pureShared_of_basisCount_le_four (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hPone : data.privateSlot ≠ slotOne) (hPtwo : data.privateSlot ≠ slotTwo)
    {atomY atomZ atomW1 atomW2 : Fin 6} (hYZ : atomY ≠ atomZ)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomY, atomZ, atomW1})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomY, atomZ, atomW2})
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0)
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hcount : data.basisCount ≤ 4) : False := by
  classical
  have hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  by_cases hallPriv : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      ∃ atomIndex : Fin 6,
        atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ ∀ other : Fin data.basisCount, other ≠ slot →
            data.tightDir (data.basisLabel other) atomIndex = 0
  · exact data.false_of_purePair_private_family hne hYZ hblockYone hblockYtwo
      hblockZone hblockZtwo hpureY hpureZ hwedge hallPriv
  · obtain ⟨slotS, hSbad⟩ := not_forall.mp hallPriv
    rw [Classical.not_imp, Classical.not_imp] at hSbad
    obtain ⟨hSone, hStwo, hSnoPriv⟩ := hSbad
    have hSp : slotS ≠ data.privateSlot := by
      intro heq
      refine hSnoPriv ⟨data.pinAtom, ?_, fun other hother => ?_⟩
      · rw [heq]; exact data.pinAtom_mem_privateSlot_support
      · rw [heq] at hother
        exact data.hprivate other hother
    -- the pin sits outside the two supports
    have hpinDeadOne : data.tightDir (data.basisLabel slotOne) data.pinAtom = 0 :=
      data.hprivate slotOne (Ne.symm hPone)
    have hpinDeadTwo : data.tightDir (data.basisLabel slotTwo) data.pinAtom = 0 :=
      data.hprivate slotTwo (Ne.symm hPtwo)
    have hpinY : data.pinAtom ≠ atomY := by
      intro heq
      exact data.basis_live_of_mem_support hblockYone (heq ▸ hpinDeadOne)
    have hpinZ : data.pinAtom ≠ atomZ := by
      intro heq
      exact data.basis_live_of_mem_support hblockZone (heq ▸ hpinDeadOne)
    have hpinW1 : data.pinAtom ≠ atomW1 := by
      intro heq
      refine data.basis_live_of_mem_support (slot := slotOne) ?_ hpinDeadOne
      rw [hsupportOne, heq]; simp
    have hpinW2 : data.pinAtom ≠ atomW2 := by
      intro heq
      refine data.basis_live_of_mem_support (slot := slotTwo) ?_ hpinDeadTwo
      rw [hsupportTwo, heq]; simp
    -- the four named slots exhaust the basis
    have hcard4 : ({slotOne, slotTwo, data.privateSlot, slotS}
        : Finset (Fin data.basisCount)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hne, Ne.symm hPone, Ne.symm hSone]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hPtwo, Ne.symm hStwo]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hSp]), Finset.card_singleton]
    have huniv : (Finset.univ : Finset (Fin data.basisCount))
        = {slotOne, slotTwo, data.privateSlot, slotS} := by
      refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
      rw [Finset.card_univ, Fintype.card_fin, hcard4]
      exact hcount
    -- the private-atom-free slot lives on the complement of the pure pair
    -- and the pin
    have hcompl : ((Finset.univ : Finset (Fin 6))
        \ {atomY, atomZ, data.pinAtom}).card = 3 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem (by simp [hYZ, Ne.symm hpinY]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hpinZ]), Finset.card_singleton]
    have hsubS : datumTightSupport data.tightDir (data.basisLabel slotS)
        ⊆ Finset.univ \ {atomY, atomZ, data.pinAtom} := by
      intro atomA hmemA
      have hliveA := data.basis_live_of_mem_support hmemA
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        rw [heq] at hliveA
        exact hliveA (hpureY slotS hSone hStwo)
      · intro heq
        rw [heq] at hliveA
        exact hliveA (hpureZ slotS hSone hStwo)
      · intro heq
        rw [heq] at hliveA
        exact hliveA (data.hprivate slotS hSp)
    have hsuppSeq : datumTightSupport data.tightDir (data.basisLabel slotS)
        = Finset.univ \ {atomY, atomZ, data.pinAtom} :=
      Finset.eq_of_subset_of_card_le hsubS
        (by rw [hcompl, data.hthree slotS])
    -- the pinned slot reaches outside the five named atoms, or hides
    by_cases hXex : ∃ atomX ∈ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot),
        atomX ∉ ({atomY, atomZ, atomW1, atomW2, data.pinAtom} : Finset (Fin 6))
    · obtain ⟨atomX, hXmemP, hXout⟩ := hXex
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hXout
      obtain ⟨hXY, hXZ, hXW1, hXW2, hXpin⟩ := hXout
      have hXmemS : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotS) := by
        rw [hsuppSeq, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, by simp [hXY, hXZ, hXpin]⟩
      exact data.false_of_pureShared_offTriple_link hne hPone hPtwo hSone hStwo
        (Ne.symm hSp) huniv hYZ hXY hXZ hXW1 hXW2 hsupportOne hsupportTwo hwedge
        hpureY hpureZ hXmemP hXmemS
    · -- the sixth atom is then private to the free slot
      have hsix : ((Finset.univ : Finset (Fin 6))
          \ {atomY, atomZ, atomW1, atomW2, data.pinAtom}).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, Fintype.card_fin]
        have hfive : ({atomY, atomZ, atomW1, atomW2, data.pinAtom}
            : Finset (Fin 6)).card ≤ 5 := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
          refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
          refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
          simp
        omega
      obtain ⟨atomSix, hSixMem⟩ := hsix
      rw [Finset.mem_sdiff] at hSixMem
      obtain ⟨-, hSixOut⟩ := hSixMem
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hSixOut
      obtain ⟨hSixY, hSixZ, hSixW1, hSixW2, hSixPin⟩ := hSixOut
      have hSixMemS : atomSix ∈ datumTightSupport data.tightDir
          (data.basisLabel slotS) := by
        rw [hsuppSeq, Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, by simp [hSixY, hSixZ, hSixPin]⟩
      refine hSnoPriv ⟨atomSix, hSixMemS, fun other hother => ?_⟩
      have hmemUniv : other ∈ (Finset.univ : Finset (Fin data.basisCount)) :=
        Finset.mem_univ other
      rw [huniv] at hmemUniv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemUniv
      rcases hmemUniv with rfl | rfl | rfl | rfl
      · exact data.basis_dead_of_notMem_support
          (by rw [hsupportOne]; simp [hSixY, hSixZ, hSixW1])
      · exact data.basis_dead_of_notMem_support
          (by rw [hsupportTwo]; simp [hSixY, hSixZ, hSixW2])
      · by_contra hlive
        exact hXex ⟨atomSix, mem_datumTightSupport.mpr hlive,
          by simp [hSixY, hSixZ, hSixW1, hSixW2, hSixPin]⟩
      · exact absurd rfl hother

end SharedPrivateData

/-! ## Layer 3 — the live-wedge residue above basis count four -/

/-- **THE COUNTED LIVE-WEDGE RESIDUE.**  The slot-split live-wedge
residue plus the new payment: two pure shared atoms with the pinned slot
outside the pair force at least five basis slots. -/
def SharedPrivateCircuitSplitWedgeCountClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomA atomB atomX atomY : Fin 6,
        atomA ≠ atomB → atomA ≠ atomX → atomA ≠ atomY →
        atomB ≠ atomX → atomB ≠ atomY → atomX ≠ atomY →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomA, atomB, atomX} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomA, atomB, atomY} →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotTwo)) atomX = 0 →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotOne)) atomY = 0 →
        data.tightDir (data.basisLabel slotOne) atomA
            * data.tightDir (data.basisLabel slotTwo) atomB
          - data.tightDir (data.basisLabel slotOne) atomB
            * data.tightDir (data.basisLabel slotTwo) atomA ≠ 0 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 2 →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomA
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomB
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomX
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomY ≤ 3 →
        -- two pure shared atoms with the pin outside the pair force five slots
        ((∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomA = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomB = 0) →
          data.privateSlot ≠ slotOne → data.privateSlot ≠ slotTwo →
          5 ≤ data.basisCount) →
        False

/-- **THE WEDGE COUNT PAYMENT BRIDGE.**  The five-slot floor of the
shared pure pair is a theorem at the datum, thus the counted live-wedge
residue closes the slot-split one. -/
theorem sharedPrivateCircuitSplitWedgeSlotClosed_of_count
    (hpaid : SharedPrivateCircuitSplitWedgeCountClosed) :
    SharedPrivateCircuitSplitWedgeSlotClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hforeignX hforeignY hwedge hbudgetOne hbudgetTwo htripleBXY htripleAXY hquad
  refine hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo
    hpair atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hforeignX hforeignY hwedge hbudgetOne hbudgetTwo htripleBXY htripleAXY hquad ?_
  intro hpureA hpureB hPone hPtwo
  by_contra hlt
  exact data.false_of_pureShared_of_basisCount_le_four hne hPone hPtwo hAB
    hsupportOne hsupportTwo hwedge hpureA hpureB (by omega)

/-! ## Layer 4 — closure two on the double-counted lattice -/

/-- **THE EXTRAS ON THE DOUBLE-COUNTED LATTICE.**  Both the identical
residue and the live-wedge residue carry their five-slot floors. -/
theorem sharedPrivateExtrasClosed_of_doubleCountLattice
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeCountClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_countLattice hidentical
    (sharedPrivateCircuitSplitWedgeSlotClosed_of_count hwedgeLive)
    hwedgeDead hwide

/-- **CLOSURE TWO FROM THE FOUR CIRCUIT RESIDUES ON THE DOUBLE-COUNTED
LATTICE.** -/
theorem sharedPrivateKilled_of_doubleCount_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeCountClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_count_circuit hidentical
    (sharedPrivateCircuitSplitWedgeSlotClosed_of_count hwedgeLive)
    hwedgeDead hwide

/-- Closure two of the rank-four rung on the double-counted lattice. -/
theorem rankFourSharedPrivateClosed_of_doubleCount_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeCountClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_count_circuit hidentical
    (sharedPrivateCircuitSplitWedgeSlotClosed_of_count hwedgeLive)
    hwedgeDead hwide

/-- The shared-private closure of the rank-five rung on the
double-counted lattice. -/
theorem rankFiveSharedPrivateClosed_of_doubleCount_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeCountClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_count_circuit hidentical
    (sharedPrivateCircuitSplitWedgeSlotClosed_of_count hwedgeLive)
    hwedgeDead hwide

/-- The shared-private closure of the rank-six rung on the
double-counted lattice. -/
theorem rankSixSharedPrivateClosed_of_doubleCount_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalCountClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeCountClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_count_circuit hidentical
    (sharedPrivateCircuitSplitWedgeSlotClosed_of_count hwedgeLive)
    hwedgeDead hwide

end Gtz
