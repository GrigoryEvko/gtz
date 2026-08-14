import Gtz.Wave.SharedPrivateWedgeCorner

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The complement eigenvalue law — a pure pair of shared atoms kills every
basis count

The corner defect engine of CERT-B20 read the two complementary corners
of the idempotent coefficient matrix through their defect determinants.
That reading needed a two-by-two complement, thus it stopped at basis
count four.  This module replaces it with a law that carries no size
restriction at all.

## The row shadow

Every atom carries a row of the basis columns.  Read against one column
of the coefficient matrix that row gives the ROW SHADOW of the atom at
that slot.  At an atom of a slot's own support the shadow is the
captured diagonal times the basis value: that is the landed basis row
law.  The shadow is also a fixed point of the coefficient matrix,
because the coefficient matrix is idempotent.

## The transfer law

Split the slots into the DEAD set of an atom and the rest.  The fixed
point identity splits with it: the live part contributes the captured
diagonal times the shadow, and the dead part contributes a small
combination of the dead shadows.  Thus at every slot

`shadow = captureDiag * shadow + (dead shadows against the dead rows)`.

Three consequences follow at once.

* A saturated atom, live at every basis slot, has an empty dead set.
  The transfer law then reads `d (1 - d) = 0` against a live value, and
  the interior window `0 < d < 1` refuses it.
* An atom whose dead set is one slot `p` reads `coeff p p = 1 - d`.  If
  that slot also carries a private atom, its diagonal is the private
  atom's captured diagonal, and two captured diagonals total one.  The
  capture total is less than one, thus the datum dies.
* An atom whose dead set is a pair of slots makes `1 - d` a root of the
  characteristic polynomial of the two-by-two corner on that pair.

## The census of a pure pair

Two atoms that live only on a named pair of slots pin the corner's
trace and determinant to the two captured diagonals.  Their purity also
empties them from every support outside the pair, thus the outside
supports draw three atoms each from the four remaining atoms.  The pin
atom has multiplicity one, thus at most one of those four outside
incidences belongs to it.  Counting forces TWO of the remaining three
atoms to be live at EVERY slot outside the pair.

Each of the two is then live at both slots of the pair, at neither, or
at exactly one.  The first case is a saturated atom.  The second makes
`1 - d` a root of `(t - dY) (t - dZ)`, thus one captured diagonal pair
totals one.  The third gives `coeff = 1 - d` on one diagonal of the
corner, and the two atoms cannot share a side because a support of
three atoms holds only one atom outside the pure pair.  The remaining
shape reads the corner trace as `2 - dP - dQ`, thus four captured
diagonals total two.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SharedPrivateData.rowShadow` with `rowShadow_eq_captureDiag` and
  `rowShadow_idempotent` — the row shadow frame.
* `Gtz.SharedPrivateData.rowShadow_transfer` — **THE TRANSFER LAW.**
* `Gtz.SharedPrivateData.false_of_saturated_atom` — **NO ATOM IS LIVE AT
  EVERY BASIS SLOT.**
* `Gtz.SharedPrivateData.coeffDiag_eq_one_sub_of_dead_single` — the
  single dead slot reads its own diagonal.
* `Gtz.SharedPrivateData.false_of_dead_only_at_privateSlot` — **THE PIN
  SLOT CARRIES NO SINGLE DEAD ATOM.**
* `Gtz.SharedPrivateData.charRoot_of_dead_pair` — the pair root law.
* `Gtz.SharedPrivateData.false_of_purePairComplement_atom` — the pure
  pair refuses an atom on its complement.
* `Gtz.SharedPrivateData.purePairAtom_charRoot` — **THE PURE ATOM IS A
  CORNER ROOT**, the mirror of the pair root law.
* `Gtz.SharedPrivateData.purePairAtom_corner_of_outerFull` — **THE
  CORNER FROM ONE PURE ATOM AND ONE OUTER ATOM.**  This reads the
  corner's trace and determinant with ONE pure atom, thus it supersedes
  the landed two-pure-atom corner reading in that regime.
* `Gtz.SharedPrivateData.captureDiag_eq_of_purePairAtom_of_two_outerFull`
  — two outer atoms against a pure atom share a captured diagonal.
* `Gtz.SharedPrivateData.exists_two_outerFull_atoms` — the census.
* `Gtz.SharedPrivateData.false_of_pureSharedPair` — **TWO SHARED PURE
  ATOMS KILL EVERY BASIS COUNT.**
* `Gtz.SharedPrivateCircuitPairIdenticalImpureClosed`,
  `Gtz.SharedPrivateCircuitSplitWedgeImpureClosed` — the two circuit
  residues with the pure branch handed over as a hypothesis.
* `Gtz.sharedPrivateKilled_of_impure_circuit` and the three rank
  bridges.

## Vacuity

The statements quantify over shared-private data, and no shared-private
datum exists if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-! ## Layer 0 — the capture total over a set of atoms -/

/-- A set of atoms carries at most the whole capture total. -/
theorem captureDiag_finset_le_total (data : SharedPrivateData crux)
    (atomSet : Finset (Fin 6)) :
    ∑ atomIndex ∈ atomSet, (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      ≤ ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun atomIndex _ _ => data.captureDiag_nonneg atomIndex

/-- A pair of distinct atoms carries at most the whole capture total. -/
theorem captureDiag_pair_le_total (data : SharedPrivateData crux)
    {atomA atomB : Fin 6} (hAB : atomA ≠ atomB) :
    (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomA)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomB)
      ≤ ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) := by
  classical
  have hsum := data.captureDiag_finset_le_total ({atomA, atomB} : Finset (Fin 6))
  rwa [Finset.sum_insert (by simp [hAB]), Finset.sum_singleton] at hsum

/-- A quadruple of distinct atoms carries at most the whole capture
total. -/
theorem captureDiag_quad_le_total (data : SharedPrivateData crux)
    {atomA atomB atomC atomD : Fin 6} (hAB : atomA ≠ atomB) (hAC : atomA ≠ atomC)
    (hAD : atomA ≠ atomD) (hBC : atomB ≠ atomC) (hBD : atomB ≠ atomD)
    (hCD : atomC ≠ atomD) :
    (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomA)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomB)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomC)
      + (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomD)
      ≤ ∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex) := by
  classical
  have hsum := data.captureDiag_finset_le_total
    ({atomA, atomB, atomC, atomD} : Finset (Fin 6))
  rw [Finset.sum_insert (by simp [hAB, hAC, hAD]),
    Finset.sum_insert (by simp [hBC, hBD]), Finset.sum_insert (by simp [hCD]),
    Finset.sum_singleton] at hsum
  linarith

/-! ## Layer 1 — the row shadow of an atom -/

/-- The row shadow of an atom at a basis slot: the atom's row of the
basis columns read against one column of the coefficient matrix. -/
noncomputable def rowShadow (data : SharedPrivateData crux) (atomIndex : Fin 6)
    (slot : Fin data.basisCount) : ℝ :=
  ∑ other : Fin data.basisCount,
    data.tightDir (data.basisLabel other) atomIndex * data.coeff other slot

/-- **THE SHADOW AT A LIVE SLOT.**  At an atom of a slot's own support
the row shadow is the captured diagonal times the basis value.  This is
the landed basis row law, renamed. -/
theorem rowShadow_eq_captureDiag (data : SharedPrivateData crux)
    {atomIndex : Fin 6} {slot : Fin data.basisCount}
    (hblock : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)) :
    data.rowShadow atomIndex slot
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.tightDir (data.basisLabel slot) atomIndex :=
  data.basisRow_capture slot hblock

/-- **THE SHADOW IS A FIXED POINT.**  The coefficient matrix is
idempotent, thus the row shadow reproduces itself against the
coefficient columns. -/
theorem rowShadow_idempotent (data : SharedPrivateData crux) (atomIndex : Fin 6)
    (slot : Fin data.basisCount) :
    ∑ other : Fin data.basisCount,
        data.rowShadow atomIndex other * data.coeff other slot
      = data.rowShadow atomIndex slot := by
  classical
  simp only [rowShadow, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun rowIdx _ => ?_
  have hentry := congrFun (congrFun data.hidempotent rowIdx) slot
  rw [Matrix.mul_apply] at hentry
  calc ∑ other : Fin data.basisCount,
        data.tightDir (data.basisLabel rowIdx) atomIndex * data.coeff rowIdx other
          * data.coeff other slot
      = data.tightDir (data.basisLabel rowIdx) atomIndex
          * ∑ other : Fin data.basisCount,
              data.coeff rowIdx other * data.coeff other slot := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun other _ => by ring
    _ = data.tightDir (data.basisLabel rowIdx) atomIndex * data.coeff rowIdx slot := by
        rw [hentry]

/-- **THE TRANSFER LAW.**  Split the slots into the dead set of an atom
and the rest.  The live part of the fixed point identity contributes the
captured diagonal times the shadow, and the dead part contributes the
dead shadows against the dead rows. -/
theorem rowShadow_transfer (data : SharedPrivateData crux) {atomIndex : Fin 6}
    {deadSet : Finset (Fin data.basisCount)}
    (hdead : ∀ slot ∈ deadSet, data.tightDir (data.basisLabel slot) atomIndex = 0)
    (hrow : ∀ slot ∉ deadSet, data.rowShadow atomIndex slot
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.tightDir (data.basisLabel slot) atomIndex)
    (slot : Fin data.basisCount) :
    data.rowShadow atomIndex slot
      = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * data.rowShadow atomIndex slot
        + ∑ dead ∈ deadSet, data.rowShadow atomIndex dead * data.coeff dead slot := by
  classical
  have hextend : ∑ other ∈ Finset.univ \ deadSet,
      data.tightDir (data.basisLabel other) atomIndex * data.coeff other slot
      = data.rowShadow atomIndex slot := by
    refine Finset.sum_subset Finset.sdiff_subset ?_
    intro other _ hnot
    have hmem : other ∈ deadSet := by
      by_contra hcontra
      exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcontra⟩)
    rw [hdead other hmem, zero_mul]
  have hlive : ∑ other ∈ Finset.univ \ deadSet,
      data.rowShadow atomIndex other * data.coeff other slot
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.rowShadow atomIndex slot := by
    rw [← hextend, Finset.mul_sum]
    refine Finset.sum_congr rfl fun other hother => ?_
    rw [hrow other (Finset.mem_sdiff.mp hother).2]
    ring
  calc data.rowShadow atomIndex slot
      = ∑ other : Fin data.basisCount,
          data.rowShadow atomIndex other * data.coeff other slot :=
        (data.rowShadow_idempotent atomIndex slot).symm
    _ = ∑ other ∈ Finset.univ \ deadSet,
            data.rowShadow atomIndex other * data.coeff other slot
          + ∑ dead ∈ deadSet, data.rowShadow atomIndex dead * data.coeff dead slot :=
        (Finset.sum_sdiff (Finset.subset_univ deadSet)).symm
    _ = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
            * data.rowShadow atomIndex slot
          + ∑ dead ∈ deadSet, data.rowShadow atomIndex dead * data.coeff dead slot := by
        rw [hlive]

/-- **THE DEAD SHADOWS CANNOT ALL VANISH.**  If every dead shadow of an
atom is zero, the transfer law reads the interior window `0 < d < 1`
against a live basis value. -/
theorem false_of_rowShadow_deadSet_eq_zero (data : SharedPrivateData crux)
    {atomIndex : Fin 6} {deadSet : Finset (Fin data.basisCount)}
    (hdead : ∀ slot ∈ deadSet, data.tightDir (data.basisLabel slot) atomIndex = 0)
    (hrow : ∀ slot ∉ deadSet, data.rowShadow atomIndex slot
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        * data.tightDir (data.basisLabel slot) atomIndex)
    (hzero : ∀ dead ∈ deadSet, data.rowShadow atomIndex dead = 0)
    {slot : Fin data.basisCount} (hout : slot ∉ deadSet)
    (hlive : data.tightDir (data.basisLabel slot) atomIndex ≠ 0) : False := by
  classical
  have htrans := data.rowShadow_transfer hdead hrow slot
  rw [Finset.sum_eq_zero (fun dead hmem => by rw [hzero dead hmem, zero_mul]),
    add_zero, hrow slot hout] at htrans
  have hdpos := crux.shifted_weight_pos atomIndex
  have hdlt := data.captureDiag_lt_one atomIndex
  have hproduct : (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex))
      * data.tightDir (data.basisLabel slot) atomIndex = 0 := by
    linear_combination htrans
  rcases mul_eq_zero.mp hproduct with hfirst | hsecond
  · rcases mul_eq_zero.mp hfirst with hd | hone
    · linarith
    · linarith
  · exact hlive hsecond

/-! ## Layer 2 — the three sizes of the dead set -/

/-- **NO ATOM IS LIVE AT EVERY BASIS SLOT.**  A saturated atom has an
empty dead set, and the transfer law then refuses the interior
window. -/
theorem false_of_saturated_atom (data : SharedPrivateData crux) {atomIndex : Fin 6}
    (hall : ∀ slot : Fin data.basisCount,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)) : False := by
  classical
  exact data.false_of_rowShadow_deadSet_eq_zero
    (deadSet := (∅ : Finset (Fin data.basisCount)))
    (fun slot hslot => absurd hslot (Finset.notMem_empty slot))
    (fun slot _ => data.rowShadow_eq_captureDiag (hall slot))
    (fun dead hdead => absurd hdead (Finset.notMem_empty dead))
    (Finset.notMem_empty data.privateSlot)
    (data.basis_live_of_mem_support (hall data.privateSlot))

/-- **EVERY ATOM HAS A DEAD SLOT.**  The saturated kill, contraposed. -/
theorem exists_dead_slot (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    ∃ slot : Fin data.basisCount,
      data.tightDir (data.basisLabel slot) atomIndex = 0 := by
  classical
  by_contra hnone
  push Not at hnone
  exact data.false_of_saturated_atom fun slot => mem_datumTightSupport.mpr (hnone slot)

/-- **THE MULTIPLICITY CEILING.**  No atom reaches every basis
support. -/
theorem basisMultiplicity_lt_basisCount (data : SharedPrivateData crux)
    (atomIndex : Fin 6) :
    basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
      < data.basisCount := by
  classical
  obtain ⟨slotDead, hslotDead⟩ := data.exists_dead_slot atomIndex
  have hsub : (Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot))
      ⊂ (Finset.univ : Finset (Fin data.basisCount)) := by
    refine Finset.ssubset_iff_of_subset (Finset.subset_univ _) |>.mpr ?_
    refine ⟨slotDead, Finset.mem_univ _, ?_⟩
    intro hmem
    exact data.basis_live_of_mem_support (Finset.mem_filter.mp hmem).2 hslotDead
  have hcard := Finset.card_lt_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

/-- **THE SINGLE DEAD SLOT READS ITS OWN DIAGONAL.**  An atom that is
dead at exactly one basis slot pins that slot's coefficient diagonal to
one minus its captured diagonal. -/
theorem coeffDiag_eq_one_sub_of_dead_single (data : SharedPrivateData crux)
    {atomIndex : Fin 6} {slotDead : Fin data.basisCount}
    (hdeadAt : data.tightDir (data.basisLabel slotDead) atomIndex = 0)
    (hlive : ∀ slot : Fin data.basisCount, slot ≠ slotDead →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    {slotLive : Fin data.basisCount} (hne : slotLive ≠ slotDead) :
    data.coeff slotDead slotDead
      = 1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) := by
  classical
  have hdead : ∀ slot ∈ ({slotDead} : Finset (Fin data.basisCount)),
      data.tightDir (data.basisLabel slot) atomIndex = 0 := by
    intro slot hslot
    rw [Finset.mem_singleton.mp hslot]
    exact hdeadAt
  have hrow : ∀ slot ∉ ({slotDead} : Finset (Fin data.basisCount)),
      data.rowShadow atomIndex slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * data.tightDir (data.basisLabel slot) atomIndex := by
    intro slot hslot
    exact data.rowShadow_eq_captureDiag
      (hlive slot fun heq => hslot (Finset.mem_singleton.mpr heq))
  have hshadowNe : data.rowShadow atomIndex slotDead ≠ 0 := by
    intro hzero
    refine data.false_of_rowShadow_deadSet_eq_zero hdead hrow ?_
      (slot := slotLive) (fun hmem => hne (Finset.mem_singleton.mp hmem))
      (data.basis_live_of_mem_support (hlive slotLive hne))
    intro dead hmem
    rw [Finset.mem_singleton.mp hmem]
    exact hzero
  have htrans := data.rowShadow_transfer hdead hrow slotDead
  rw [Finset.sum_singleton] at htrans
  have hfactor : data.rowShadow atomIndex slotDead
      * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)
        - data.coeff slotDead slotDead) = 0 := by
    linear_combination htrans
  have hsolve := (mul_eq_zero.mp hfactor).resolve_left hshadowNe
  linarith

/-- **THE PIN SLOT CARRIES NO SINGLE DEAD ATOM.**  The pinned slot's
coefficient diagonal is the pin atom's captured diagonal.  An atom dead
at exactly that slot would read the same diagonal as one minus its own
captured diagonal, thus two captured diagonals would total one against a
capture total below one. -/
theorem false_of_dead_only_at_privateSlot (data : SharedPrivateData crux)
    {atomIndex : Fin 6}
    (hdeadAt : data.tightDir (data.basisLabel data.privateSlot) atomIndex = 0)
    (hlive : ∀ slot : Fin data.basisCount, slot ≠ data.privateSlot →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    {slotLive : Fin data.basisCount} (hne : slotLive ≠ data.privateSlot) : False := by
  classical
  have hcoeff := data.coeffDiag_eq_one_sub_of_dead_single hdeadAt hlive hne
  have hpinNe : atomIndex ≠ data.pinAtom := by
    intro heq
    rw [heq] at hdeadAt
    exact data.hpinNe hdeadAt
  have hpair := data.captureDiag_pair_le_total hpinNe
  have htotal := data.sum_captureDiag_lt_one
  rw [data.hpin] at hcoeff
  linarith

/-- **THE PAIR ROOT LAW.**  An atom whose dead set is a pair of slots
makes one minus its captured diagonal a root of the characteristic
polynomial of the two-by-two coefficient corner on that pair. -/
theorem charRoot_of_dead_pair (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomIndex : Fin 6}
    (hdeadOne : data.tightDir (data.basisLabel slotOne) atomIndex = 0)
    (hdeadTwo : data.tightDir (data.basisLabel slotTwo) atomIndex = 0)
    (hlive : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    {slotFree : Fin data.basisCount} (hfreeOne : slotFree ≠ slotOne)
    (hfreeTwo : slotFree ≠ slotTwo) :
    (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex))
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex))
      - (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)
        * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex))
      + (data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
        - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne) = 0 := by
  classical
  have hdead : ∀ slot ∈ ({slotOne, slotTwo} : Finset (Fin data.basisCount)),
      data.tightDir (data.basisLabel slot) atomIndex = 0 := by
    intro slot hslot
    simp only [Finset.mem_insert, Finset.mem_singleton] at hslot
    rcases hslot with rfl | rfl
    · exact hdeadOne
    · exact hdeadTwo
  have hrow : ∀ slot ∉ ({slotOne, slotTwo} : Finset (Fin data.basisCount)),
      data.rowShadow atomIndex slot
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)
          * data.tightDir (data.basisLabel slot) atomIndex := by
    intro slot hslot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hslot
    exact data.rowShadow_eq_captureDiag (hlive slot hslot.1 hslot.2)
  have hfreeOut : slotFree ∉ ({slotOne, slotTwo} : Finset (Fin data.basisCount)) := by
    simp [hfreeOne, hfreeTwo]
  have hsome : data.rowShadow atomIndex slotOne ≠ 0
      ∨ data.rowShadow atomIndex slotTwo ≠ 0 := by
    by_contra hnone
    push Not at hnone
    refine data.false_of_rowShadow_deadSet_eq_zero hdead hrow ?_ hfreeOut
      (data.basis_live_of_mem_support (hlive slotFree hfreeOne hfreeTwo))
    intro dead hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hnone.1
    · exact hnone.2
  have htransOne := data.rowShadow_transfer hdead hrow slotOne
  have htransTwo := data.rowShadow_transfer hdead hrow slotTwo
  rw [Finset.sum_pair hne] at htransOne htransTwo
  have heqOne : data.rowShadow atomIndex slotOne
        * (data.coeff slotOne slotOne
          - (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex)))
      + data.rowShadow atomIndex slotTwo * data.coeff slotTwo slotOne = 0 := by
    linear_combination -htransOne
  have heqTwo : data.rowShadow atomIndex slotOne * data.coeff slotOne slotTwo
      + data.rowShadow atomIndex slotTwo
        * (data.coeff slotTwo slotTwo
          - (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))) = 0 := by
    linear_combination -htransTwo
  rcases hsome with hfirst | hsecond
  · have hdet : ((1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
          * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
        - (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)
          * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
        + (data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
          - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne))
        * data.rowShadow atomIndex slotOne = 0 := by
      linear_combination (data.coeff slotTwo slotTwo
          - (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))) * heqOne
        - data.coeff slotTwo slotOne * heqTwo
    exact (mul_eq_zero.mp hdet).resolve_right hfirst
  · have hdet : ((1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
          * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
        - (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)
          * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))
        + (data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
          - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne))
        * data.rowShadow atomIndex slotTwo = 0 := by
      linear_combination (data.coeff slotOne slotOne
          - (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex))) * heqTwo
        - data.coeff slotOne slotTwo * heqOne
    exact (mul_eq_zero.mp hdet).resolve_right hsecond

/-- **THE PURE PAIR REFUSES ITS COMPLEMENT.**  Two pure atoms pin the
corner's characteristic polynomial to `(t - dY) (t - dZ)`.  An atom live
exactly outside the pair makes `1 - d` a root, thus two captured
diagonals total one. -/
theorem false_of_purePairComplement_atom (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6}
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0)
    {atomQ : Fin 6} (hQY : atomQ ≠ atomY) (hQZ : atomQ ≠ atomZ)
    (hdeadOne : data.tightDir (data.basisLabel slotOne) atomQ = 0)
    (hdeadTwo : data.tightDir (data.basisLabel slotTwo) atomQ = 0)
    (hlive : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    {slotFree : Fin data.basisCount} (hfreeOne : slotFree ≠ slotOne)
    (hfreeTwo : slotFree ≠ slotTwo) : False := by
  have htrace := data.purePair_corner_trace hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  have hdet := data.purePair_corner_det hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  have hchar := data.charRoot_of_dead_pair hne hdeadOne hdeadTwo hlive hfreeOne hfreeTwo
  rw [htrace, hdet] at hchar
  have hfactor : (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ)
        - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomY))
      * (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ)
        - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomZ)) = 0 := by
    linear_combination hchar
  have hpairY := data.captureDiag_pair_le_total hQY
  have hpairZ := data.captureDiag_pair_le_total hQZ
  have htotal := data.sum_captureDiag_lt_one
  rcases mul_eq_zero.mp hfactor with hzeroY | hzeroZ
  · linarith
  · linarith

/-! ## Layer 3 — one pure atom reads the corner -/

/-- **THE PURE ATOM IS A CORNER ROOT.**  An atom that lives only on a
named pair of basis slots makes its captured diagonal a root of the
characteristic polynomial of the two-by-two coefficient corner.  This is
the mirror of the pair root law: the live set is the pair instead of the
dead set. -/
theorem purePairAtom_charRoot (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomW : Fin 6}
    (hblockOne : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockTwo : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomW = 0) :
    (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
        * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
      - (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)
        * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
      + (data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
        - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne) = 0 := by
  have hone := data.pairRow_capture hne hblockOne hpure
  have htwo := data.pairRow_capture hne hblockTwo hpure
  have hliveOne := data.basis_live_of_mem_support hblockOne
  have hdet : ((chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
        * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
      - (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)
        * (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
      + (data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
        - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne))
      * data.tightDir (data.basisLabel slotOne) atomW = 0 := by
    linear_combination (data.coeff slotTwo slotTwo
        - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)) * hone
      - data.coeff slotTwo slotOne * htwo
  exact (mul_eq_zero.mp hdet).resolve_right hliveOne

/-- **THE CORNER FROM ONE PURE ATOM AND ONE OUTER ATOM.**  A pure atom of
the pair contributes the root `dW`, and an atom live exactly outside the
pair contributes the root `1 - dQ`.  The two are distinct because two
captured diagonals total less than one, thus they ARE the two roots and
they read the corner's trace and determinant.  Two pure atoms are no
longer necessary. -/
theorem purePairAtom_corner_of_outerFull (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomW atomQ : Fin 6} (hWQ : atomW ≠ atomQ)
    (hblockOne : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockTwo : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomW = 0)
    (hdeadOne : data.tightDir (data.basisLabel slotOne) atomQ = 0)
    (hdeadTwo : data.tightDir (data.basisLabel slotTwo) atomQ = 0)
    (hlive : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    {slotFree : Fin data.basisCount} (hfreeOne : slotFree ≠ slotOne)
    (hfreeTwo : slotFree ≠ slotTwo) :
    data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomW)
          + (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomQ))
      ∧ data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
          - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne
        = (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomW)
          * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomQ)) := by
  have hrootW := data.purePairAtom_charRoot hne hblockOne hblockTwo hpure
  have hrootQ := data.charRoot_of_dead_pair hne hdeadOne hdeadTwo hlive hfreeOne hfreeTwo
  have hpair := data.captureDiag_pair_le_total hWQ
  have htotal := data.sum_captureDiag_lt_one
  have hsep : (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomW)
      - (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomQ)) ≠ 0 := by
    intro hzero
    linarith
  have hdiff : ((chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
        - (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ)))
      * ((chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomW)
          + (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomQ))
        - (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)) = 0 := by
    linear_combination hrootW - hrootQ
  have htrace : data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomW)
        + (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ)) := by
    have := (mul_eq_zero.mp hdiff).resolve_left hsep
    linarith
  refine ⟨htrace, ?_⟩
  linear_combination hrootW + (chartObjective (chartPointOfDesign crux.design)
    + (chartPointOfDesign crux.design).weight atomW) * htrace

/-- **TWO OUTER ATOMS AGAINST A PURE ATOM SHARE A CAPTURED DIAGONAL.**
The corner's trace reads the same way against each of them, thus the two
captured diagonals agree. -/
theorem captureDiag_eq_of_purePairAtom_of_two_outerFull
    (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomW atomP atomQ : Fin 6} (hWP : atomW ≠ atomP) (hWQ : atomW ≠ atomQ)
    (hblockOne : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockTwo : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomW = 0)
    (hdeadPone : data.tightDir (data.basisLabel slotOne) atomP = 0)
    (hdeadPtwo : data.tightDir (data.basisLabel slotTwo) atomP = 0)
    (hlivePfull : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomP ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    (hdeadQone : data.tightDir (data.basisLabel slotOne) atomQ = 0)
    (hdeadQtwo : data.tightDir (data.basisLabel slotTwo) atomQ = 0)
    (hliveQfull : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    {slotFree : Fin data.basisCount} (hfreeOne : slotFree ≠ slotOne)
    (hfreeTwo : slotFree ≠ slotTwo) :
    (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomP)
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomQ := by
  have hP := (data.purePairAtom_corner_of_outerFull hne hWP hblockOne hblockTwo hpure
    hdeadPone hdeadPtwo hlivePfull hfreeOne hfreeTwo).1
  have hQ := (data.purePairAtom_corner_of_outerFull hne hWQ hblockOne hblockTwo hpure
    hdeadQone hdeadQtwo hliveQfull hfreeOne hfreeTwo).1
  rw [hP] at hQ
  linarith

/-- **THE CORNER FROM TWO OUTER ATOMS.**  Two atoms live exactly outside
the pair, with different captured diagonals, read the corner's trace and
determinant with NO pure atom at all.  This is the law of the surviving
identical shape at basis count six. -/
theorem corner_of_two_outerFull (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomP atomQ : Fin 6}
    (hcapture : (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomP)
      ≠ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomQ)
    (hdeadPone : data.tightDir (data.basisLabel slotOne) atomP = 0)
    (hdeadPtwo : data.tightDir (data.basisLabel slotTwo) atomP = 0)
    (hlivePfull : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomP ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    (hdeadQone : data.tightDir (data.basisLabel slotOne) atomQ = 0)
    (hdeadQtwo : data.tightDir (data.basisLabel slotTwo) atomQ = 0)
    (hliveQfull : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    {slotFree : Fin data.basisCount} (hfreeOne : slotFree ≠ slotOne)
    (hfreeTwo : slotFree ≠ slotTwo) :
    data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
        = (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomP))
          + (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomQ))
      ∧ data.coeff slotOne slotOne * data.coeff slotTwo slotTwo
          - data.coeff slotOne slotTwo * data.coeff slotTwo slotOne
        = (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomP))
          * (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomQ)) := by
  have hrootP := data.charRoot_of_dead_pair hne hdeadPone hdeadPtwo hlivePfull
    hfreeOne hfreeTwo
  have hrootQ := data.charRoot_of_dead_pair hne hdeadQone hdeadQtwo hliveQfull
    hfreeOne hfreeTwo
  have hsep : (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomP))
      - (1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomQ)) ≠ 0 := by
    intro hzero
    exact hcapture (by linarith)
  have hdiff : ((1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomP))
        - (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ)))
      * ((1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomP))
          + (1 - (chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomQ))
        - (data.coeff slotOne slotOne + data.coeff slotTwo slotTwo)) = 0 := by
    linear_combination hrootP - hrootQ
  have htrace : data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
      = (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomP))
        + (1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ)) := by
    have := (mul_eq_zero.mp hdiff).resolve_left hsep
    linarith
  refine ⟨htrace, ?_⟩
  linear_combination hrootP + (1 - (chartObjective (chartPointOfDesign crux.design)
    + (chartPointOfDesign crux.design).weight atomP)) * htrace

/-- **THE SINGLE DEAD PAIR AGAINST A PURE ATOM AND AN OUTER ATOM.**  Two
atoms dead at one slot of the pair each read the two corner diagonals as
`1 - d`, thus the trace is `2 - dR1 - dR2`.  A pure atom and an outer
atom read the same trace as `dW + 1 - dQ`.  The two readings put three
captured diagonals above one. -/
theorem false_of_purePairAtom_of_outerFull_of_singleDead_pair
    (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomW atomQ atomR atomT : Fin 6} (hWQ : atomW ≠ atomQ)
    (hWR : atomW ≠ atomR) (hWT : atomW ≠ atomT) (hRT : atomR ≠ atomT)
    (hblockOne : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockTwo : atomW ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomW = 0)
    (hdeadQone : data.tightDir (data.basisLabel slotOne) atomQ = 0)
    (hdeadQtwo : data.tightDir (data.basisLabel slotTwo) atomQ = 0)
    (hliveQfull : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot))
    (hdiagOne : data.coeff slotOne slotOne
      = 1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomR))
    (hdiagTwo : data.coeff slotTwo slotTwo
      = 1 - (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomT))
    {slotFree : Fin data.basisCount} (hfreeOne : slotFree ≠ slotOne)
    (hfreeTwo : slotFree ≠ slotTwo) : False := by
  have htrace := (data.purePairAtom_corner_of_outerFull hne hWQ hblockOne hblockTwo
    hpure hdeadQone hdeadQtwo hliveQfull hfreeOne hfreeTwo).1
  rw [hdiagOne, hdiagTwo] at htrace
  have htriple := data.captureDiag_triple_le_total hWR hWT hRT
  have htotal := data.sum_captureDiag_lt_one
  have hQnonneg := data.captureDiag_nonneg atomQ
  linarith

/-! ## Layer 4 — the census of a pure pair -/

/-- The multiplicity of an atom among the basis slots outside a named
pair. -/
noncomputable def outerMultiplicity (data : SharedPrivateData crux)
    (slotOne slotTwo : Fin data.basisCount) (atomIndex : Fin 6) : ℕ :=
  ((Finset.univ \ ({slotOne, slotTwo} : Finset (Fin data.basisCount))).filter
    fun slot => atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)).card

/-- **THE OUTER CENSUS.**  The outer multiplicities total three times the
number of outer slots, because every basis support holds three atoms. -/
theorem sum_outerMultiplicity (data : SharedPrivateData crux)
    (slotOne slotTwo : Fin data.basisCount) :
    ∑ atomIndex : Fin 6, data.outerMultiplicity slotOne slotTwo atomIndex
      = 3 * (Finset.univ \ ({slotOne, slotTwo}
        : Finset (Fin data.basisCount))).card := by
  classical
  have hinner : ∀ slot ∈ (Finset.univ \ ({slotOne, slotTwo}
      : Finset (Fin data.basisCount))),
      (∑ atomIndex : Fin 6, if atomIndex
        ∈ datumTightSupport data.tightDir (data.basisLabel slot) then 1 else 0) = 3 := by
    intro slot _
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact data.hthree slot
  simp only [outerMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul,
    mul_comm]

/-- A pure atom of the pair has outer multiplicity zero. -/
theorem outerMultiplicity_eq_zero_of_pure (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} {atomIndex : Fin 6}
    (hpure : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomIndex = 0) :
    data.outerMultiplicity slotOne slotTwo atomIndex = 0 := by
  classical
  rw [outerMultiplicity, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro slot hslot
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hslot
  exact fun hmem =>
    data.basis_live_of_mem_support hmem (hpure slot hslot.2.1 hslot.2.2)

/-- The outer multiplicity never exceeds the number of outer slots. -/
theorem outerMultiplicity_le (data : SharedPrivateData crux)
    (slotOne slotTwo : Fin data.basisCount) (atomIndex : Fin 6) :
    data.outerMultiplicity slotOne slotTwo atomIndex
      ≤ (Finset.univ \ ({slotOne, slotTwo}
        : Finset (Fin data.basisCount))).card :=
  Finset.card_filter_le _ _

/-- The pin atom has outer multiplicity at most one. -/
theorem outerMultiplicity_pinAtom_le_one (data : SharedPrivateData crux)
    (slotOne slotTwo : Fin data.basisCount) :
    data.outerMultiplicity slotOne slotTwo data.pinAtom ≤ 1 := by
  classical
  have hsub : ((Finset.univ \ ({slotOne, slotTwo} : Finset (Fin data.basisCount))).filter
      fun slot => data.pinAtom
        ∈ datumTightSupport data.tightDir (data.basisLabel slot))
      ⊆ Finset.univ.filter fun slot => data.pinAtom
        ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro slot hslot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hslot).2⟩
  have hcard := Finset.card_le_card hsub
  have hone := data.hmultOne
  simp only [basisSupportMultiplicity] at hone
  rw [outerMultiplicity]
  omega

/-- An atom of full outer multiplicity is live at every outer slot. -/
theorem live_outer_of_outerMultiplicity_full (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} {atomIndex : Fin 6}
    (hfull : data.outerMultiplicity slotOne slotTwo atomIndex
      = (Finset.univ \ ({slotOne, slotTwo} : Finset (Fin data.basisCount))).card)
    {slot : Fin data.basisCount} (hone : slot ≠ slotOne) (htwo : slot ≠ slotTwo) :
    atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
  classical
  have heq : (Finset.univ \ ({slotOne, slotTwo} : Finset (Fin data.basisCount))).filter
      (fun other => atomIndex
        ∈ datumTightSupport data.tightDir (data.basisLabel other))
      = Finset.univ \ ({slotOne, slotTwo} : Finset (Fin data.basisCount)) :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (le_of_eq hfull.symm)
  have hmem : slot ∈ Finset.univ \ ({slotOne, slotTwo}
      : Finset (Fin data.basisCount)) := by
    simp [hone, htwo]
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- **THE CENSUS OF A PURE PAIR.**  Two pure atoms empty the outer
supports of themselves, thus the outer supports draw three atoms each
from the four remaining atoms.  The pin atom takes at most one outer
incidence, thus two of the other three atoms are live at every outer
slot. -/
theorem exists_two_outerFull_atoms (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6} (hYZ : atomY ≠ atomZ)
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0) :
    ∃ atomP atomQ : Fin 6, atomP ≠ atomQ
      ∧ atomP ≠ atomY ∧ atomP ≠ atomZ ∧ atomQ ≠ atomY ∧ atomQ ≠ atomZ
      ∧ (∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
          atomP ∈ datumTightSupport data.tightDir (data.basisLabel slot))
      ∧ (∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
          atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot)) := by
  classical
  -- the pin atom is neither pure atom, because a pure atom carries two slots
  have hmultTwo : ∀ atomIndex : Fin 6,
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) →
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) →
      atomIndex ≠ data.pinAtom := by
    intro atomIndex hone htwo heq
    have hpairSub : ({slotOne, slotTwo} : Finset (Fin data.basisCount))
        ⊆ Finset.univ.filter fun slot => data.pinAtom
          ∈ datumTightSupport data.tightDir (data.basisLabel slot) := by
      intro slot hslot
      simp only [Finset.mem_insert, Finset.mem_singleton] at hslot
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hslot with rfl | rfl
      · rw [← heq]; exact hone
      · rw [← heq]; exact htwo
    have hcard := Finset.card_le_card hpairSub
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton] at hcard
    have hone' := data.hmultOne
    simp only [basisSupportMultiplicity] at hone'
    omega
  have hpinY : atomY ≠ data.pinAtom := hmultTwo atomY hblockYone hblockYtwo
  have hpinZ : atomZ ≠ data.pinAtom := hmultTwo atomZ hblockZone hblockZtwo
  -- the three remaining atoms
  set outer : Finset (Fin data.basisCount) :=
    Finset.univ \ ({slotOne, slotTwo} : Finset (Fin data.basisCount)) with houter
  set rest : Finset (Fin 6) :=
    Finset.univ \ ({atomY, atomZ, data.pinAtom} : Finset (Fin 6)) with hrest
  have hcardRest : rest.card = 3 := by
    rw [hrest, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hYZ, hpinY]),
      Finset.card_insert_of_notMem (by simp [hpinZ]), Finset.card_singleton]
  obtain ⟨atomA, atomB, atomC, hAB, hAC, hBC, hrestEq⟩ :=
    Finset.card_eq_three.mp hcardRest
  have hsplit : ∑ atomIndex ∈ rest, data.outerMultiplicity slotOne slotTwo atomIndex
      + ∑ atomIndex ∈ ({atomY, atomZ, data.pinAtom} : Finset (Fin 6)),
          data.outerMultiplicity slotOne slotTwo atomIndex
      = ∑ atomIndex : Fin 6, data.outerMultiplicity slotOne slotTwo atomIndex :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have hnamed : ∑ atomIndex ∈ ({atomY, atomZ, data.pinAtom} : Finset (Fin 6)),
      data.outerMultiplicity slotOne slotTwo atomIndex
      = data.outerMultiplicity slotOne slotTwo data.pinAtom := by
    rw [Finset.sum_insert (by simp [hYZ, hpinY]), Finset.sum_insert (by simp [hpinZ]),
      Finset.sum_singleton, data.outerMultiplicity_eq_zero_of_pure hpureY,
      data.outerMultiplicity_eq_zero_of_pure hpureZ, zero_add, zero_add]
  have hrestSum : ∑ atomIndex ∈ rest,
      data.outerMultiplicity slotOne slotTwo atomIndex
      = data.outerMultiplicity slotOne slotTwo atomA
        + data.outerMultiplicity slotOne slotTwo atomB
        + data.outerMultiplicity slotOne slotTwo atomC := by
    rw [hrestEq, Finset.sum_insert (by simp [hAB, hAC]),
      Finset.sum_insert (by simp [hBC]), Finset.sum_singleton, add_assoc]
  have htotal := data.sum_outerMultiplicity slotOne slotTwo
  rw [hnamed, hrestSum, htotal] at hsplit
  have hpinLe := data.outerMultiplicity_pinAtom_le_one slotOne slotTwo
  have hAle := data.outerMultiplicity_le slotOne slotTwo atomA
  have hBle := data.outerMultiplicity_le slotOne slotTwo atomB
  have hCle := data.outerMultiplicity_le slotOne slotTwo atomC
  rw [← houter] at hsplit hAle hBle hCle
  have hpick : (data.outerMultiplicity slotOne slotTwo atomA = outer.card
        ∧ data.outerMultiplicity slotOne slotTwo atomB = outer.card)
      ∨ (data.outerMultiplicity slotOne slotTwo atomA = outer.card
        ∧ data.outerMultiplicity slotOne slotTwo atomC = outer.card)
      ∨ (data.outerMultiplicity slotOne slotTwo atomB = outer.card
        ∧ data.outerMultiplicity slotOne slotTwo atomC = outer.card) := by
    omega
  have hmemRest : ∀ atomIndex : Fin 6, atomIndex ∈ rest →
      atomIndex ≠ atomY ∧ atomIndex ≠ atomZ := by
    intro atomIndex hmem
    rw [hrest, Finset.mem_sdiff] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    exact ⟨hmem.2.1, hmem.2.2.1⟩
  have hAmem : atomA ∈ rest := by rw [hrestEq]; simp
  have hBmem : atomB ∈ rest := by rw [hrestEq]; simp
  have hCmem : atomC ∈ rest := by rw [hrestEq]; simp
  obtain ⟨hAY, hAZ⟩ := hmemRest atomA hAmem
  obtain ⟨hBY, hBZ⟩ := hmemRest atomB hBmem
  obtain ⟨hCY, hCZ⟩ := hmemRest atomC hCmem
  rcases hpick with ⟨hfullA, hfullB⟩ | ⟨hfullA, hfullC⟩ | ⟨hfullB, hfullC⟩
  · exact ⟨atomA, atomB, hAB, hAY, hAZ, hBY, hBZ,
      fun slot hone htwo => data.live_outer_of_outerMultiplicity_full
        (by rw [hfullA, houter]) hone htwo,
      fun slot hone htwo => data.live_outer_of_outerMultiplicity_full
        (by rw [hfullB, houter]) hone htwo⟩
  · exact ⟨atomA, atomC, hAC, hAY, hAZ, hCY, hCZ,
      fun slot hone htwo => data.live_outer_of_outerMultiplicity_full
        (by rw [hfullA, houter]) hone htwo,
      fun slot hone htwo => data.live_outer_of_outerMultiplicity_full
        (by rw [hfullC, houter]) hone htwo⟩
  · exact ⟨atomB, atomC, hBC, hBY, hBZ, hCY, hCZ,
      fun slot hone htwo => data.live_outer_of_outerMultiplicity_full
        (by rw [hfullB, houter]) hone htwo,
      fun slot hone htwo => data.live_outer_of_outerMultiplicity_full
        (by rw [hfullC, houter]) hone htwo⟩

/-! ## Layer 5 — the pure pair kill at every basis count -/

/-- The three readings of an atom that is live at every outer slot: it is
saturated, it sits on the pair complement, or it reads one diagonal of
the corner. -/
theorem outerFull_dichotomy (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6}
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0)
    {atomQ : Fin 6} (hQY : atomQ ≠ atomY) (hQZ : atomQ ≠ atomZ)
    (hfull : ∀ slot : Fin data.basisCount, slot ≠ slotOne → slot ≠ slotTwo →
      atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot)) :
    (atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
      ∧ data.coeff slotTwo slotTwo
        = 1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ))
    ∨ (atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)
      ∧ data.coeff slotOne slotOne
        = 1 - (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomQ)) := by
  classical
  by_cases hone : atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne)
  · by_cases htwo : atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)
    · -- a saturated atom
      refine absurd (data.false_of_saturated_atom (atomIndex := atomQ) ?_) not_false
      intro slot
      by_cases hslotOne : slot = slotOne
      · rw [hslotOne]; exact hone
      by_cases hslotTwo : slot = slotTwo
      · rw [hslotTwo]; exact htwo
      exact hfull slot hslotOne hslotTwo
    · refine Or.inl ⟨hone, ?_⟩
      refine data.coeffDiag_eq_one_sub_of_dead_single
        (data.basis_dead_of_notMem_support htwo) ?_ (slotLive := slotOne) hne
      intro slot hslot
      by_cases hslotOne : slot = slotOne
      · rw [hslotOne]; exact hone
      exact hfull slot hslotOne hslot
  · by_cases htwo : atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo)
    · refine Or.inr ⟨htwo, ?_⟩
      refine data.coeffDiag_eq_one_sub_of_dead_single
        (data.basis_dead_of_notMem_support hone) ?_ (slotLive := slotTwo) (Ne.symm hne)
      intro slot hslot
      by_cases hslotTwo : slot = slotTwo
      · rw [hslotTwo]; exact htwo
      exact hfull slot hslot hslotTwo
    · -- the atom sits on the pair complement
      have hmult := basisSupportMultiplicity_pos_of_Hform data.hdata data.basisLabel
        data.gram data.hHform atomQ
      simp only [basisSupportMultiplicity] at hmult
      rw [Finset.card_pos] at hmult
      obtain ⟨slotFree, hslotFree⟩ := hmult
      have hlive := (Finset.mem_filter.mp hslotFree).2
      have hfreeOne : slotFree ≠ slotOne := by
        intro heq; rw [heq] at hlive; exact hone hlive
      have hfreeTwo : slotFree ≠ slotTwo := by
        intro heq; rw [heq] at hlive; exact htwo hlive
      exact absurd (data.false_of_purePairComplement_atom hne hblockYone hblockYtwo
        hblockZone hblockZtwo hpureY hpureZ hwedge hQY hQZ
        (data.basis_dead_of_notMem_support hone)
        (data.basis_dead_of_notMem_support htwo) hfull hfreeOne hfreeTwo) not_false

/-- **TWO SHARED PURE ATOMS KILL EVERY BASIS COUNT.**  Two atoms that
live only on a named pair of basis slots, with independent value pairs,
refuse the datum.  The census gives two atoms live at every outer slot,
and the dichotomy leaves only the shape where the two read the two
diagonals of the corner.  Those two atoms then sit in the two supports
outside the pure pair, one each, and the corner trace reads four
captured diagonals as two. -/
theorem false_of_pureSharedPair (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomY atomZ : Fin 6} (hYZ : atomY ≠ atomZ)
    (hblockYone : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockYtwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hblockZone : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hblockZtwo : atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo))
    (hpureY : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomY = 0)
    (hpureZ : ∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
      data.tightDir (data.basisLabel other) atomZ = 0)
    (hwedge : data.tightDir (data.basisLabel slotOne) atomY
        * data.tightDir (data.basisLabel slotTwo) atomZ
      - data.tightDir (data.basisLabel slotOne) atomZ
        * data.tightDir (data.basisLabel slotTwo) atomY ≠ 0) : False := by
  classical
  obtain ⟨atomP, atomQ, hPQ, hPY, hPZ, hQY, hQZ, hPfull, hQfull⟩ :=
    data.exists_two_outerFull_atoms hne hYZ hblockYone hblockYtwo hblockZone
      hblockZtwo hpureY hpureZ
  have hdichP := data.outerFull_dichotomy hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge hPY hPZ hPfull
  have hdichQ := data.outerFull_dichotomy hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge hQY hQZ hQfull
  have htrace := data.purePair_corner_trace hne hblockYone hblockYtwo hblockZone
    hblockZtwo hpureY hpureZ hwedge
  -- a support of three atoms holds one atom outside the pure pair
  have hsingle : ∀ slot : Fin data.basisCount,
      atomY ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      atomZ ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      atomP ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
      atomQ ∈ datumTightSupport data.tightDir (data.basisLabel slot) → False := by
    intro slot hY hZ hP hQ
    have hsub : ({atomY, atomZ, atomP, atomQ} : Finset (Fin 6))
        ⊆ datumTightSupport data.tightDir (data.basisLabel slot) := by
      intro atomIndex hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact hY
      · exact hZ
      · exact hP
      · exact hQ
    have hcard := Finset.card_le_card hsub
    rw [data.hthree slot, Finset.card_insert_of_notMem (by simp [hYZ, Ne.symm hPY,
        Ne.symm hQY]), Finset.card_insert_of_notMem (by simp [Ne.symm hPZ,
        Ne.symm hQZ]), Finset.card_insert_of_notMem (by simp [hPQ]),
      Finset.card_singleton] at hcard
    omega
  -- the four captured diagonals of a quadruple total less than one
  have hquad := data.captureDiag_quad_le_total hYZ (Ne.symm hPY) (Ne.symm hQY)
    (Ne.symm hPZ) (Ne.symm hQZ) hPQ
  have htotal := data.sum_captureDiag_lt_one
  rcases hdichP with ⟨hPone, hPcoeff⟩ | ⟨hPtwo, hPcoeff⟩
  · rcases hdichQ with ⟨hQone, hQcoeff⟩ | ⟨hQtwo, hQcoeff⟩
    · exact hsingle slotOne hblockYone hblockZone hPone hQone
    · rw [hPcoeff, hQcoeff] at htrace
      linarith
  · rcases hdichQ with ⟨hQone, hQcoeff⟩ | ⟨hQtwo, hQcoeff⟩
    · rw [hPcoeff, hQcoeff] at htrace
      linarith
    · exact hsingle slotTwo hblockYtwo hblockZtwo hPtwo hQtwo

end SharedPrivateData

/-! ## Layer 6 — the two circuit residues with the pure branch paid -/

/-- **THE IMPURE IDENTICAL RESIDUE.**  The counted identical residue with
the five-slot payment replaced by the stronger fact that two pure atoms
of the shared triple are impossible. -/
def SharedPrivateCircuitPairIdenticalImpureClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomU atomV atomS : Fin 6, atomU ≠ atomV → atomU ≠ atomS → atomV ≠ atomS →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomU, atomV, atomS} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomU, atomV, atomS} →
        GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS →
        data.pinAtom ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) →
        shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomU
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomV
          + shiftedGapDiag (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomS ≤ 1 →
        1 - 6 * chartObjective (chartPointOfDesign crux.design)
          ≤ ∑ atomIndex ∈ Finset.univ \ ({atomU, atomV, atomS} : Finset (Fin 6)),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex →
        (∀ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
          shiftedGapDiag (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              (chartObjective (chartPointOfDesign crux.design)) atomY
              * ((∑ atomIndex ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
                    shiftedGapDiag (chartPointOfDesign crux.design).chart
                      (chartPointOfDesign crux.design).weight
                      (chartObjective (chartPointOfDesign crux.design)) atomIndex)
                + 2 * (chartObjective (chartPointOfDesign crux.design)
                  + (chartPointOfDesign crux.design).weight atomY) - 1)
            ≤ (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY)
              * (1 - (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY))) →
        (∀ atomP atomQ atomR : Fin 6, atomP ≠ atomQ → atomP ≠ atomR → atomQ ≠ atomR →
          ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
              = Finset.univ →
          ¬ GapBlockRankOne (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (chartObjective (chartPointOfDesign crux.design)) atomP atomQ atomR) →
        (∀ slot : Fin data.basisCount,
          ∑ atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot),
              shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomIndex ≤ 2) →
        (data.privateSlot ≠ slotOne ∧ data.privateSlot ≠ slotTwo
          ∧ datumTightSupport data.tightDir (data.basisLabel data.privateSlot)
            ≠ ({atomU, atomV, atomS} : Finset (Fin 6))) →
        (∀ slotThree slotFour : Fin data.basisCount,
          ∀ atomP atomQ atomR : Fin 6, atomP ≠ atomQ → atomP ≠ atomR → atomQ ≠ atomR →
            ({atomU, atomV, atomS} : Finset (Fin 6)) ∪ {atomP, atomQ, atomR}
                = Finset.univ →
            slotThree ≠ slotFour →
            datumTightSupport data.tightDir (data.basisLabel slotThree)
              = {atomP, atomQ, atomR} →
            datumTightSupport data.tightDir (data.basisLabel slotFour)
              = {atomP, atomQ, atomR} →
            False) →
        (∀ slotThree : Fin data.basisCount, ∀ atomY atomZ atomW : Fin 6,
          atomY ≠ atomZ → atomY ≠ atomW → atomZ ≠ atomW →
            atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
            atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
            datumTightSupport data.tightDir (data.basisLabel slotThree)
              = {atomY, atomZ, atomW} →
            shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomY
              + shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomZ
              + shiftedGapDiag (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (chartObjective (chartPointOfDesign crux.design)) atomW ≤ 1) →
        (2 : ℝ) ≤ Matrix.trace data.coeff →
        (∑ atomIndex : Fin 6, (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex)) < 1 →
        (∀ slot : Fin data.basisCount, ∀ atomIndex : Fin 6,
          atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
          (∀ other : Fin data.basisCount, other ≠ slot →
            data.tightDir (data.basisLabel other) atomIndex = 0) →
          data.coeff slot slot = chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex) →
        (∀ atomY atomZ : Fin 6, atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
          atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) → atomY ≠ atomZ →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomY = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomZ = 0) →
          data.coeff slotOne slotOne + data.coeff slotTwo slotTwo
            = (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomY)
              + (chartObjective (chartPointOfDesign crux.design)
                + (chartPointOfDesign crux.design).weight atomZ)) →
        (∃ slotThree : Fin data.basisCount, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
          ∧ ∃ atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)),
            atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotThree)) →
        (∀ atomY atomZ : Fin 6, atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
          atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) → atomY ≠ atomZ →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomY = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomZ = 0) →
          (∃ slotThree : Fin data.basisCount, slotThree ≠ slotOne ∧ slotThree ≠ slotTwo
            ∧ slotThree ≠ data.privateSlot
            ∧ ∀ atomIndex : Fin 6,
                atomIndex
                  ∈ datumTightSupport data.tightDir (data.basisLabel slotThree) →
                ∃ other : Fin data.basisCount, other ≠ slotThree
                  ∧ data.tightDir (data.basisLabel other) atomIndex ≠ 0)
          ∧ 1 < ∑ slot ∈ Finset.univ \ ({slotOne, slotTwo, data.privateSlot}
              : Finset (Fin data.basisCount)), data.coeff slot slot) →
        -- the shared triple keeps at most one pure atom
        (∀ atomY atomZ : Fin 6, atomY ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) →
          atomZ ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) → atomY ≠ atomZ →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomY = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomZ = 0) →
          False) →
        False

/-- **THE IMPURE LIVE-WEDGE RESIDUE.**  The counted live-wedge residue
with the five-slot payment replaced by the stronger fact that two shared
pure atoms are impossible. -/
def SharedPrivateCircuitSplitWedgeImpureClosed : Prop :=
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
        -- the two shared atoms are not both pure
        ((∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomA = 0) →
          (∀ other : Fin data.basisCount, other ≠ slotOne → other ≠ slotTwo →
            data.tightDir (data.basisLabel other) atomB = 0) →
          False) →
        False

/-- **THE IDENTICAL PURE PAYMENT.**  Two pure atoms of an identical
shared triple are impossible, thus the impure residue closes the counted
one. -/
theorem sharedPrivateCircuitPairIdenticalCountClosed_of_impure
    (hpaid : SharedPrivateCircuitPairIdenticalImpureClosed) :
    SharedPrivateCircuitPairIdenticalCountClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin hbudget
    hcomplement hleak hnotRankOne hsingular hthird hnoPair hstraddle htraceLow
    hcapture hdiag hcorner himpure hfourth _hpay
  refine hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo
    hpair atomU atomV atomS hUV hUS hVS hsupportOne hsupportTwo hshape hpin
    hbudget hcomplement hleak hnotRankOne hsingular hthird hnoPair hstraddle
    htraceLow hcapture hdiag hcorner himpure hfourth ?_
  intro atomY atomZ hY hZ hYZ hpureY hpureZ
  obtain ⟨atomW, hYW, hZW, hsetEq⟩ := exists_triple_reorder hUV hUS hVS hY hZ hYZ
  rw [hsetEq] at hsupportOne hsupportTwo
  exact data.false_of_pureSharedPair hne hYZ
    (by rw [hsupportOne]; simp) (by rw [hsupportTwo]; simp)
    (by rw [hsupportOne]; simp) (by rw [hsupportTwo]; simp)
    hpureY hpureZ
    (data.identicalPair_wedge_ne_zero hne hYZ hYW hZW hsupportOne hsupportTwo)

/-- **THE WEDGE PURE PAYMENT.**  Two shared pure atoms with a live wedge
are impossible, thus the impure live-wedge residue closes the counted
one. -/
theorem sharedPrivateCircuitSplitWedgeCountClosed_of_impure
    (hpaid : SharedPrivateCircuitSplitWedgeImpureClosed) :
    SharedPrivateCircuitSplitWedgeCountClosed := by
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hforeignX hforeignY hwedge hbudgetOne hbudgetTwo htripleBXY htripleAXY hquad
    _hpay
  refine hpaid crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo
    hpair atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hforeignX hforeignY hwedge hbudgetOne hbudgetTwo htripleBXY htripleAXY hquad ?_
  intro hpureA hpureB
  exact data.false_of_pureSharedPair hne hAB
    (by rw [hsupportOne]; simp) (by rw [hsupportTwo]; simp)
    (by rw [hsupportOne]; simp) (by rw [hsupportTwo]; simp)
    hpureA hpureB hwedge

/-! ## Layer 7 — closure two on the impure lattice -/

/-- **THE EXTRAS ON THE IMPURE LATTICE.** -/
theorem sharedPrivateExtrasClosed_of_impureLattice
    (hidentical : SharedPrivateCircuitPairIdenticalImpureClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_doubleCountLattice
    (sharedPrivateCircuitPairIdenticalCountClosed_of_impure hidentical)
    (sharedPrivateCircuitSplitWedgeCountClosed_of_impure hwedgeLive)
    hwedgeDead hwide

/-- **CLOSURE TWO FROM THE FOUR CIRCUIT RESIDUES ON THE IMPURE
LATTICE.**  The two pair residues now carry the pure branch as a
hypothesis at every basis count. -/
theorem sharedPrivateKilled_of_impure_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalImpureClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_doubleCount_circuit
    (sharedPrivateCircuitPairIdenticalCountClosed_of_impure hidentical)
    (sharedPrivateCircuitSplitWedgeCountClosed_of_impure hwedgeLive)
    hwedgeDead hwide

/-- Closure two of the rank-four rung on the impure lattice. -/
theorem rankFourSharedPrivateClosed_of_impure_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalImpureClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_doubleCount_circuit
    (sharedPrivateCircuitPairIdenticalCountClosed_of_impure hidentical)
    (sharedPrivateCircuitSplitWedgeCountClosed_of_impure hwedgeLive)
    hwedgeDead hwide

/-- The shared-private closure of the rank-five rung on the impure
lattice. -/
theorem rankFiveSharedPrivateClosed_of_impure_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalImpureClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_doubleCount_circuit
    (sharedPrivateCircuitPairIdenticalCountClosed_of_impure hidentical)
    (sharedPrivateCircuitSplitWedgeCountClosed_of_impure hwedgeLive)
    hwedgeDead hwide

/-- The shared-private closure of the rank-six rung on the impure
lattice. -/
theorem rankSixSharedPrivateClosed_of_impure_circuit
    (hidentical : SharedPrivateCircuitPairIdenticalImpureClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_doubleCount_circuit
    (sharedPrivateCircuitPairIdenticalCountClosed_of_impure hidentical)
    (sharedPrivateCircuitSplitWedgeCountClosed_of_impure hwedgeLive)
    hwedgeDead hwide

end Gtz
