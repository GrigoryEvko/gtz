import Gtz.Wave.SharedPrivateKernelGram

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-private boundary dispatch — the four-class budget and the
rank-four rigidity

The strata dispatch left the trace-two boundary residue: a diagonal-Gram
datum with an atom of three or more carriers at the shifted-weight zero
set.  The refined budget priced only the interior atoms, thus it stopped
at the boundary.  This module prices the boundary atoms too, and the new
budget makes the boundary stratum rigid.

The boundary cap.  A symmetric idempotent is positive semidefinite, thus
each diagonal entry is nonnegative and a carrier sum caps at the trace.
The cap costs one unit against the interior cap, and it needs no window.

The four-class budget.  The double count now runs with four atom
classes: the pins read exactly, the two-carrier atoms take the corner
cap, the boundary atoms take the trace cap, and only the remaining atoms
need the interior window.  At trace two the budget reads: the number of
pins is at most the number of boundary atoms.  The pin atom is one pin,
thus one boundary atom always exists, at every basis count.

The rank-four rigidity.  The multiplicity sum is three times the basis
count.  The budget law and that sum together force the basis count above
three.  At basis count four the two bounds meet: every atom with three
or more carriers has exactly three carriers and sits at the boundary,
the pin class and the boundary class have equal cardinality, and the
carrier profile is fixed.

The private-slot family.  A family of boundary reads with one carrier
slot each that no other family member carries is independent, because
the private slot reads the coefficient directly.  The trace floor then
caps the family by the complement trace.  This kill contains the landed
disjoint-support kill, because pairwise disjoint carriers give every
slot as a private slot.

The pin-complement law.  At basis count four and trace two, two atoms
off the private block that share no block would give a three-atom
disjoint family together with the pin.  Thus the complement of the
private block is pairwise co-carrier.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.carrier_diag_le_trace` — **THE BOUNDARY CAP.**
* `Gtz.carrier_budget_with_boundary` — **THE FOUR-CLASS BUDGET.**
* `Gtz.pin_card_le_boundary_card_of_budget` — the trace-two count law.
* `Gtz.SharedPrivateData.multiplicity_pos`,
  `Gtz.SharedPrivateData.sum_multiplicity` — the census vocabulary.
* `Gtz.SharedPrivateData.pin_card_le_boundary_card` — **THE BOUNDARY
  COUNT LAW.**
* `Gtz.SharedPrivateData.exists_boundary_atom` — a boundary atom always
  exists at trace two.
* `Gtz.SharedPrivateData.four_le_basisCount_of_trace_two` — the basis
  count is at least four.
* `Gtz.SharedPrivateData.boundary_rigid_of_basisCount_four` — **THE
  RANK-FOUR RIGIDITY.**
* `Gtz.gram_kernel_free_of_independent`,
  `Gtz.independent_of_private_slot` — the independence engine.
* `Gtz.SharedPrivateData.false_of_private_slot_boundary_family` — **THE
  PRIVATE-SLOT KILL.**
* `Gtz.SharedPrivateData.cocarrier_offPrivate_of_basisCount_four` — the
  pin-complement law.
* `Gtz.SharedPrivateBoundaryFourClosed`,
  `Gtz.SharedPrivateBoundaryHighClosed` — **THE TWO NARROWED
  RESIDUES.**
* `Gtz.sharedPrivateBoundaryClosed_of_split` — the boundary dispatch.
* `Gtz.sharedPrivateKilled_of_strata_boundary`,
  `Gtz.rankFourSharedPrivateClosed_of_boundary_strata`,
  `Gtz.rankFiveSharedPrivateClosed_of_boundary_strata`,
  `Gtz.rankSixSharedPrivateClosed_of_boundary_strata` — the rung
  compositions.

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over shared-private data, and no datum exists if `Gtz.GtzWeighted 6 3`
holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the boundary cap -/

/-- **THE BOUNDARY CAP.**  A carrier sum of the diagonal of a symmetric
idempotent caps at the trace.  The matrix is positive semidefinite, thus
every diagonal entry is nonnegative. -/
theorem carrier_diag_le_trace {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (carrier : Finset (Fin n)) :
    ∑ slot ∈ carrier, S slot slot ≤ Matrix.trace S := by
  have hpsd := posSemidef_of_transpose_eq_of_idem hsymm hidem
  have hsplit : ∑ slot ∈ carrier, S slot slot
      + ∑ slot ∈ carrierᶜ, S slot slot = Matrix.trace S := by
    rw [Matrix.trace]
    exact Finset.sum_add_sum_compl carrier fun slot => S slot slot
  have hrest : 0 ≤ ∑ slot ∈ carrierᶜ, S slot slot :=
    Finset.sum_nonneg fun slot _ => hpsd.diag_nonneg
  linarith

/-! ## Layer 2 — the four-class budget -/

set_option maxHeartbeats 800000 in
/-- **THE FOUR-CLASS BUDGET.**  The double count with four atom classes:
the pins read exactly, the two-carrier atoms take the corner cap, the
boundary atoms take the trace cap, and only the remaining atoms need the
interior window. -/
theorem carrier_budget_with_boundary {n m : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (car : Fin m → Finset (Fin n))
    (v : Fin m → Fin n → ℝ) (d : Fin m → ℝ) (blockCount : ℕ)
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = blockCount)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (pinSet pairSet bndSet : Finset (Fin m))
    (hpinPair : Disjoint pinSet pairSet) (hpinBnd : Disjoint pinSet bndSet)
    (hpairBnd : Disjoint pairSet bndSet)
    (hpin : ∀ atom ∈ pinSet, ∃ pinSlot, car atom = {pinSlot})
    (hpair : ∀ atom ∈ pairSet, ∃ slotOne slotTwo,
      slotOne ≠ slotTwo ∧ car atom = {slotOne, slotTwo})
    (hbndNonneg : ∀ atom ∈ bndSet, 0 ≤ d atom)
    (hd0 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → atom ∉ bndSet →
      0 < d atom)
    (hd1 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → atom ∉ bndSet →
      d atom < 1) :
    (blockCount : ℝ) * Matrix.trace S
      ≤ ((m : ℝ) - pinSet.card - pairSet.card - bndSet.card)
          * (Matrix.trace S - 1)
        + pairSet.card + (bndSet.card : ℝ) * Matrix.trace S
        + ∑ atom, d atom := by
  classical
  -- the double count of the carrier incidences
  have hdouble : ∑ atom, (∑ slot ∈ car atom, S slot slot)
      = (blockCount : ℝ) * Matrix.trace S := by
    have hswap : ∑ atom, (∑ slot ∈ car atom, S slot slot)
        = ∑ slot, ∑ atom,
            (if slot ∈ car atom then S slot slot else 0) := by
      rw [← Finset.sum_comm]
      refine Finset.sum_congr rfl fun atom _ => ?_
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hswap]
    have hinner : ∀ slot : Fin n,
        (∑ atom, (if slot ∈ car atom then S slot slot else 0))
          = (blockCount : ℝ) * S slot slot := by
      intro slot
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hinc slot]
    rw [Finset.sum_congr rfl fun slot _ => hinner slot, ← Finset.mul_sum,
      Matrix.trace]
    rfl
  -- the special classes and their union
  set special := pinSet ∪ pairSet ∪ bndSet with hspecial
  have hunionDisj : Disjoint (pinSet ∪ pairSet) bndSet :=
    Finset.disjoint_union_left.mpr ⟨hpinBnd, hpairBnd⟩
  have hcardSpecial : special.card
      = pinSet.card + pairSet.card + bndSet.card := by
    rw [hspecial, Finset.card_union_of_disjoint hunionDisj,
      Finset.card_union_of_disjoint hpinPair]
  have hsumSplit : ∀ f : Fin m → ℝ,
      ∑ atom ∈ special, f atom = ∑ atom ∈ pinSet, f atom
        + ∑ atom ∈ pairSet, f atom + ∑ atom ∈ bndSet, f atom := by
    intro f
    rw [hspecial, Finset.sum_union hunionDisj, Finset.sum_union hpinPair]
  -- the four class bounds
  have hpineq : ∑ atom ∈ pinSet, (∑ slot ∈ car atom, S slot slot)
      = ∑ atom ∈ pinSet, d atom := by
    refine Finset.sum_congr rfl fun atom hatom => ?_
    obtain ⟨pinSlot, hps⟩ := hpin atom hatom
    rw [hps, Finset.sum_singleton]
    exact pin_diag_eq_of_read (hsupp atom) (hread atom) (hnz atom) hps
  have hpairle : ∑ atom ∈ pairSet, (∑ slot ∈ car atom, S slot slot)
      ≤ (pairSet.card : ℝ) + ∑ atom ∈ pairSet, d atom := by
    have hstep : ∑ atom ∈ pairSet, (∑ slot ∈ car atom, S slot slot)
        ≤ ∑ atom ∈ pairSet, (1 + d atom) := by
      refine Finset.sum_le_sum fun atom hatom => ?_
      obtain ⟨slotOne, slotTwo, hneq, hps⟩ := hpair atom hatom
      have hsupp' : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
          v atom slot = 0 := by
        intro slot h1 h2
        exact hsupp atom slot (by rw [hps]; simp [h1, h2])
      have hcap := two_carrier_trace_cap hsymm hidem hneq hsupp'
        (hread atom slotOne (by rw [hps]; exact Finset.mem_insert_self _ _))
        (hread atom slotTwo (by
          rw [hps]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        (hnz atom)
      rw [hps, Finset.sum_pair hneq]
      exact hcap
    have hexpand : ∑ atom ∈ pairSet, (1 + d atom)
        = (pairSet.card : ℝ) + ∑ atom ∈ pairSet, d atom := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith [hstep, hexpand.le, hexpand.ge]
  have hbndle : ∑ atom ∈ bndSet, (∑ slot ∈ car atom, S slot slot)
      ≤ (bndSet.card : ℝ) * Matrix.trace S := by
    have hstep : ∑ atom ∈ bndSet, (∑ slot ∈ car atom, S slot slot)
        ≤ ∑ _atom ∈ bndSet, Matrix.trace S :=
      Finset.sum_le_sum fun atom _ =>
        carrier_diag_le_trace hsymm hidem (car atom)
    rwa [Finset.sum_const, nsmul_eq_mul] at hstep
  have hrestle : ∑ atom ∈ specialᶜ, (∑ slot ∈ car atom, S slot slot)
      ≤ ((specialᶜ.card : ℕ) : ℝ) * (Matrix.trace S - 1)
        + ∑ atom ∈ specialᶜ, d atom := by
    have hstep : ∑ atom ∈ specialᶜ, (∑ slot ∈ car atom, S slot slot)
        ≤ ∑ atom ∈ specialᶜ, (Matrix.trace S - 1 + d atom) := by
      refine Finset.sum_le_sum fun atom hatom => ?_
      have hmem := Finset.mem_compl.mp hatom
      rw [hspecial, Finset.mem_union, Finset.mem_union] at hmem
      push Not at hmem
      exact carrier_diag_cap_of_read hsymm hidem (hsupp atom) (hread atom)
        (hnz atom) (hd0 atom hmem.1.1 hmem.1.2 hmem.2)
        (hd1 atom hmem.1.1 hmem.1.2 hmem.2)
    have hexpand : ∑ atom ∈ specialᶜ, (Matrix.trace S - 1 + d atom)
        = ((specialᶜ.card : ℕ) : ℝ) * (Matrix.trace S - 1)
          + ∑ atom ∈ specialᶜ, d atom := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith [hstep, hexpand.le, hexpand.ge]
  -- the cardinality bookkeeping
  have hcardle : pinSet.card + pairSet.card + bndSet.card ≤ m := by
    rw [← hcardSpecial]
    simpa [Fintype.card_fin] using Finset.card_le_univ special
  have hcardcompl : ((specialᶜ.card : ℕ) : ℝ)
      = (m : ℝ) - pinSet.card - pairSet.card - bndSet.card := by
    rw [Finset.card_compl, Fintype.card_fin, hcardSpecial,
      Nat.cast_sub hcardle, Nat.cast_add, Nat.cast_add]
    ring
  rw [hcardcompl] at hrestle
  -- the boundary values are nonnegative, thus the total sum dominates
  have hbndd : 0 ≤ ∑ atom ∈ bndSet, d atom :=
    Finset.sum_nonneg fun atom hatom => hbndNonneg atom hatom
  have hdtotal : ∑ atom ∈ pinSet, d atom + ∑ atom ∈ pairSet, d atom
      + ∑ atom ∈ specialᶜ, d atom + ∑ atom ∈ bndSet, d atom
      = ∑ atom, d atom := by
    have hall := Finset.sum_add_sum_compl special d
    have hsp := hsumSplit d
    linarith
  -- assemble
  have htotal := Finset.sum_add_sum_compl special
    (fun atom => ∑ slot ∈ car atom, S slot slot)
  have hsp := hsumSplit (fun atom => ∑ slot ∈ car atom, S slot slot)
  linarith [hdouble.le, hdouble.ge, htotal.le, htotal.ge, hsp.le, hsp.ge,
    hpineq.le, hpineq.ge, hpairle, hbndle, hrestle, hbndd, hdtotal.le,
    hdtotal.ge]

/-- **THE TRACE-TWO COUNT LAW.**  Six atoms with three atoms in each
block, a trace-two symmetric idempotent, a shifted weight sum
`6 * value + 1` at a negative value: the pin class is not larger than
the boundary class. -/
theorem pin_card_le_boundary_card_of_budget {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    (car : Fin 6 → Finset (Fin n)) (v : Fin 6 → Fin n → ℝ)
    (d : Fin 6 → ℝ) {value : ℝ}
    (hinc : ∀ slot : Fin n,
      (Finset.univ.filter fun atom => slot ∈ car atom).card = 3)
    (hsupp : ∀ atom, ∀ slot ∉ car atom, v atom slot = 0)
    (hnz : ∀ atom, v atom ≠ 0)
    (hread : ∀ atom, ∀ slot ∈ car atom,
      (S *ᵥ v atom) slot = d atom * v atom slot)
    (pinSet pairSet bndSet : Finset (Fin 6))
    (hpinPair : Disjoint pinSet pairSet) (hpinBnd : Disjoint pinSet bndSet)
    (hpairBnd : Disjoint pairSet bndSet)
    (hpin : ∀ atom ∈ pinSet, ∃ pinSlot, car atom = {pinSlot})
    (hpair : ∀ atom ∈ pairSet, ∃ slotOne slotTwo,
      slotOne ≠ slotTwo ∧ car atom = {slotOne, slotTwo})
    (hbndNonneg : ∀ atom ∈ bndSet, 0 ≤ d atom)
    (hd0 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → atom ∉ bndSet →
      0 < d atom)
    (hd1 : ∀ atom, atom ∉ pinSet → atom ∉ pairSet → atom ∉ bndSet →
      d atom < 1)
    (hsum : ∑ atom, d atom = 6 * value + 1) (hneg : value < 0) :
    pinSet.card ≤ bndSet.card := by
  have hbudget := carrier_budget_with_boundary hsymm hidem car v d 3 hinc
    hsupp hnz hread pinSet pairSet bndSet hpinPair hpinBnd hpairBnd hpin
    hpair hbndNonneg hd0 hd1
  rw [htrace, hsum] at hbudget
  norm_num at hbudget
  have hstrict : (pinSet.card : ℝ) < (bndSet.card : ℝ) + 1 := by linarith
  have : pinSet.card < bndSet.card + 1 := by exact_mod_cast hstrict
  omega

/-! ## Layer 3 — the datum census -/

/-- Every atom carries at least one basis slot. -/
theorem SharedPrivateData.multiplicity_pos {crux : SixThreeCrux}
    (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    0 < basisSupportMultiplicity data.tightDir data.basisLabel atomIndex := by
  classical
  obtain ⟨slot, hslot⟩ := exists_basisIndex_datumTightSupport data.hdata
    data.basisLabel data.hspan data.leftInv data.hleft atomIndex
  exact Finset.card_pos.mpr
    ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hslot⟩⟩

/-- The total multiplicity is three times the basis count: every basis
support carries three atoms. -/
theorem SharedPrivateData.sum_multiplicity {crux : SixThreeCrux}
    (data : SharedPrivateData crux) :
    ∑ atomIndex : Fin 6,
        basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
      = 3 * data.basisCount := by
  rw [sum_basisSupportMultiplicity data.tightDir data.basisLabel,
    Finset.sum_congr rfl fun slot _ => data.hthree slot, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

set_option maxHeartbeats 3200000 in
/-- **THE BOUNDARY COUNT LAW.**  At a diagonal Gram core with trace two,
the pin class is not larger than the boundary class.  The caller names
the boundary set and shows that every other atom with three or more
carriers is interior. -/
theorem SharedPrivateData.pin_card_le_boundary_card {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2)
    (bndSet : Finset (Fin 6))
    (hbndMult : ∀ atomIndex ∈ bndSet,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex)
    (hinterior : ∀ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex →
      atomIndex ∉ bndSet →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex = 1).card ≤ bndSet.card := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsuppFrame, hreadFrame,
    _hnorm, hnz, _hboundary, _hcarrierNz⟩ :=
    data.exists_kernel_read_frame hdiag
  set chartValue := chartObjective (chartPointOfDesign crux.design)
    with hchartValue
  set atomWeight := (chartPointOfDesign crux.design).weight with hatomWeight
  set shifted : Fin 6 → ℝ := fun atomIndex =>
    chartValue + atomWeight atomIndex with hshifted
  set car : Fin 6 → Finset (Fin data.basisCount) := fun atomIndex =>
    Finset.univ.filter fun slot =>
      atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcar
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
  have hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex,
      readVecs atomIndex slot = 0 := by
    intro atomIndex slot hslot
    exact hsuppFrame atomIndex slot fun hmem =>
      hslot ((hcarmem atomIndex slot).mpr hmem)
  have hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = shifted atomIndex * readVecs atomIndex slot := by
    intro atomIndex slot hslot
    exact hreadFrame atomIndex slot (datumTightSupport_subset data.hdata
      (hmemActive slot) ((hcarmem atomIndex slot).mp hslot))
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
  have hcarCard : ∀ atomIndex, (car atomIndex).card
      = basisSupportMultiplicity data.tightDir data.basisLabel atomIndex :=
    fun _ => rfl
  -- the three named classes
  set pinSet := Finset.univ.filter fun atomIndex =>
    basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 1
    with hpinSet
  set pairSet := Finset.univ.filter fun atomIndex =>
    basisSupportMultiplicity data.tightDir data.basisLabel atomIndex = 2
    with hpairSet
  have hmultBnd : ∀ atomIndex ∈ bndSet, 3 ≤ (car atomIndex).card :=
    fun atomIndex hatom => (hcarCard atomIndex) ▸ hbndMult atomIndex hatom
  have hpinPair : Disjoint pinSet pairSet := by
    refine Finset.disjoint_left.mpr fun atomIndex h1 h2 => ?_
    have hm1 := (Finset.mem_filter.mp h1).2
    have hm2 := (Finset.mem_filter.mp h2).2
    omega
  have hpinBnd : Disjoint pinSet bndSet := by
    refine Finset.disjoint_left.mpr fun atomIndex h1 h2 => ?_
    have hm1 := (Finset.mem_filter.mp h1).2
    have hm2 := hbndMult atomIndex h2
    omega
  have hpairBnd : Disjoint pairSet bndSet := by
    refine Finset.disjoint_left.mpr fun atomIndex h1 h2 => ?_
    have hm1 := (Finset.mem_filter.mp h1).2
    have hm2 := hbndMult atomIndex h2
    omega
  have hpin : ∀ atomIndex ∈ pinSet, ∃ pinSlot,
      car atomIndex = {pinSlot} := by
    intro atomIndex hmem
    exact Finset.card_eq_one.mp
      ((hcarCard atomIndex).trans (Finset.mem_filter.mp hmem).2)
  have hpair : ∀ atomIndex ∈ pairSet, ∃ slotOne slotTwo,
      slotOne ≠ slotTwo ∧ car atomIndex = {slotOne, slotTwo} := by
    intro atomIndex hmem
    exact Finset.card_eq_two.mp
      ((hcarCard atomIndex).trans (Finset.mem_filter.mp hmem).2)
  have hbndNonneg : ∀ atomIndex ∈ bndSet, 0 ≤ shifted atomIndex :=
    fun atomIndex _ =>
      capture_diagonal_nonneg_of_isChartStationaryData data.hdata atomIndex
  have hrestMult : ∀ atomIndex, atomIndex ∉ pinSet → atomIndex ∉ pairSet →
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex := by
    intro atomIndex hnotPin hnotPair
    have h1 : basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex ≠ 1 := fun h =>
      hnotPin (Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, h⟩)
    have h2 : basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex ≠ 2 := fun h =>
      hnotPair (Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, h⟩)
    have h0 := data.multiplicity_pos atomIndex
    omega
  have hd0 : ∀ atomIndex, atomIndex ∉ pinSet → atomIndex ∉ pairSet →
      atomIndex ∉ bndSet → 0 < shifted atomIndex :=
    fun atomIndex hnotPin hnotPair hnotBnd =>
      hinterior atomIndex (hrestMult atomIndex hnotPin hnotPair) hnotBnd
  have hd1 : ∀ atomIndex : Fin 6, shifted atomIndex < 1 := by
    intro atomIndex
    have hwle : atomWeight atomIndex ≤ 1 := by
      have hsumOne := data.hdata.weight_sum_one
      have hle : atomWeight atomIndex ≤ ∑ y, atomWeight y :=
        Finset.single_le_sum (f := atomWeight)
          (fun y _ => (data.hdata.weight_pos y).le)
          (Finset.mem_univ atomIndex)
      rwa [hsumOne] at hle
    have hneg : chartValue < 0 := data.hvalueNeg
    have hval : shifted atomIndex = chartValue + atomWeight atomIndex := rfl
    rw [hval]
    linarith
  have hsum : ∑ atomIndex, shifted atomIndex = 6 * chartValue + 1 := by
    have hexpand : ∑ atomIndex : Fin 6, shifted atomIndex
        = ∑ atomIndex : Fin 6, (chartValue + atomWeight atomIndex) := rfl
    rw [hexpand, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, data.hdata.weight_sum_one,
      nsmul_eq_mul]
    norm_num
  have hStrace2 : Matrix.trace S = 2 := by rw [hStrace, htrace]
  exact pin_card_le_boundary_card_of_budget hSsymm hSidem hStrace2 car
    readVecs shifted hinc hsupp hnz hread pinSet pairSet bndSet hpinPair
    hpinBnd hpairBnd hpin hpair hbndNonneg hd0
    (fun atomIndex _ _ _ => hd1 atomIndex) hsum data.hvalueNeg

open scoped Classical in
/-- The boundary set of a datum: the atoms with three or more carriers
whose shifted weight vanishes. -/
noncomputable def SharedPrivateData.boundarySet {crux : SixThreeCrux}
    (data : SharedPrivateData crux) : Finset (Fin 6) :=
  Finset.univ.filter fun atomIndex =>
    3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
      ∧ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0

theorem SharedPrivateData.mem_boundarySet {crux : SixThreeCrux}
    (data : SharedPrivateData crux) {atomIndex : Fin 6} :
    atomIndex ∈ data.boundarySet ↔
      (3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
        ∧ chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0) := by
  unfold SharedPrivateData.boundarySet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **THE PIN-BOUNDARY LAW.**  At trace two the pin class is not larger
than the boundary set. -/
theorem SharedPrivateData.pin_card_le_boundarySet_card {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) :
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex = 1).card ≤ data.boundarySet.card := by
  classical
  refine data.pin_card_le_boundary_card hdiag htrace data.boundarySet
    (fun atomIndex hatom => (data.mem_boundarySet.mp hatom).1) ?_
  intro atomIndex hmult hnot
  rcases (capture_diagonal_nonneg_of_isChartStationaryData data.hdata
    atomIndex).lt_or_eq with hpos | heq
  · exact hpos
  · exact absurd (data.mem_boundarySet.mpr ⟨hmult, heq.symm⟩) hnot

/-- **THE BOUNDARY EXISTENCE.**  At trace two some atom with three or
more carriers sits at the shifted-weight boundary.  The pin atom is one
pin, and the count law needs a boundary atom for it. -/
theorem SharedPrivateData.exists_boundary_atom {crux : SixThreeCrux}
    (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) :
    ∃ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
        ∧ chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atomIndex = 0 := by
  classical
  have hle := data.pin_card_le_boundarySet_card hdiag htrace
  have hpinMem : data.pinAtom ∈ Finset.univ.filter fun atomIndex =>
      basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex = 1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ data.pinAtom, data.hmultOne⟩
  have hpos : 0 < data.boundarySet.card :=
    lt_of_lt_of_le (Finset.card_pos.mpr ⟨data.pinAtom, hpinMem⟩) hle
  obtain ⟨atomIndex, hatom⟩ := Finset.card_pos.mp hpos
  exact ⟨atomIndex, data.mem_boundarySet.mp hatom⟩

/-! ## Layer 4 — the multiplicity arithmetic -/

set_option maxHeartbeats 1200000 in
/-- **THE PROFILE ARITHMETIC.**  The multiplicity classes of a datum
count six atoms, and the multiplicity sum bounds the two upper classes.
The pin class is the complement of the two-or-more class. -/
theorem SharedPrivateData.profile_arithmetic {crux : SixThreeCrux}
    (data : SharedPrivateData crux) :
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex = 1).card
        + (Finset.univ.filter fun atomIndex =>
            2 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
              atomIndex).card = 6
      ∧ 6 + (Finset.univ.filter fun atomIndex =>
            2 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
              atomIndex).card
          + (Finset.univ.filter fun atomIndex =>
              3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
                atomIndex).card
        ≤ 3 * data.basisCount := by
  classical
  set mult := basisSupportMultiplicity data.tightDir data.basisLabel
    with hmult
  set bound : Fin 6 → ℕ := fun atomIndex =>
    1 + (if 2 ≤ mult atomIndex then 1 else 0)
      + (if 3 ≤ mult atomIndex then 1 else 0) with hbound
  have hpointwise : ∀ atomIndex, bound atomIndex ≤ mult atomIndex := by
    intro atomIndex
    have hpos : 0 < mult atomIndex := data.multiplicity_pos atomIndex
    show 1 + (if 2 ≤ mult atomIndex then 1 else 0)
        + (if 3 ≤ mult atomIndex then 1 else 0) ≤ mult atomIndex
    split_ifs <;> omega
  have hindTwo : ∑ atomIndex : Fin 6,
      (if 2 ≤ mult atomIndex then 1 else 0)
      = (Finset.univ.filter fun atomIndex => 2 ≤ mult atomIndex).card := by
    rw [Finset.card_filter]
  have hindThree : ∑ atomIndex : Fin 6,
      (if 3 ≤ mult atomIndex then 1 else 0)
      = (Finset.univ.filter fun atomIndex => 3 ≤ mult atomIndex).card := by
    rw [Finset.card_filter]
  have hsumBound : ∑ atomIndex, bound atomIndex
      = 6 + (Finset.univ.filter fun atomIndex => 2 ≤ mult atomIndex).card
        + (Finset.univ.filter fun atomIndex => 3 ≤ mult atomIndex).card := by
    have hexpand : ∑ atomIndex : Fin 6, bound atomIndex
        = ∑ atomIndex : Fin 6, (1 + (if 2 ≤ mult atomIndex then 1 else 0)
            + (if 3 ≤ mult atomIndex then 1 else 0)) := rfl
    rw [hexpand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one, hindTwo, hindThree]
  have hle : ∑ atomIndex, bound atomIndex ≤ ∑ atomIndex, mult atomIndex :=
    Finset.sum_le_sum fun atomIndex _ => hpointwise atomIndex
  have hsumMult : ∑ atomIndex, mult atomIndex = 3 * data.basisCount :=
    data.sum_multiplicity
  have hcomplement : (Finset.univ.filter fun atomIndex => mult atomIndex = 1)
      = Finset.univ.filter fun atomIndex => ¬ 2 ≤ mult atomIndex := by
    refine Finset.filter_congr fun atomIndex _ => ?_
    have hpos : 0 < mult atomIndex := data.multiplicity_pos atomIndex
    constructor
    · intro h; omega
    · intro h; omega
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 6)))
    (p := fun atomIndex => 2 ≤ mult atomIndex)
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  refine ⟨?_, ?_⟩
  · rw [hcomplement]
    omega
  · omega

set_option maxHeartbeats 1200000 in
/-- **THE BASIS-COUNT FLOOR.**  At a diagonal Gram core with trace two
the basis count is at least four.  The count law forces the two upper
classes to twelve incidences, and the multiplicity sum prices them. -/
theorem SharedPrivateData.four_le_basisCount_of_trace_two
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) : 4 ≤ data.basisCount := by
  classical
  obtain ⟨hcount, hsum⟩ := data.profile_arithmetic
  have hle := data.pin_card_le_boundarySet_card hdiag htrace
  have hsub : data.boundarySet ⊆ Finset.univ.filter fun atomIndex =>
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex := by
    intro atomIndex hatom
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ atomIndex, (data.mem_boundarySet.mp hatom).1⟩
  have hbig := Finset.card_le_card hsub
  have hthreeTwo : (Finset.univ.filter fun atomIndex =>
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex).card
      ≤ (Finset.univ.filter fun atomIndex =>
          2 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
            atomIndex).card := by
    refine Finset.card_le_card fun atomIndex hatom => ?_
    have hmem := (Finset.mem_filter.mp hatom).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, by omega⟩
  omega

set_option maxHeartbeats 1600000 in
/-- **THE RANK-FOUR RIGIDITY.**  At basis count four and trace two the
multiplicity bound and the count law meet.  Every atom with three or
more carriers has exactly three carriers and sits at the boundary, and
the pin class and the three-carrier class have equal cardinality. -/
theorem SharedPrivateData.boundary_rigid_of_basisCount_four
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) (hbasis : data.basisCount = 4) :
    (∀ atomIndex : Fin 6,
        3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex →
        basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex = 3)
      ∧ (∀ atomIndex : Fin 6,
          3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
            atomIndex →
          chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight atomIndex = 0)
      ∧ (Finset.univ.filter fun atomIndex =>
            basisSupportMultiplicity data.tightDir data.basisLabel
              atomIndex = 1).card
          = (Finset.univ.filter fun atomIndex =>
              3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
                atomIndex).card := by
  classical
  obtain ⟨hcount, hsumBound⟩ := data.profile_arithmetic
  have hle := data.pin_card_le_boundarySet_card hdiag htrace
  have hsumMult : ∑ atomIndex,
      basisSupportMultiplicity data.tightDir data.basisLabel atomIndex
      = 3 * data.basisCount := data.sum_multiplicity
  have hbc : 3 * data.basisCount = 12 := by rw [hbasis]
  set mult := basisSupportMultiplicity data.tightDir data.basisLabel
    with hmult
  set bigSet := Finset.univ.filter fun atomIndex => 3 ≤ mult atomIndex
    with hbigSet
  set twoSet := Finset.univ.filter fun atomIndex => 2 ≤ mult atomIndex
    with htwoSet
  set pinSet := Finset.univ.filter fun atomIndex => mult atomIndex = 1
    with hpinSet
  have hsub : data.boundarySet ⊆ bigSet := by
    intro atomIndex hatom
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ atomIndex, (data.mem_boundarySet.mp hatom).1⟩
  have hbig := Finset.card_le_card hsub
  have hthreeTwo : bigSet.card ≤ twoSet.card := by
    refine Finset.card_le_card fun atomIndex hatom => ?_
    have hmem := (Finset.mem_filter.mp hatom).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, by omega⟩
  -- the two bounds meet
  have hpinEq : pinSet.card = bigSet.card := by omega
  have hbndEq : data.boundarySet.card = bigSet.card := by omega
  have hbndSet : data.boundarySet = bigSet :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hbndEq.symm)
  -- the multiplicity slack is exhausted
  set bound : Fin 6 → ℕ := fun atomIndex =>
    1 + (if 2 ≤ mult atomIndex then 1 else 0)
      + (if 3 ≤ mult atomIndex then 1 else 0) with hbound
  have hpointwise : ∀ atomIndex, bound atomIndex ≤ mult atomIndex := by
    intro atomIndex
    have hpos : 0 < mult atomIndex := data.multiplicity_pos atomIndex
    show 1 + (if 2 ≤ mult atomIndex then 1 else 0)
        + (if 3 ≤ mult atomIndex then 1 else 0) ≤ mult atomIndex
    split_ifs <;> omega
  have hindTwo : ∑ atomIndex : Fin 6,
      (if 2 ≤ mult atomIndex then 1 else 0) = twoSet.card := by
    rw [htwoSet, Finset.card_filter]
  have hindThree : ∑ atomIndex : Fin 6,
      (if 3 ≤ mult atomIndex then 1 else 0) = bigSet.card := by
    rw [hbigSet, Finset.card_filter]
  have hsumBoundEq : ∑ atomIndex, bound atomIndex
      = 6 + twoSet.card + bigSet.card := by
    have hexpand : ∑ atomIndex : Fin 6, bound atomIndex
        = ∑ atomIndex : Fin 6, (1 + (if 2 ≤ mult atomIndex then 1 else 0)
            + (if 3 ≤ mult atomIndex then 1 else 0)) := rfl
    rw [hexpand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one, hindTwo, hindThree]
  have hsumEq : ∑ atomIndex, bound atomIndex
      = ∑ atomIndex, mult atomIndex := by
    rw [hsumBoundEq, hsumMult]
    omega
  have htight : ∀ atomIndex : Fin 6, bound atomIndex = mult atomIndex := by
    intro atomIndex
    by_contra hne
    have hlt : bound atomIndex < mult atomIndex :=
      lt_of_le_of_ne (hpointwise atomIndex) hne
    have hstrict : ∑ y, bound y < ∑ y, mult y :=
      Finset.sum_lt_sum (fun y _ => hpointwise y)
        ⟨atomIndex, Finset.mem_univ atomIndex, hlt⟩
    omega
  refine ⟨?_, ?_, hpinEq⟩
  · intro atomIndex hthree
    have h2 : 2 ≤ mult atomIndex := by omega
    have hb : 1 + (if 2 ≤ mult atomIndex then 1 else 0)
        + (if 3 ≤ mult atomIndex then 1 else 0) = mult atomIndex :=
      htight atomIndex
    rw [if_pos h2, if_pos hthree] at hb
    omega
  · intro atomIndex hthree
    have hmem : atomIndex ∈ bigSet :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ atomIndex, hthree⟩
    rw [← hbndSet] at hmem
    exact (data.mem_boundarySet.mp hmem).2

/-! ## Layer 5 — the private-slot independence kill -/

/-- A family with an independent span has a kernel-free Gram: the
quadratic form of the Gram is the energy of the combination. -/
theorem gram_kernel_free_of_independent {m n : ℕ} (V : Fin m → Fin n → ℝ)
    (hind : ∀ x : Fin m → ℝ, (∀ slot, ∑ i, x i * V i slot = 0) → x = 0) :
    ∀ x : Fin m → ℝ,
      (Matrix.of fun i j => V i ⬝ᵥ V j) *ᵥ x = 0 → x = 0 := by
  intro x hx
  classical
  set Vmat : Matrix (Fin n) (Fin m) ℝ :=
    Matrix.of fun slot i => V i slot with hVmat
  have hgram : Vmatᵀ * Vmat = Matrix.of fun i j => V i ⬝ᵥ V j := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ slot, Vmat slot i * Vmat slot j = V i ⬝ᵥ V j
    rw [dotProduct]
    rfl
  have hq : x ⬝ᵥ ((Vmatᵀ * Vmat) *ᵥ x) = 0 := by
    rw [hgram, hx, dotProduct_zero]
  have hswap : x ⬝ᵥ ((Vmatᵀ * Vmat) *ᵥ x) = (Vmat *ᵥ x) ⬝ᵥ (Vmat *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [hswap] at hq
  have hzero : Vmat *ᵥ x = 0 := by
    funext slot
    rw [dotProduct] at hq
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_self_nonneg ((Vmat *ᵥ x) i)).mp hq slot (Finset.mem_univ slot)
    simpa using mul_self_eq_zero.mp hall
  refine hind x fun slot => ?_
  have happly := congrFun hzero slot
  rw [Matrix.mulVec, dotProduct] at happly
  have hcongr : ∑ i, x i * V i slot = ∑ i, Vmat slot i * x i :=
    Finset.sum_congr rfl fun i _ => by
      show x i * V i slot = Vmat slot i * x i
      exact mul_comm _ _
  rw [hcongr]
  simpa using happly

/-- **THE PRIVATE-SLOT INDEPENDENCE.**  A family of supported vectors,
each with one slot that no other family member carries, is independent:
the private slot reads the coefficient directly. -/
theorem independent_of_private_slot {m n : ℕ} (V : Fin m → Fin n → ℝ)
    (car : Fin m → Finset (Fin n))
    (hsupp : ∀ i, ∀ slot ∉ car i, V i slot = 0)
    (priv : Fin m → Fin n) (hprivNz : ∀ i, V i (priv i) ≠ 0)
    (hprivOut : ∀ i j, j ≠ i → priv i ∉ car j) :
    ∀ x : Fin m → ℝ, (∀ slot, ∑ i, x i * V i slot = 0) → x = 0 := by
  intro x hx
  funext i
  have hrow := hx (priv i)
  have hcollapse : ∑ j, x j * V j (priv i) = x i * V i (priv i) := by
    refine Finset.sum_eq_single i (fun j _ hne => ?_) (fun hnot => ?_)
    · rw [hsupp j (priv i) (hprivOut i j hne), mul_zero]
    · exact absurd (Finset.mem_univ i) hnot
  rw [hcollapse] at hrow
  rcases mul_eq_zero.mp hrow with h | h
  · exact h
  · exact absurd h (hprivNz i)

set_option maxHeartbeats 1600000 in
/-- **THE PRIVATE-SLOT KILL.**  At a diagonal Gram core, a family of
boundary atoms with one private carrier slot each, one atom more than
the complement trace, kills the datum.  Each boundary read lies wholly
in the kernel of the coefficient idempotent, the private slots make the
family independent, and the trace floor refuses the count.  Pairwise
disjoint carriers are the special case in which every slot is private. -/
theorem SharedPrivateData.false_of_private_slot_boundary_family
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (T : Finset (Fin 6))
    (hbnd : ∀ y ∈ T, chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight y = 0)
    (hprivate : ∀ y ∈ T, ∃ slot : Fin data.basisCount,
      y ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∀ y' ∈ T, y' ≠ y →
          y' ∉ datumTightSupport data.tightDir (data.basisLabel slot))
    (hcount : (data.basisCount : ℝ)
      < Matrix.trace data.coeff + T.card) : False := by
  classical
  obtain ⟨S, readVecs, hSsymm, hSidem, hStrace, hsupp, _hread, _hnorm,
    _hnz, hboundary, hcarrierNz⟩ :=
    data.exists_kernel_read_frame hdiag
  set count := T.card with hcountDef
  set enum := T.orderIsoOfFin (rfl : T.card = count) with henum
  set atomOf : Fin count → Fin 6 := fun i =>
    ((enum i : {x // x ∈ T}) : Fin 6) with hatomOf
  have hatomMem : ∀ i : Fin count, atomOf i ∈ T := fun i => (enum i).2
  have hatomNe : ∀ i j : Fin count, i ≠ j → atomOf i ≠ atomOf j := by
    intro i j hne hcontra
    exact hne (enum.toEquiv.injective (Subtype.coe_injective hcontra))
  set V : Fin count → Fin data.basisCount → ℝ := fun i =>
    readVecs (atomOf i) with hV
  -- the boundary reads are kernel vectors, thus the complement fixes them
  have hcomplSymm : (1 - S)ᵀ = 1 - S := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hSsymm]
  have hcomplIdem : (1 - S) * (1 - S) = 1 - S := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hSidem]
    abel
  have hfix : ∀ i : Fin count, (1 - S) *ᵥ V i = V i := by
    intro i
    have hzero := hboundary (atomOf i) (hbnd (atomOf i) (hatomMem i))
    show (1 - S) *ᵥ readVecs (atomOf i) = readVecs (atomOf i)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hzero, sub_zero]
  -- the private slots make the family independent
  set car : Fin count → Finset (Fin data.basisCount) := fun i =>
    Finset.univ.filter fun slot =>
      atomOf i ∈ datumTightSupport data.tightDir (data.basisLabel slot)
    with hcar
  have hcarSupp : ∀ i : Fin count, ∀ slot ∉ car i, V i slot = 0 := by
    intro i slot hslot
    refine hsupp (atomOf i) slot ?_
    intro hmem
    exact hslot (Finset.mem_filter.mpr ⟨Finset.mem_univ slot, hmem⟩)
  have hprivChoice : ∀ i : Fin count, ∃ slot : Fin data.basisCount,
      atomOf i ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ ∀ j : Fin count, j ≠ i →
          atomOf j ∉ datumTightSupport data.tightDir
            (data.basisLabel slot) := by
    intro i
    obtain ⟨slot, hmem, hout⟩ := hprivate (atomOf i) (hatomMem i)
    refine ⟨slot, hmem, fun j hne => ?_⟩
    exact hout (atomOf j) (hatomMem j) (hatomNe j i hne)
  choose priv hprivMem hprivOut using hprivChoice
  have hprivNz : ∀ i : Fin count, V i (priv i) ≠ 0 :=
    fun i => hcarrierNz (atomOf i) (priv i) (hprivMem i)
  have hprivNotCar : ∀ i j : Fin count, j ≠ i → priv i ∉ car j := by
    intro i j hne hmem
    exact hprivOut i j hne (Finset.mem_filter.mp hmem).2
  have hker := gram_kernel_free_of_independent V
    (independent_of_private_slot V car hcarSupp priv hprivNz hprivNotCar)
  -- the trace floor refuses the count
  have hfloor := trace_floor_of_fixed_family hcomplSymm hcomplIdem V hfix
    hker
  have htraceCompl : Matrix.trace ((1 : Matrix (Fin data.basisCount)
      (Fin data.basisCount) ℝ) - S)
      = (data.basisCount : ℝ) - Matrix.trace data.coeff := by
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, hStrace]
  rw [htraceCompl] at hfloor
  rw [hcountDef] at hfloor
  linarith

/-! ## Layer 6 — the pin-complement law -/

set_option maxHeartbeats 800000 in
/-- **THE PIN-COMPLEMENT LAW.**  At basis count four and trace two, two
distinct atoms off the private block share a block.  Two such atoms with
no common block would join the pin atom in a three-atom disjoint family,
and the disjoint-family kill refuses it. -/
theorem SharedPrivateData.cocarrier_offPrivate_of_basisCount_four
    {crux : SixThreeCrux} (data : SharedPrivateData crux)
    {gramDiag : Fin data.basisCount → ℝ}
    (hdiag : data.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace data.coeff = 2) (hbasis : data.basisCount = 4)
    {atomOne atomTwo : Fin 6}
    (hone : atomOne ∉ datumTightSupport data.tightDir
      (data.basisLabel data.privateSlot))
    (htwo : atomTwo ∉ datumTightSupport data.tightDir
      (data.basisLabel data.privateSlot))
    (hne : atomOne ≠ atomTwo) :
    ∃ slot : Fin data.basisCount,
      atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot)
        ∧ atomTwo ∈ datumTightSupport data.tightDir
          (data.basisLabel slot) := by
  classical
  by_contra hnot
  push Not at hnot
  have hpinMem : data.pinAtom ∈ datumTightSupport data.tightDir
      (data.basisLabel data.privateSlot) :=
    mem_datumTightSupport.mpr data.hpinNe
  have hpinOne : data.pinAtom ≠ atomOne := fun h => hone (h ▸ hpinMem)
  have hpinTwo : data.pinAtom ≠ atomTwo := fun h => htwo (h ▸ hpinMem)
  set T : Finset (Fin 6) := {data.pinAtom, atomOne, atomTwo} with hT
  have hcard : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [hpinOne, hpinTwo]),
      Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hmemT : ∀ y ∈ T, y = data.pinAtom ∨ y = atomOne ∨ y = atomTwo := by
    intro y hy
    rw [hT] at hy
    simpa using hy
  have hdisjoint : ∀ y ∈ T, ∀ y' ∈ T, y ≠ y' →
      ∀ slot : Fin data.basisCount,
        y ∈ datumTightSupport data.tightDir (data.basisLabel slot) →
        y' ∉ datumTightSupport data.tightDir (data.basisLabel slot) := by
    intro y hy y' hy' hyne slot hmem
    rcases hmemT y hy with hy1 | hy2 | hy3
    · subst hy1
      rcases hmemT y' hy' with h1 | h2 | h3
      · exact absurd h1.symm hyne
      · subst h2
        exact data.pin_disjoint_of_offSupport hone slot hmem
      · subst h3
        exact data.pin_disjoint_of_offSupport htwo slot hmem
    · subst hy2
      rcases hmemT y' hy' with h1 | h2 | h3
      · subst h1
        intro hcontra
        exact data.pin_disjoint_of_offSupport hone slot hcontra hmem
      · exact absurd h2.symm hyne
      · subst h3
        exact fun hcontra => hnot slot hmem hcontra
    · subst hy3
      rcases hmemT y' hy' with h1 | h2 | h3
      · subst h1
        intro hcontra
        exact data.pin_disjoint_of_offSupport htwo slot hcontra hmem
      · subst h2
        exact fun hcontra => hnot slot hcontra hmem
      · exact absurd h3.symm hyne
  have hcast : (data.basisCount : ℝ) = 4 := by rw [hbasis]; norm_num
  refine data.false_of_disjoint_support_family hdiag T hdisjoint ?_
  rw [htrace, hcard, hcast]
  norm_num

/-! ## Layer 7 — the two narrowed residues and the dispatch -/

/-- **THE RANK-FOUR BOUNDARY RESIDUE.**  A diagonal-Gram datum at basis
count four and trace two with the full rigidity: every atom with three
or more carriers has exactly three carriers and sits at the boundary,
the pin class and the three-carrier class have equal cardinality, and
the complement of the private block is pairwise co-carrier. -/
def SharedPrivateBoundaryFourClosed : Prop :=
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
    (∀ atomOne : Fin 6, atomOne ∉ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot) →
      ∀ atomTwo : Fin 6, atomTwo ∉ datumTightSupport data.tightDir
        (data.basisLabel data.privateSlot) →
      atomOne ≠ atomTwo →
      ∃ slot : Fin data.basisCount,
        atomOne ∈ datumTightSupport data.tightDir (data.basisLabel slot)
          ∧ atomTwo ∈ datumTightSupport data.tightDir
            (data.basisLabel slot)) →
    ∀ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 →
      False

/-- **THE HIGH BOUNDARY RESIDUE.**  A diagonal-Gram datum at basis count
five or more and trace two, with the pin class not larger than the
boundary class. -/
def SharedPrivateBoundaryHighClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (gramDiag : Fin data.basisCount → ℝ),
    data.gram = Matrix.diagonal gramDiag →
    Matrix.trace data.coeff = 2 →
    5 ≤ data.basisCount →
    (Finset.univ.filter fun atomIndex =>
        basisSupportMultiplicity data.tightDir data.basisLabel
          atomIndex = 1).card ≤ data.boundarySet.card →
    ∀ atomIndex : Fin 6,
      3 ≤ basisSupportMultiplicity data.tightDir data.basisLabel
        atomIndex →
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex = 0 →
      False

/-- **THE BOUNDARY DISPATCH.**  The two narrowed residues close the
trace-two boundary residue.  The basis-count floor kills every count
below four, the rank-four rigidity and the pin-complement law feed the
first residue, and the count law feeds the second. -/
theorem sharedPrivateBoundaryClosed_of_split
    (hfour : SharedPrivateBoundaryFourClosed)
    (hhigh : SharedPrivateBoundaryHighClosed) :
    SharedPrivateBoundaryClosed := by
  intro crux data gramDiag hdiag htrace atomIndex hmult hzero
  classical
  have hfloor := data.four_le_basisCount_of_trace_two hdiag htrace
  rcases Nat.lt_or_ge data.basisCount 5 with hlt | hge
  · have hbasis : data.basisCount = 4 := by omega
    obtain ⟨hexact, hbnd, hcards⟩ :=
      data.boundary_rigid_of_basisCount_four hdiag htrace hbasis
    exact hfour crux data gramDiag hdiag htrace hbasis hexact hbnd hcards
      (fun atomOne hone atomTwo htwo hne =>
        data.cocarrier_offPrivate_of_basisCount_four hdiag htrace hbasis
          hone htwo hne)
      atomIndex hmult hzero
  · exact hhigh crux data gramDiag hdiag htrace hge
      (data.pin_card_le_boundarySet_card hdiag htrace) atomIndex hmult hzero

/-- **THE REFINED STRATA DISPATCH.**  The extras residue, the two
boundary residues, and the deficit residue close the generic
shared-private kill. -/
theorem sharedPrivateKilled_of_strata_boundary
    (hextras : SharedPrivateExtrasClosed)
    (hfour : SharedPrivateBoundaryFourClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_strata hextras
    (sharedPrivateBoundaryClosed_of_split hfour hhigh) hdeficit

/-- The refined residues discharge closure two of the rank-four rung. -/
theorem rankFourSharedPrivateClosed_of_boundary_strata
    (hextras : SharedPrivateExtrasClosed)
    (hfour : SharedPrivateBoundaryFourClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_strata_boundary hextras hfour hhigh hdeficit)

/-- The refined residues discharge the shared-private closure of the
rank-five rung. -/
theorem rankFiveSharedPrivateClosed_of_boundary_strata
    (hextras : SharedPrivateExtrasClosed)
    (hfour : SharedPrivateBoundaryFourClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_strata_boundary hextras hfour hhigh hdeficit)

/-- The refined residues discharge the shared-private closure of the
rank-six rung. -/
theorem rankSixSharedPrivateClosed_of_boundary_strata
    (hextras : SharedPrivateExtrasClosed)
    (hfour : SharedPrivateBoundaryFourClosed)
    (hhigh : SharedPrivateBoundaryHighClosed)
    (hdeficit : SharedPrivateDeficitClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_strata_boundary hextras hfour hhigh hdeficit)

end Gtz
