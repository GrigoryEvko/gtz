import Gtz.Wave.OuterColumnGramFold
import Gtz.Wave.SharedPrivateKernelGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer zero and the profile lattice — the degree split of the third rung

The rank-six kill lattice of the column-Gram fold reduces the third rung
to two residues: the circuit residue and the LOW-PROFILE residue.  This
module opens the low-profile residue.

Three layers do the work.

The first layer prices a FULL block carrier.  When one atom sits in the
block of every basis slot, the read law holds at every slot, thus the
row of the chart at that atom is the shifted weight times the unit row.
The two-sided inverse of the basis carries that reading from the basis
columns to the whole ambient row.  Idempotence then prices the diagonal
entry as its own square, so the shifted weight is zero or one.  At rank
six the shifted weight is strictly between zero and one, thus NO atom
carries every slot.  The kill needs no Gram core and no circuit
residue.

The second layer prices the degree census.  The block carriers of a
rank-six frame carry eighteen incidences over six nonempty carriers.
If no carrier is small, that is, if every carrier holds three slots or
more, then a carrier of four slots or more pushes the census above
eighteen.  Thus every rank-six frame is REGULAR, with all six carriers
of card three, or LIGHT, with a carrier of card two or less.  The
dichotomy is complete, and it splits the low-profile residue into the
regular residue and the thin residue.

The third layer prices the OUTER ZERO.  The pair column of an outer
datum has a tight support of card two inside a block of card three,
thus one block atom reads zero on that column.  The two-sided inverse
keeps the row of that atom alive, so the atom carries a second slot.
The outer zero atom is thus never a pin, and in the regular stratum its
tight support is a proper nonempty part of its three-slot carrier.

The fourth layer supplies the boundary engine of the trace-two branch.
A vanished shifted weight prices the capture energy of the read vector
at zero, and the energy of a symmetric idempotent is the square norm of
the capture.  Thus the read vector of a boundary atom lies WHOLLY in
the kernel of the conjugate, at every slot and not only on its carrier.
The kernel vectors are fixed by the complementary idempotent, so the
landed trace floor counts a disjoint-carrier boundary family below the
kernel dimension.

The fifth layer prices the TIGHT census, the support-side analogue of
the block census.  The pair column of an outer datum carries two atoms
while every column block carries three, thus the tight census stops at
seventeen against the block census of eighteen.  Some atom therefore
has a tight carrier strictly inside its block carrier.

The sixth layer prices a PIN.  A pin atom carries one slot, thus its
ambient row holds one live entry, and the two-sided inverse
concentrates the inverse row of the pin slot on the pin atom.  Two pin
atoms never share a pin slot, and the coefficient matrix reads the
shifted weight of the pin atom on the diagonal of the pin slot.  In the
regular stratum no pin and no pair exists, thus the regular stratum
carries profile mass zero and the split of the low-profile residue
loses nothing.

The last layer generalizes the degree dichotomy to every rank.  Six
nonempty carriers need eighteen incidences to stay at card three, and a
basis of `basisCount` slots supplies `3 basisCount` only.  A carrier of
card one pays two of the deficit and a carrier of card two pays one,
thus `18 ≤ 3 basisCount + 2 p + q`.  The floor is six at rank four,
three at rank five, and zero at rank six.  At rank five with a diagonal
Gram core and capture trace three the floor meets the refined kill, so
the profile mass is EXACTLY three.  At rank six the same reading caps
the mass at three, thus the low-profile residue is the whole rank-six
diagonal-Gram branch.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.dot_mulVec_comm_of_symm` — the adjoint reading of a symmetric
  matrix.
* `Gtz.projection_row_eq_of_full_block` — **THE FULL-CARRIER ROW LAW.**
* `Gtz.false_of_full_block_carrier` — **THE FULL-CARRIER KILL.**
* `Gtz.RankSixFrame.shifted_weight_lt_one` — the shifted weight window.
* `Gtz.RankSixFrame.blockCarrier_ne_univ` — **NO RANK-SIX ATOM CARRIES
  EVERY SLOT.**
* `Gtz.RankSixFrame.blockCarrier_card_le_five` — the carrier ceiling.
* `Gtz.RankSixFrame.blockCarrier_card_sum` — the eighteen incidences.
* `Gtz.RankSixFrame.blockCarrier_card_pos` — the carrier floor.
* `Gtz.RankSixFrame.regular_or_light` — **THE DEGREE DICHOTOMY.**
* `Gtz.RankSixOuterData.exists_outer_zero_atom` — **THE OUTER ZERO.**
* `Gtz.RankSixOuterData.two_le_zero_atom_carrier` — the outer zero atom
  carries two slots.
* `Gtz.RankSixOuterData.zero_atom_not_pin` — it is never a pin.
* `Gtz.RankSixOuterData.regular_zero_atom_deficient` — the regular
  reading of the outer zero.
* `Gtz.RankSixOuterRegularClosed` — the regular residue.
* `Gtz.RankSixOuterThinClosed` — the thin residue.
* `Gtz.rankSixOuterLowProfileClosed_of_regular_and_thin` — **THE
  LOW-PROFILE SPLIT.**
* `Gtz.rankSixOuterKilled_of_circuit_regular_thin` — the three-residue
  kill.
* `Gtz.rankSixSupportTwoClosed_of_circuit_regular_thin` — **THE RANK-SIX
  DISCHARGE FROM THREE RESIDUES.**
* `Gtz.read_kernel_of_boundary` — **THE BOUNDARY KERNEL LAW.**
* `Gtz.kernel_fixed_of_complement` — the complementary fixed reading.
* `Gtz.boundary_family_card_le` — **THE BOUNDARY TRACE FLOOR.**
* `Gtz.false_of_boundary_disjoint_family` — the boundary family kill.
* `Gtz.boundary_family_card_le_of_trace_two` — the trace-two ceiling.
* `Gtz.tightCarrier` — the tight carrier of an atom.
* `Gtz.mem_tightCarrier` — its membership reading.
* `Gtz.tightCarrier_subset_blockCarrier` — the tight carrier sits in the
  block carrier.
* `Gtz.tightCarrier_double_count` — **THE TIGHT CENSUS.**
* `Gtz.RankSixOuterData.tight_incidence_le_seventeen` — **THE OUTER
  TIGHT CEILING.**
* `Gtz.RankSixOuterData.exists_tight_deficient_atom` — **THE TIGHT
  DEFICIENCY.**
* `Gtz.RankSixFrame.pin_leftInv_row` — **THE PIN ROW LAW.**
* `Gtz.RankSixFrame.pin_dir_ne_zero` — the pin scale is alive.
* `Gtz.RankSixFrame.pin_leftInv_off` — the concentrated inverse row.
* `Gtz.RankSixFrame.pin_slot_inj` — **THE PIN SLOT INJECTION.**
* `Gtz.RankSixFrame.pin_coeff_diagonal` — **THE PIN COEFFICIENT
  DIAGONAL.**
* `Gtz.RankSixFrame.regular_pinSet_empty` — no pin in the regular
  stratum.
* `Gtz.RankSixFrame.regular_pairSet_empty` — no pair in the regular
  stratum.
* `Gtz.RankSixFrame.regular_profile_zero` — **THE FAITHFUL SPLIT.**
* `Gtz.rankSixOuterRegularClosed_of_lowProfile` — the converse reading.
* `Gtz.blockPinSet` / `Gtz.blockPairSet` — the profile sets of a basis.
* `Gtz.blockPin_pair_disjoint`, `Gtz.blockPinSet_singleton`,
  `Gtz.blockPairSet_pair` — their readings.
* `Gtz.blockCarrier_profile_floor` — **THE PROFILE MASS FLOOR.**
* `Gtz.RankFiveFrame.profile_mass_ge_three` — the rank-five floor.
* `Gtz.RankFourFrame.profile_mass_ge_six` — the rank-four floor.
* `Gtz.RankFiveFrame.profile_mass_eq_three_of_trace_three` — **THE
  RANK-FIVE TRACE-THREE NARROWING.**
* `Gtz.RankSixFrame.profile_mass_le_three_of_diagonal_gram` — **THE
  RANK-SIX PROFILE CEILING.**

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.  The matrix statements of layers
zero, one, four, and five are unconditional.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the adjoint reading -/

/-- The adjoint reading of a symmetric matrix: the matrix moves across
the dot product. -/
theorem dot_mulVec_comm_of_symm {slotCount : ℕ}
    {mat : Matrix (Fin slotCount) (Fin slotCount) ℝ} (hsymm : matᵀ = mat)
    (leftVec rightVec : Fin slotCount → ℝ) :
    leftVec ⬝ᵥ (mat *ᵥ rightVec) = (mat *ᵥ leftVec) ⬝ᵥ rightVec := by
  classical
  have hentry : ∀ rowIndex colIndex : Fin slotCount,
      mat colIndex rowIndex = mat rowIndex colIndex := by
    intro rowIndex colIndex
    have h := congrFun (congrFun hsymm rowIndex) colIndex
    rwa [Matrix.transpose_apply] at h
  have hleft : leftVec ⬝ᵥ (mat *ᵥ rightVec)
      = ∑ rowIndex, ∑ colIndex,
          leftVec rowIndex * (mat rowIndex colIndex * rightVec colIndex) := by
    show (∑ rowIndex, leftVec rowIndex * ∑ colIndex,
        mat rowIndex colIndex * rightVec colIndex) = _
    exact Finset.sum_congr rfl fun rowIndex _ => Finset.mul_sum _ _ _
  have hright : (mat *ᵥ leftVec) ⬝ᵥ rightVec
      = ∑ colIndex, ∑ rowIndex,
          leftVec rowIndex * (mat rowIndex colIndex * rightVec colIndex) := by
    show (∑ colIndex, (∑ rowIndex, mat colIndex rowIndex * leftVec rowIndex)
        * rightVec colIndex) = _
    refine Finset.sum_congr rfl fun colIndex _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun rowIndex _ => ?_
    rw [hentry rowIndex colIndex]
    ring
  rw [hleft, hright, Finset.sum_comm]

/-! ## Layer 1 — the full-carrier kill -/

variable {activeIndex : Type*} {basisCount : ℕ}
variable {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin 6)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin 6 → ℝ)}

/-- **THE FULL-CARRIER ROW LAW.**  When an atom sits in the block of
every basis slot, the read law holds at every basis column, and the
two-sided inverse carries the reading to the whole ambient row: the
chart row at that atom is the shifted weight times the unit row. -/
theorem projection_row_eq_of_full_block
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet)
    {rightInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hright : tightBasisColumns tightDir basisLabel * rightInv = 1)
    {atomIndex : Fin 6}
    (hfull : ∀ slot, atomIndex ∈ activeSubset (basisLabel slot))
    (colIndex : Fin 6) :
    projection atomIndex colIndex
      = (value + weight atomIndex)
        * (1 : Matrix (Fin 6) (Fin 6) ℝ) atomIndex colIndex := by
  classical
  set basisMat := tightBasisColumns tightDir basisLabel with hbasisMat
  have hrow : ∀ slot, (projection * basisMat) atomIndex slot
      = (value + weight atomIndex) * basisMat atomIndex slot := by
    intro slot
    have hprod : (projection * basisMat) atomIndex slot
        = (projection *ᵥ tightDir (basisLabel slot)) atomIndex := by
      rw [Matrix.mul_apply]
      rfl
    rw [hprod, projection_mulVec_tightDir_of_mem hdata (hmemActive slot)
      (hfull slot)]
    rfl
  have hassoc : projection atomIndex colIndex
      = (projection * basisMat * rightInv) atomIndex colIndex := by
    rw [Matrix.mul_assoc, hright, Matrix.mul_one]
  have hexpand : (projection * basisMat * rightInv) atomIndex colIndex
      = (value + weight atomIndex)
        * (basisMat * rightInv) atomIndex colIndex := by
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [hrow slot, mul_assoc]
  rw [hassoc, hexpand, hright]

/-- **THE FULL-CARRIER KILL.**  A stationary datum with a two-sided
basis inverse has no atom that sits in every block, once the shifted
weight of that atom is strictly between zero and one.  The chart row is
concentrated on the diagonal, thus idempotence prices the diagonal
entry as its own square. -/
theorem false_of_full_block_carrier
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet)
    {rightInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hright : tightBasisColumns tightDir basisLabel * rightInv = 1)
    {atomIndex : Fin 6}
    (hfull : ∀ slot, atomIndex ∈ activeSubset (basisLabel slot))
    (hpos : 0 < value + weight atomIndex)
    (hlt : value + weight atomIndex < 1) : False := by
  classical
  have hrow := projection_row_eq_of_full_block hdata hmemActive hright hfull
  have hdiag : projection atomIndex atomIndex = value + weight atomIndex := by
    have h := hrow atomIndex
    rwa [Matrix.one_apply_eq, mul_one] at h
  have hoff : ∀ colIndex, colIndex ≠ atomIndex →
      projection atomIndex colIndex = 0 := by
    intro colIndex hne
    have h := hrow colIndex
    have hzeroOne : (1 : Matrix (Fin 6) (Fin 6) ℝ) atomIndex colIndex = 0 :=
      Matrix.one_apply_ne (Ne.symm hne)
    rwa [hzeroOne, mul_zero] at h
  have hsquare : projection atomIndex atomIndex
      = projection atomIndex atomIndex * projection atomIndex atomIndex := by
    have h := congrFun (congrFun hdata.isIdempotent atomIndex) atomIndex
    rw [Matrix.mul_apply] at h
    have hcollapse : (∑ colIndex : Fin 6,
          projection atomIndex colIndex * projection colIndex atomIndex)
        = projection atomIndex atomIndex * projection atomIndex atomIndex := by
      refine Finset.sum_eq_single atomIndex ?_ ?_
      · intro colIndex _ hne
        rw [hoff colIndex hne, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ atomIndex) hcon
    rw [← hcollapse]
    exact h.symm
  rw [hdiag] at hsquare
  nlinarith [hpos, hlt, hsquare]

/-! ## Layer 2 — the rank-six carrier ceiling -/

/-- The shifted weight of a rank-six frame stays below one: the six
shifted weights are positive and they sum to `6 value + 1`, which is
less than one at a negative value. -/
theorem RankSixFrame.shifted_weight_lt_one {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (atomIndex : Fin 6) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex < 1 := by
  classical
  have hsum : ∑ atom : Fin 6,
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atom)
      = 6 * chartObjective (chartPointOfDesign crux.design) + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, frame.hdata.weight_sum_one, nsmul_eq_mul]
    norm_num
  have hle : (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex)
      ≤ ∑ atom : Fin 6,
        (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight atom) :=
    Finset.single_le_sum
      (f := fun atom : Fin 6 => chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atom)
      (fun atom _ => (frame.shifted_weight_pos atom).le) (Finset.mem_univ atomIndex)
  have hneg := frame.hvalueNeg
  rw [hsum] at hle
  linarith

/-- **NO RANK-SIX ATOM CARRIES EVERY SLOT.**  A full block carrier
forces the shifted weight into `{0, 1}`, and the rank-six window keeps
it strictly inside.  The kill needs no Gram core and no residue. -/
theorem RankSixFrame.blockCarrier_ne_univ {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (atomIndex : Fin 6) :
    blockCarrier frame.activeSubset frame.basisLabel atomIndex ≠ Finset.univ := by
  classical
  intro huniv
  have hfull : ∀ slot : Fin 6, atomIndex ∈ frame.activeSubset (frame.basisLabel slot) := by
    intro slot
    have hmem : slot ∈ blockCarrier frame.activeSubset frame.basisLabel atomIndex := by
      rw [huniv]; exact Finset.mem_univ slot
    exact blockCarrier_mem.mp hmem
  exact false_of_full_block_carrier frame.hdata frame.hmemAll frame.hright hfull
    (frame.shifted_weight_pos atomIndex) (frame.shifted_weight_lt_one atomIndex)

/-- The rank-six carrier ceiling: every block carrier misses a slot. -/
theorem RankSixFrame.blockCarrier_card_le_five {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (atomIndex : Fin 6) :
    (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card ≤ 5 := by
  classical
  have hle : (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card ≤ 6 := by
    have h := Finset.card_le_univ
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex)
    rwa [Fintype.card_fin] at h
  have hne : (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card ≠ 6 := by
    intro heq
    refine frame.blockCarrier_ne_univ atomIndex ?_
    refine Finset.eq_univ_of_card _ ?_
    rw [heq, Fintype.card_fin]
  omega

/-! ## Layer 3 — the degree dichotomy -/

/-- The rank-six degree census: the six block carriers carry eighteen
incidences. -/
theorem RankSixFrame.blockCarrier_card_sum {crux : SixThreeCrux}
    (frame : RankSixFrame crux) :
    ∑ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 18 := by
  have h := blockCarrier_double_count frame.hdata frame.hmemAll (basisLabel := frame.basisLabel)
  norm_num at h
  exact h

/-- Every rank-six block carrier is nonempty. -/
theorem RankSixFrame.blockCarrier_card_pos {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (atomIndex : Fin 6) :
    1 ≤ (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card :=
  Finset.card_pos.mpr (blockCarrier_nonempty frame.hdata frame.hmemAll frame.hspan
    frame.hleft atomIndex)

/-- **THE DEGREE DICHOTOMY.**  Eighteen incidences over six carriers
split every rank-six frame in two.  Either every carrier holds exactly
three slots, or some carrier holds two slots or less.  If no carrier is
small, a carrier of four slots or more pushes the census to nineteen. -/
theorem RankSixFrame.regular_or_light {crux : SixThreeCrux}
    (frame : RankSixFrame crux) :
    (∀ atomIndex : Fin 6,
        (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 3)
      ∨ ∃ atomIndex : Fin 6,
        (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card ≤ 2 := by
  classical
  by_cases hlight : ∃ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card ≤ 2
  · exact Or.inr hlight
  push Not at hlight
  refine Or.inl fun atomIndex => ?_
  by_contra hne
  have hbig : 4 ≤ (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card := by
    have := hlight atomIndex
    omega
  have hsplit : ∑ atom : Fin 6,
        (blockCarrier frame.activeSubset frame.basisLabel atom).card
      = (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card
        + ∑ atom ∈ Finset.univ.erase atomIndex,
            (blockCarrier frame.activeSubset frame.basisLabel atom).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ atomIndex)).symm
  have hcard : (Finset.univ.erase atomIndex).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ atomIndex), Finset.card_univ,
      Fintype.card_fin]
  have hrest : 15 ≤ ∑ atom ∈ Finset.univ.erase atomIndex,
      (blockCarrier frame.activeSubset frame.basisLabel atom).card := by
    have hconst : ∑ _atom ∈ Finset.univ.erase atomIndex, 3 = 15 := by
      rw [Finset.sum_const, hcard]
      norm_num
    rw [← hconst]
    refine Finset.sum_le_sum fun atom _ => ?_
    have := hlight atom
    omega
  have hsum := frame.blockCarrier_card_sum
  omega

/-! ## Layer 4 — the outer zero -/

/-- **THE OUTER ZERO.**  The pair column of a rank-six outer datum has
a tight support of card two inside a block of card three, thus one atom
of that block reads zero on the pair column.  That atom is neither pair
atom. -/
theorem RankSixOuterData.exists_outer_zero_atom {crux : SixThreeCrux}
    (data : RankSixOuterData crux) :
    ∃ zeroAtom : Fin 6,
      zeroAtom ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex)
      ∧ zeroAtom ≠ data.atomU ∧ zeroAtom ≠ data.atomV
      ∧ data.frame.tightDir (data.frame.basisLabel data.columnIndex) zeroAtom = 0 := by
  classical
  have hmem : data.frame.basisLabel data.columnIndex ∈ data.frame.activeSet :=
    data.frame.hmemAll data.columnIndex
  have hsub : datumTightSupport data.frame.tightDir
      (data.frame.basisLabel data.columnIndex)
      ⊆ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) :=
    datumTightSupport_subset data.frame.hdata hmem
  have hblockCard : (data.frame.activeSubset
      (data.frame.basisLabel data.columnIndex)).card = 3 :=
    data.frame.hdata.activeSubset_card _ hmem
  have hlt : (datumTightSupport data.frame.tightDir
        (data.frame.basisLabel data.columnIndex)).card
      < (data.frame.activeSubset (data.frame.basisLabel data.columnIndex)).card := by
    rw [data.hcard, hblockCard]
    norm_num
  have hssub : datumTightSupport data.frame.tightDir
      (data.frame.basisLabel data.columnIndex)
      ⊂ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => by rw [heq] at hlt; omega⟩
  obtain ⟨zeroAtom, hzin, hznot⟩ := Finset.exists_of_ssubset hssub
  have hzero : data.frame.tightDir (data.frame.basisLabel data.columnIndex) zeroAtom = 0 := by
    by_contra hne
    exact hznot (mem_datumTightSupport.mpr hne)
  refine ⟨zeroAtom, hzin, ?_, ?_, hzero⟩
  · intro heq
    exact data.hneU (heq ▸ hzero)
  · intro heq
    exact data.hneV (heq ▸ hzero)

/-- **THE OUTER ZERO CARRIER.**  The outer zero atom carries two slots
at least: the pair column carries it in the block, and the two-sided
inverse keeps its ambient row alive at a second slot. -/
theorem RankSixOuterData.two_le_zero_atom_carrier {crux : SixThreeCrux}
    (data : RankSixOuterData crux) {zeroAtom : Fin 6}
    (hzin : zeroAtom ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex))
    (hzero : data.frame.tightDir (data.frame.basisLabel data.columnIndex) zeroAtom = 0) :
    2 ≤ (blockCarrier data.frame.activeSubset data.frame.basisLabel zeroAtom).card := by
  classical
  have hone : ∑ slot : Fin 6,
      tightBasisColumns data.frame.tightDir data.frame.basisLabel zeroAtom slot
        * data.frame.leftInv slot zeroAtom = 1 := by
    have h := congrFun (congrFun data.frame.hright zeroAtom) zeroAtom
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    exact h
  have hne : ∑ slot : Fin 6,
      tightBasisColumns data.frame.tightDir data.frame.basisLabel zeroAtom slot
        * data.frame.leftInv slot zeroAtom ≠ 0 := by
    rw [hone]; norm_num
  obtain ⟨aliveSlot, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have haliveDir : data.frame.tightDir (data.frame.basisLabel aliveSlot) zeroAtom ≠ 0 := by
    intro hzeroDir
    refine hterm ?_
    have hentry : tightBasisColumns data.frame.tightDir data.frame.basisLabel
        zeroAtom aliveSlot
        = data.frame.tightDir (data.frame.basisLabel aliveSlot) zeroAtom := rfl
    rw [hentry, hzeroDir, zero_mul]
  have haliveMem : aliveSlot ∈ blockCarrier data.frame.activeSubset
      data.frame.basisLabel zeroAtom := by
    rw [blockCarrier_mem]
    by_contra hnot
    exact haliveDir (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll aliveSlot) zeroAtom hnot)
  have hcolMem : data.columnIndex ∈ blockCarrier data.frame.activeSubset
      data.frame.basisLabel zeroAtom := blockCarrier_mem.mpr hzin
  have hdistinct : data.columnIndex ≠ aliveSlot := by
    intro heq
    exact haliveDir (heq ▸ hzero)
  have hlt : 1 < (blockCarrier data.frame.activeSubset
      data.frame.basisLabel zeroAtom).card :=
    Finset.one_lt_card.mpr ⟨data.columnIndex, hcolMem, aliveSlot, haliveMem, hdistinct⟩
  omega

/-- The outer zero atom is never a pin. -/
theorem RankSixOuterData.zero_atom_not_pin {crux : SixThreeCrux}
    (data : RankSixOuterData crux) {zeroAtom : Fin 6}
    (hzin : zeroAtom ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex))
    (hzero : data.frame.tightDir (data.frame.basisLabel data.columnIndex) zeroAtom = 0) :
    zeroAtom ∉ data.frame.pinSet := by
  classical
  intro hpin
  rw [RankSixFrame.pinSet, Finset.mem_filter] at hpin
  have := data.two_le_zero_atom_carrier hzin hzero
  omega

/-- **THE REGULAR DEFICIENCY.**  In the regular stratum the outer zero
atom carries exactly three slots, and it reads zero on one of them.
Thus its tight support inside its own carrier is a proper nonempty
part. -/
theorem RankSixOuterData.regular_zero_atom_deficient {crux : SixThreeCrux}
    (data : RankSixOuterData crux)
    (hregular : ∀ atomIndex : Fin 6,
      (blockCarrier data.frame.activeSubset data.frame.basisLabel atomIndex).card = 3) :
    ∃ zeroAtom : Fin 6, ∃ aliveSlot : Fin 6,
      (blockCarrier data.frame.activeSubset data.frame.basisLabel zeroAtom).card = 3
      ∧ data.columnIndex ∈ blockCarrier data.frame.activeSubset
          data.frame.basisLabel zeroAtom
      ∧ aliveSlot ∈ blockCarrier data.frame.activeSubset
          data.frame.basisLabel zeroAtom
      ∧ data.columnIndex ≠ aliveSlot
      ∧ data.frame.tightDir (data.frame.basisLabel data.columnIndex) zeroAtom = 0
      ∧ data.frame.tightDir (data.frame.basisLabel aliveSlot) zeroAtom ≠ 0 := by
  classical
  obtain ⟨zeroAtom, hzin, _, _, hzero⟩ := data.exists_outer_zero_atom
  have hone : ∑ slot : Fin 6,
      tightBasisColumns data.frame.tightDir data.frame.basisLabel zeroAtom slot
        * data.frame.leftInv slot zeroAtom = 1 := by
    have h := congrFun (congrFun data.frame.hright zeroAtom) zeroAtom
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    exact h
  have hne : ∑ slot : Fin 6,
      tightBasisColumns data.frame.tightDir data.frame.basisLabel zeroAtom slot
        * data.frame.leftInv slot zeroAtom ≠ 0 := by
    rw [hone]; norm_num
  obtain ⟨aliveSlot, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have haliveDir : data.frame.tightDir (data.frame.basisLabel aliveSlot) zeroAtom ≠ 0 := by
    intro hzeroDir
    refine hterm ?_
    have hentry : tightBasisColumns data.frame.tightDir data.frame.basisLabel
        zeroAtom aliveSlot
        = data.frame.tightDir (data.frame.basisLabel aliveSlot) zeroAtom := rfl
    rw [hentry, hzeroDir, zero_mul]
  refine ⟨zeroAtom, aliveSlot, hregular zeroAtom, blockCarrier_mem.mpr hzin, ?_, ?_,
    hzero, haliveDir⟩
  · rw [blockCarrier_mem]
    by_contra hnot
    exact haliveDir (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll aliveSlot) zeroAtom hnot)
  · intro heq
    exact haliveDir (heq ▸ hzero)

/-! ## Layer 5 — the low-profile split -/

/-- **THE REGULAR RESIDUE.**  No rank-six outer datum has every block
carrier of card three. -/
def RankSixOuterRegularClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankSixOuterData crux),
    (∀ atomIndex : Fin 6,
      (blockCarrier data.frame.activeSubset data.frame.basisLabel atomIndex).card = 3) →
    False

/-- **THE THIN RESIDUE.**  No rank-six outer datum has a block carrier
of card two or less together with a pin and pair profile of mass three
or less. -/
def RankSixOuterThinClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankSixOuterData crux) (lightAtom : Fin 6),
    (blockCarrier data.frame.activeSubset data.frame.basisLabel lightAtom).card ≤ 2 →
    2 * data.frame.pinSet.card + data.frame.pairSet.card ≤ 3 →
    False

/-- **THE LOW-PROFILE SPLIT.**  The degree dichotomy splits the
low-profile residue of the column-Gram fold into the regular residue
and the thin residue. -/
theorem rankSixOuterLowProfileClosed_of_regular_and_thin
    (hregular : RankSixOuterRegularClosed) (hthin : RankSixOuterThinClosed) :
    RankSixOuterLowProfileClosed := by
  intro crux data hprofile
  rcases data.frame.regular_or_light with hreg | ⟨lightAtom, hlight⟩
  · exact hregular crux data hreg
  · exact hthin crux data lightAtom hlight hprofile

/-- **THE RANK-SIX KILL FROM THREE RESIDUES.** -/
theorem rankSixOuterKilled_of_circuit_regular_thin
    (hcirc : RankSixOuterCircuitClosed)
    (hregular : RankSixOuterRegularClosed) (hthin : RankSixOuterThinClosed) :
    RankSixOuterKilled :=
  rankSixOuterKilled_of_circuit_and_lowProfile hcirc
    (rankSixOuterLowProfileClosed_of_regular_and_thin hregular hthin)

/-- **THE RANK-SIX DISCHARGE FROM THREE RESIDUES.**  The support-two
closure of the third rung follows from the circuit residue, the regular
residue, and the thin residue. -/
theorem rankSixSupportTwoClosed_of_circuit_regular_thin
    (hcirc : RankSixOuterCircuitClosed)
    (hregular : RankSixOuterRegularClosed) (hthin : RankSixOuterThinClosed) :
    RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_outer_killed
    (rankSixOuterKilled_of_circuit_regular_thin hcirc hregular hthin)

/-! ## Layer 6 — the boundary kernel line -/

variable {slotCount : ℕ} {S : Matrix (Fin slotCount) (Fin slotCount) ℝ}
variable {readVecs : Fin 6 → Fin slotCount → ℝ} {readVal : Fin 6 → ℝ}
variable {car : Fin 6 → Finset (Fin slotCount)}

/-- **THE BOUNDARY KERNEL LAW.**  At a vanished read value the capture
energy of the read vector is zero, and the energy of a symmetric
idempotent is the square norm of the capture.  Thus the read vector
lies WHOLLY in the kernel of the conjugate, at every slot and not only
on its carrier. -/
theorem read_kernel_of_boundary (hsymm : Sᵀ = S) (hidem : S * S = S)
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = readVal atomIndex * readVecs atomIndex slot)
    {atomIndex : Fin 6} (hzero : readVal atomIndex = 0) :
    S *ᵥ readVecs atomIndex = 0 := by
  classical
  have henergy : readVecs atomIndex ⬝ᵥ (S *ᵥ readVecs atomIndex)
      = readVal atomIndex * (readVecs atomIndex ⬝ᵥ readVecs atomIndex) :=
    read_energy_eq hsupp hread atomIndex
  have hfix : S *ᵥ (S *ᵥ readVecs atomIndex) = S *ᵥ readVecs atomIndex := by
    rw [Matrix.mulVec_mulVec, hidem]
  have hquad : (S *ᵥ readVecs atomIndex) ⬝ᵥ (S *ᵥ readVecs atomIndex)
      = readVecs atomIndex ⬝ᵥ (S *ᵥ readVecs atomIndex) := by
    rw [dot_mulVec_comm_of_symm hsymm (S *ᵥ readVecs atomIndex) (readVecs atomIndex),
      hfix]
    exact dotProduct_comm _ _
  rw [henergy, hzero, zero_mul] at hquad
  exact dotProduct_self_eq_zero.mp hquad

/-- The kernel vectors are fixed by the complementary idempotent. -/
theorem kernel_fixed_of_complement {vec : Fin slotCount → ℝ}
    (hkernel : S *ᵥ vec = 0) : (1 - S) *ᵥ vec = vec := by
  rw [Matrix.sub_mulVec, hkernel, Matrix.one_mulVec, sub_zero]

/-- **THE BOUNDARY TRACE FLOOR.**  A family of kernel vectors with
pairwise disjoint carriers and nonzero energies counts below the
kernel dimension of the conjugate.  The complementary idempotent fixes
each vector, and the disjoint carriers make the family Gram diagonal,
thus kernel free. -/
theorem boundary_family_card_le {famCount : ℕ}
    (hsymm : Sᵀ = S) (hidem : S * S = S)
    (family : Fin famCount → Fin slotCount → ℝ)
    (familyCar : Fin famCount → Finset (Fin slotCount))
    (hsuppFamily : ∀ i, ∀ slot ∉ familyCar i, family i slot = 0)
    (hnz : ∀ i, family i ⬝ᵥ family i ≠ 0)
    (hdisj : ∀ i j, i ≠ j → ∀ slot ∈ familyCar i, slot ∉ familyCar j)
    (hkernel : ∀ i, S *ᵥ family i = 0) :
    (famCount : ℝ) ≤ (slotCount : ℝ) - Matrix.trace S := by
  classical
  set comp : Matrix (Fin slotCount) (Fin slotCount) ℝ := 1 - S with hcomp
  have hcompSymm : compᵀ = comp := by
    rw [hcomp, Matrix.transpose_sub, Matrix.transpose_one, hsymm]
  have hcompIdem : comp * comp = comp := by
    rw [hcomp, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  have hcompTrace : Matrix.trace comp = (slotCount : ℝ) - Matrix.trace S := by
    rw [hcomp, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
  have hfix : ∀ i, comp *ᵥ family i = family i := by
    intro i
    rw [hcomp]
    exact kernel_fixed_of_complement (hkernel i)
  have hoffdiag : ∀ i j : Fin famCount, i ≠ j → family i ⬝ᵥ family j = 0 := by
    intro i j hij
    exact disjoint_support_dot (hsuppFamily i) (hsuppFamily j) (hdisj i j hij)
  have hkerFree : ∀ x : Fin famCount → ℝ,
      (Matrix.of fun i j => family i ⬝ᵥ family j) *ᵥ x = 0 → x = 0 := by
    intro x hx
    funext i
    show x i = 0
    have hrow : (∑ j, (family i ⬝ᵥ family j) * x j) = 0 := congrFun hx i
    have hcollapse : (∑ j, (family i ⬝ᵥ family j) * x j)
        = (family i ⬝ᵥ family i) * x i := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _ hji
        rw [hoffdiag i j (Ne.symm hji), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
    rw [hcollapse] at hrow
    rcases mul_eq_zero.mp hrow with hzeroEnergy | hzeroX
    · exact absurd hzeroEnergy (hnz i)
    · exact hzeroX
  have hfloor := trace_floor_of_fixed_family hcompSymm hcompIdem family hfix hkerFree
  rwa [hcompTrace] at hfloor

/-- The boundary family kill: a disjoint-carrier kernel family larger
than the kernel dimension cannot exist. -/
theorem false_of_boundary_disjoint_family {famCount : ℕ}
    (hsymm : Sᵀ = S) (hidem : S * S = S)
    (family : Fin famCount → Fin slotCount → ℝ)
    (familyCar : Fin famCount → Finset (Fin slotCount))
    (hsuppFamily : ∀ i, ∀ slot ∉ familyCar i, family i slot = 0)
    (hnz : ∀ i, family i ⬝ᵥ family i ≠ 0)
    (hdisj : ∀ i j, i ≠ j → ∀ slot ∈ familyCar i, slot ∉ familyCar j)
    (hkernel : ∀ i, S *ᵥ family i = 0)
    (hcount : (slotCount : ℝ) - Matrix.trace S < (famCount : ℝ)) : False :=
  absurd (boundary_family_card_le hsymm hidem family familyCar hsuppFamily hnz
    hdisj hkernel) (not_le.mpr hcount)

/-- **THE TRACE-TWO BOUNDARY CEILING.**  At a conjugate of trace two a
disjoint-carrier boundary family counts below `slotCount - 2`.  The
boundary reads come from the kernel law, thus the ceiling prices the
trace-two branch directly. -/
theorem boundary_family_card_le_of_trace_two {famCount : ℕ}
    (hsymm : Sᵀ = S) (hidem : S * S = S) (htrace : Matrix.trace S = 2)
    (boundaryAtom : Fin famCount → Fin 6)
    (hsupp : ∀ atomIndex, ∀ slot ∉ car atomIndex, readVecs atomIndex slot = 0)
    (hread : ∀ atomIndex, ∀ slot ∈ car atomIndex,
      (S *ᵥ readVecs atomIndex) slot
        = readVal atomIndex * readVecs atomIndex slot)
    (hboundary : ∀ i, readVal (boundaryAtom i) = 0)
    (hnz : ∀ i, readVecs (boundaryAtom i) ⬝ᵥ readVecs (boundaryAtom i) ≠ 0)
    (hdisj : ∀ i j, i ≠ j → ∀ slot ∈ car (boundaryAtom i),
      slot ∉ car (boundaryAtom j)) :
    (famCount : ℝ) ≤ (slotCount : ℝ) - 2 := by
  have hfloor := boundary_family_card_le hsymm hidem
    (fun i => readVecs (boundaryAtom i)) (fun i => car (boundaryAtom i))
    (fun i => hsupp (boundaryAtom i)) hnz hdisj
    (fun i => read_kernel_of_boundary hsymm hidem hsupp hread (hboundary i))
  rwa [htrace] at hfloor

/-! ## Layer 7 — the tight carrier census -/

/-- The TIGHT carrier of an atom: the basis slots whose column is alive
at that atom.  It sits inside the block carrier, and the two-sided
inverse keeps it nonempty. -/
noncomputable def tightCarrier (tightDir : activeIndex → (Fin 6 → ℝ))
    (basisLabel : Fin basisCount → activeIndex) (atomIndex : Fin 6) :
    Finset (Fin basisCount) :=
  Finset.univ.filter fun slot => tightDir (basisLabel slot) atomIndex ≠ 0

/-- The tight carrier membership reading. -/
theorem mem_tightCarrier {basisLabel : Fin basisCount → activeIndex}
    {atomIndex : Fin 6} {slot : Fin basisCount} :
    slot ∈ tightCarrier tightDir basisLabel atomIndex
      ↔ tightDir (basisLabel slot) atomIndex ≠ 0 := by
  rw [tightCarrier, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- The tight carrier sits inside the block carrier. -/
theorem tightCarrier_subset_blockCarrier
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet) (atomIndex : Fin 6) :
    tightCarrier tightDir basisLabel atomIndex
      ⊆ blockCarrier activeSubset basisLabel atomIndex := by
  intro slot hslot
  rw [blockCarrier_mem]
  by_contra hnot
  exact mem_tightCarrier.mp hslot
    (hdata.tightDir_support _ (hmemActive slot) atomIndex hnot)

/-- **THE TIGHT CENSUS.**  The tight carrier cards sum to the tight
support cards of the basis columns.  The count is the same incidence
set read along the two axes. -/
theorem tightCarrier_double_count {basisLabel : Fin basisCount → activeIndex} :
    ∑ atomIndex : Fin 6, (tightCarrier tightDir basisLabel atomIndex).card
      = ∑ slot : Fin basisCount,
          (datumTightSupport tightDir (basisLabel slot)).card := by
  classical
  have hleft : ∑ atomIndex : Fin 6, (tightCarrier tightDir basisLabel atomIndex).card
      = ∑ atomIndex : Fin 6, ∑ slot : Fin basisCount,
          if tightDir (basisLabel slot) atomIndex ≠ 0 then 1 else 0 := by
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [tightCarrier, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hright : ∑ slot : Fin basisCount,
        (datumTightSupport tightDir (basisLabel slot)).card
      = ∑ slot : Fin basisCount, ∑ atomIndex : Fin 6,
          if tightDir (basisLabel slot) atomIndex ≠ 0 then 1 else 0 := by
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [datumTightSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hleft, hright, Finset.sum_comm]

/-- **THE OUTER TIGHT CEILING.**  The pair column of a rank-six outer
datum carries two atoms while every column block carries three, thus
the tight census stops at seventeen. -/
theorem RankSixOuterData.tight_incidence_le_seventeen {crux : SixThreeCrux}
    (data : RankSixOuterData crux) :
    ∑ slot : Fin 6,
      (datumTightSupport data.frame.tightDir
        (data.frame.basisLabel slot)).card ≤ 17 := by
  classical
  have hbound : ∀ slot : Fin 6,
      (datumTightSupport data.frame.tightDir (data.frame.basisLabel slot)).card ≤ 3 := by
    intro slot
    have hsub := datumTightSupport_subset data.frame.hdata (data.frame.hmemAll slot)
    have hcard := data.frame.hdata.activeSubset_card _ (data.frame.hmemAll slot)
    have := Finset.card_le_card hsub
    omega
  have hsplit : ∑ slot : Fin 6,
        (datumTightSupport data.frame.tightDir (data.frame.basisLabel slot)).card
      = (datumTightSupport data.frame.tightDir
          (data.frame.basisLabel data.columnIndex)).card
        + ∑ slot ∈ Finset.univ.erase data.columnIndex,
            (datumTightSupport data.frame.tightDir (data.frame.basisLabel slot)).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ data.columnIndex)).symm
  have hcard : (Finset.univ.erase data.columnIndex).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ data.columnIndex), Finset.card_univ,
      Fintype.card_fin]
  have hrest : ∑ slot ∈ Finset.univ.erase data.columnIndex,
      (datumTightSupport data.frame.tightDir (data.frame.basisLabel slot)).card ≤ 15 := by
    have hconst : ∑ _slot ∈ Finset.univ.erase data.columnIndex, 3 = 15 := by
      rw [Finset.sum_const, hcard]
      norm_num
    rw [← hconst]
    exact Finset.sum_le_sum fun slot _ => hbound slot
  have := data.hcard
  omega

/-- **THE TIGHT DEFICIENCY.**  Some atom of a rank-six outer datum has
a tight carrier strictly inside its block carrier.  The block census is
eighteen and the tight census stops at seventeen. -/
theorem RankSixOuterData.exists_tight_deficient_atom {crux : SixThreeCrux}
    (data : RankSixOuterData crux) :
    ∃ atomIndex : Fin 6,
      (tightCarrier data.frame.tightDir data.frame.basisLabel atomIndex).card
        < (blockCarrier data.frame.activeSubset data.frame.basisLabel atomIndex).card := by
  classical
  by_contra hnot
  push Not at hnot
  have hsubset : ∀ atomIndex : Fin 6,
      (tightCarrier data.frame.tightDir data.frame.basisLabel atomIndex).card
        ≤ (blockCarrier data.frame.activeSubset data.frame.basisLabel atomIndex).card :=
    fun atomIndex => Finset.card_le_card
      (tightCarrier_subset_blockCarrier data.frame.hdata data.frame.hmemAll atomIndex)
  have heq : ∀ atomIndex : Fin 6,
      (tightCarrier data.frame.tightDir data.frame.basisLabel atomIndex).card
        = (blockCarrier data.frame.activeSubset data.frame.basisLabel atomIndex).card := by
    intro atomIndex
    have := hnot atomIndex
    have := hsubset atomIndex
    omega
  have hsumEq : ∑ atomIndex : Fin 6,
        (tightCarrier data.frame.tightDir data.frame.basisLabel atomIndex).card
      = ∑ atomIndex : Fin 6,
        (blockCarrier data.frame.activeSubset data.frame.basisLabel atomIndex).card :=
    Finset.sum_congr rfl fun atomIndex _ => heq atomIndex
  have hblock := data.frame.blockCarrier_card_sum
  have htight := tightCarrier_double_count (tightDir := data.frame.tightDir)
    (basisLabel := data.frame.basisLabel)
  have hceil := data.tight_incidence_le_seventeen
  omega

/-! ## Layer 8 — the pin rigidity of a rank-six frame -/

/-- **THE PIN ROW LAW.**  A pin atom carries one slot only, thus its
ambient row holds one live entry, and the two-sided inverse reads the
row of that slot as the scaled unit row at the pin atom. -/
theorem RankSixFrame.pin_leftInv_row {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {pinAtom pinSlot : Fin 6}
    (hpin : blockCarrier frame.activeSubset frame.basisLabel pinAtom = {pinSlot})
    (colAtom : Fin 6) :
    frame.tightDir (frame.basisLabel pinSlot) pinAtom * frame.leftInv pinSlot colAtom
      = (1 : Matrix (Fin 6) (Fin 6) ℝ) pinAtom colAtom := by
  classical
  have hoffRow : ∀ slot : Fin 6, slot ≠ pinSlot →
      frame.tightDir (frame.basisLabel slot) pinAtom = 0 := by
    intro slot hne
    refine frame.hdata.tightDir_support _ (frame.hmemAll slot) pinAtom ?_
    intro hmem
    have hcarrier : slot ∈ blockCarrier frame.activeSubset frame.basisLabel pinAtom :=
      blockCarrier_mem.mpr hmem
    rw [hpin, Finset.mem_singleton] at hcarrier
    exact hne hcarrier
  have h := congrFun (congrFun frame.hright pinAtom) colAtom
  rw [Matrix.mul_apply] at h
  have hcollapse : (∑ slot : Fin 6,
        tightBasisColumns frame.tightDir frame.basisLabel pinAtom slot
          * frame.leftInv slot colAtom)
      = frame.tightDir (frame.basisLabel pinSlot) pinAtom
        * frame.leftInv pinSlot colAtom := by
    refine Finset.sum_eq_single pinSlot ?_ ?_
    · intro slot _ hne
      have hentry : tightBasisColumns frame.tightDir frame.basisLabel pinAtom slot
          = frame.tightDir (frame.basisLabel slot) pinAtom := rfl
      rw [hentry, hoffRow slot hne, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ pinSlot) hcon
  rw [← hcollapse]
  exact h

/-- The pin scale is alive. -/
theorem RankSixFrame.pin_dir_ne_zero {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {pinAtom pinSlot : Fin 6}
    (hpin : blockCarrier frame.activeSubset frame.basisLabel pinAtom = {pinSlot}) :
    frame.tightDir (frame.basisLabel pinSlot) pinAtom ≠ 0 := by
  intro hzero
  have h := frame.pin_leftInv_row hpin pinAtom
  rw [hzero, zero_mul, Matrix.one_apply_eq] at h
  exact zero_ne_one h

/-- The row of a pin slot in the inverse dies off the pin atom. -/
theorem RankSixFrame.pin_leftInv_off {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {pinAtom pinSlot : Fin 6}
    (hpin : blockCarrier frame.activeSubset frame.basisLabel pinAtom = {pinSlot})
    {colAtom : Fin 6} (hne : colAtom ≠ pinAtom) :
    frame.leftInv pinSlot colAtom = 0 := by
  have h := frame.pin_leftInv_row hpin colAtom
  rw [Matrix.one_apply_ne (Ne.symm hne)] at h
  rcases mul_eq_zero.mp h with hzeroDir | hzeroInv
  · exact absurd hzeroDir (frame.pin_dir_ne_zero hpin)
  · exact hzeroInv

/-- **THE PIN SLOT INJECTION.**  Two pin atoms never share a pin slot:
the inverse row of that slot is concentrated on one atom. -/
theorem RankSixFrame.pin_slot_inj {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {atomOne atomTwo pinSlot : Fin 6}
    (hpinOne : blockCarrier frame.activeSubset frame.basisLabel atomOne = {pinSlot})
    (hpinTwo : blockCarrier frame.activeSubset frame.basisLabel atomTwo = {pinSlot}) :
    atomOne = atomTwo := by
  by_contra hne
  have hzeroInv : frame.leftInv pinSlot atomOne = 0 :=
    frame.pin_leftInv_off hpinTwo hne
  have h := frame.pin_leftInv_row hpinOne atomOne
  rw [hzeroInv, mul_zero, Matrix.one_apply_eq] at h
  exact zero_ne_one h

/-- **THE PIN COEFFICIENT DIAGONAL.**  The coefficient matrix reads the
shifted weight of a pin atom on the diagonal of its pin slot.  The
inverse row of the pin slot is concentrated, and the read law prices
the single surviving entry. -/
theorem RankSixFrame.pin_coeff_diagonal {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {pinAtom pinSlot : Fin 6}
    (hpin : blockCarrier frame.activeSubset frame.basisLabel pinAtom = {pinSlot}) :
    frame.coeff pinSlot pinSlot
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight pinAtom := by
  classical
  have hmemSubset : pinAtom ∈ frame.activeSubset (frame.basisLabel pinSlot) := by
    refine blockCarrier_mem.mp ?_
    rw [hpin]
    exact Finset.mem_singleton_self pinSlot
  have hcoeff : frame.coeff
      = frame.leftInv * ((chartPointOfDesign crux.design).chart
        * tightBasisColumns frame.tightDir frame.basisLabel) := by
    rw [frame.hrepresentation, ← Matrix.mul_assoc, frame.hleft, Matrix.one_mul]
  have hentry := congrFun (congrFun hcoeff pinSlot) pinSlot
  rw [Matrix.mul_apply] at hentry
  have hcollapse : (∑ rowAtom : Fin 6, frame.leftInv pinSlot rowAtom
        * ((chartPointOfDesign crux.design).chart
          * tightBasisColumns frame.tightDir frame.basisLabel) rowAtom pinSlot)
      = frame.leftInv pinSlot pinAtom
        * ((chartPointOfDesign crux.design).chart
          * tightBasisColumns frame.tightDir frame.basisLabel) pinAtom pinSlot := by
    refine Finset.sum_eq_single pinAtom ?_ ?_
    · intro rowAtom _ hne
      rw [frame.pin_leftInv_off hpin hne, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ pinAtom) hcon
  have hread : ((chartPointOfDesign crux.design).chart
        * tightBasisColumns frame.tightDir frame.basisLabel) pinAtom pinSlot
      = (chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight pinAtom)
        * frame.tightDir (frame.basisLabel pinSlot) pinAtom := by
    have hprod : ((chartPointOfDesign crux.design).chart
          * tightBasisColumns frame.tightDir frame.basisLabel) pinAtom pinSlot
        = ((chartPointOfDesign crux.design).chart
          *ᵥ frame.tightDir (frame.basisLabel pinSlot)) pinAtom := by
      rw [Matrix.mul_apply]
      rfl
    rw [hprod, projection_mulVec_tightDir_of_mem frame.hdata
      (frame.hmemAll pinSlot) hmemSubset]
  have hunit := frame.pin_leftInv_row hpin pinAtom
  rw [Matrix.one_apply_eq] at hunit
  rw [hentry, hcollapse, hread]
  linear_combination (chartObjective (chartPointOfDesign crux.design)
    + (chartPointOfDesign crux.design).weight pinAtom) * hunit

/-! ## Layer 9 — the regular stratum is a low-profile stratum -/

/-- In the regular stratum no atom is a pin. -/
theorem RankSixFrame.regular_pinSet_empty {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    (hregular : ∀ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 3) :
    frame.pinSet = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun atomIndex hmem => ?_
  rw [RankSixFrame.pinSet, Finset.mem_filter] at hmem
  have := hregular atomIndex
  omega

/-- In the regular stratum no atom is a pair. -/
theorem RankSixFrame.regular_pairSet_empty {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    (hregular : ∀ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 3) :
    frame.pairSet = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun atomIndex hmem => ?_
  rw [RankSixFrame.pairSet, Finset.mem_filter] at hmem
  have := hregular atomIndex
  omega

/-- **THE FAITHFUL SPLIT.**  The regular stratum carries profile mass
zero, thus it sits inside the low-profile stratum.  The split of the
low-profile residue into the regular residue and the thin residue loses
nothing. -/
theorem RankSixFrame.regular_profile_zero {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    (hregular : ∀ atomIndex : Fin 6,
      (blockCarrier frame.activeSubset frame.basisLabel atomIndex).card = 3) :
    2 * frame.pinSet.card + frame.pairSet.card = 0 := by
  rw [frame.regular_pinSet_empty hregular, frame.regular_pairSet_empty hregular]
  simp

/-- **THE REGULAR RESIDUE IS INSIDE THE LOW-PROFILE RESIDUE.** -/
theorem rankSixOuterRegularClosed_of_lowProfile
    (hlow : RankSixOuterLowProfileClosed) : RankSixOuterRegularClosed := by
  intro crux data hregular
  refine hlow crux data ?_
  rw [data.frame.regular_profile_zero hregular]
  omega

/-! ## Layer 10 — the profile mass floor at every rank -/

/-- The pin set of a basis: the atoms whose block carrier is one slot. -/
def blockPinSet (activeSubset : activeIndex → Finset (Fin 6))
    (basisLabel : Fin basisCount → activeIndex) : Finset (Fin 6) :=
  Finset.univ.filter fun atomIndex =>
    (blockCarrier activeSubset basisLabel atomIndex).card = 1

/-- The pair set of a basis: the atoms whose block carrier is a slot
pair. -/
def blockPairSet (activeSubset : activeIndex → Finset (Fin 6))
    (basisLabel : Fin basisCount → activeIndex) : Finset (Fin 6) :=
  Finset.univ.filter fun atomIndex =>
    (blockCarrier activeSubset basisLabel atomIndex).card = 2

/-- The pin set and the pair set of a basis are disjoint. -/
theorem blockPin_pair_disjoint {basisLabel : Fin basisCount → activeIndex} :
    Disjoint (blockPinSet activeSubset basisLabel)
      (blockPairSet activeSubset basisLabel) := by
  classical
  rw [Finset.disjoint_left]
  intro atomIndex hpin hpair
  rw [blockPinSet, Finset.mem_filter] at hpin
  rw [blockPairSet, Finset.mem_filter] at hpair
  omega

/-- Every pin-set atom carries a singleton block carrier. -/
theorem blockPinSet_singleton {basisLabel : Fin basisCount → activeIndex}
    {atomIndex : Fin 6} (hmem : atomIndex ∈ blockPinSet activeSubset basisLabel) :
    ∃ pinSlot, blockCarrier activeSubset basisLabel atomIndex = {pinSlot} := by
  classical
  rw [blockPinSet, Finset.mem_filter] at hmem
  exact Finset.card_eq_one.mp hmem.2

/-- Every pair-set atom carries a two-slot block carrier. -/
theorem blockPairSet_pair {basisLabel : Fin basisCount → activeIndex}
    {atomIndex : Fin 6} (hmem : atomIndex ∈ blockPairSet activeSubset basisLabel) :
    ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
      blockCarrier activeSubset basisLabel atomIndex = {slotOne, slotTwo} := by
  classical
  rw [blockPairSet, Finset.mem_filter] at hmem
  obtain ⟨slotOne, slotTwo, hne, hset⟩ := Finset.card_eq_two.mp hmem.2
  exact ⟨slotOne, slotTwo, hne, hset⟩

/-- **THE PROFILE MASS FLOOR.**  Eighteen is the mass budget of six
nonempty carriers: each carrier of card one pays two of the deficit and
each carrier of card two pays one, thus `18 ≤ 3 basisCount + 2 p + q`.
At rank four the floor is six, at rank five it is three, and at rank
six it vanishes. -/
theorem blockCarrier_profile_floor
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1) :
    18 ≤ 3 * basisCount
      + 2 * (blockPinSet activeSubset basisLabel).card
      + (blockPairSet activeSubset basisLabel).card := by
  classical
  have hcount : ∀ chosen : Finset (Fin 6),
      (∑ atomIndex : Fin 6, if atomIndex ∈ chosen then 1 else 0) = chosen.card := by
    intro chosen
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact (Finset.card_eq_sum_ones chosen).symm
  have hpoint : ∀ atomIndex : Fin 6,
      3 ≤ (blockCarrier activeSubset basisLabel atomIndex).card
        + 2 * (if atomIndex ∈ blockPinSet activeSubset basisLabel then 1 else 0)
        + (if atomIndex ∈ blockPairSet activeSubset basisLabel then 1 else 0) := by
    intro atomIndex
    have hpos : 1 ≤ (blockCarrier activeSubset basisLabel atomIndex).card :=
      Finset.card_pos.mpr
        (blockCarrier_nonempty hdata hmemActive hspan hleft atomIndex)
    by_cases hone : (blockCarrier activeSubset basisLabel atomIndex).card = 1
    · have hmem : atomIndex ∈ blockPinSet activeSubset basisLabel := by
        rw [blockPinSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ atomIndex, hone⟩
      rw [if_pos hmem, hone]
      omega
    by_cases htwo : (blockCarrier activeSubset basisLabel atomIndex).card = 2
    · have hmem : atomIndex ∈ blockPairSet activeSubset basisLabel := by
        rw [blockPairSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ atomIndex, htwo⟩
      have hnotPin : atomIndex ∉ blockPinSet activeSubset basisLabel := by
        rw [blockPinSet, Finset.mem_filter]
        rintro ⟨-, hcard⟩
        omega
      rw [if_pos hmem, if_neg hnotPin, htwo]
    · omega
  have hsumLe : (18 : ℕ)
      ≤ ∑ atomIndex : Fin 6,
        ((blockCarrier activeSubset basisLabel atomIndex).card
          + 2 * (if atomIndex ∈ blockPinSet activeSubset basisLabel then 1 else 0)
          + (if atomIndex ∈ blockPairSet activeSubset basisLabel then 1 else 0)) := by
    have hconst : ∑ _atomIndex : Fin 6, 3 = 18 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
    rw [← hconst]
    exact Finset.sum_le_sum fun atomIndex _ => hpoint atomIndex
  have hsplit : ∑ atomIndex : Fin 6,
        ((blockCarrier activeSubset basisLabel atomIndex).card
          + 2 * (if atomIndex ∈ blockPinSet activeSubset basisLabel then 1 else 0)
          + (if atomIndex ∈ blockPairSet activeSubset basisLabel then 1 else 0))
      = (∑ atomIndex : Fin 6, (blockCarrier activeSubset basisLabel atomIndex).card)
        + 2 * (blockPinSet activeSubset basisLabel).card
        + (blockPairSet activeSubset basisLabel).card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      hcount (blockPinSet activeSubset basisLabel),
      hcount (blockPairSet activeSubset basisLabel)]
  rw [hsplit, blockCarrier_double_count hdata hmemActive] at hsumLe
  exact hsumLe

/-- **THE RANK-FIVE PROFILE FLOOR.**  Fifteen incidences over six
nonempty carriers force a profile mass of three at least. -/
theorem RankFiveFrame.profile_mass_ge_three {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) :
    3 ≤ 2 * (blockPinSet frame.activeSubset frame.basisLabel).card
      + (blockPairSet frame.activeSubset frame.basisLabel).card := by
  have h := blockCarrier_profile_floor frame.hdata frame.hmemAll frame.hspan
    frame.hleft (basisLabel := frame.basisLabel)
  omega

/-- **THE RANK-FOUR PROFILE FLOOR.**  Twelve incidences over six
nonempty carriers force a profile mass of six at least. -/
theorem RankFourFrame.profile_mass_ge_six {crux : SixThreeCrux}
    (frame : RankFourFrame crux) :
    6 ≤ 2 * (blockPinSet frame.activeSubset frame.basisLabel).card
      + (blockPairSet frame.activeSubset frame.basisLabel).card := by
  have h := blockCarrier_profile_floor frame.hdata frame.hmemAll frame.hspan
    frame.hleft (basisLabel := frame.basisLabel)
  omega

/-- **THE RANK-FIVE TRACE-THREE NARROWING.**  A rank-five frame with a
diagonal Gram core and capture trace three carries profile mass EXACTLY
three.  The floor gives three, the refined kill removes four and more,
and the trace-three interior law supplies the interiority with no
hypothesis. -/
theorem RankFiveFrame.profile_mass_eq_three_of_trace_three {crux : SixThreeCrux}
    (frame : RankFiveFrame crux) {gramDiag : Fin 5 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag)
    (htrace : Matrix.trace frame.coeff = 3) :
    2 * (blockPinSet frame.activeSubset frame.basisLabel).card
      + (blockPairSet frame.activeSubset frame.basisLabel).card = 3 := by
  classical
  have hfloor := frame.profile_mass_ge_three
  by_contra hne
  have hbig : 4 ≤ 2 * (blockPinSet frame.activeSubset frame.basisLabel).card
      + (blockPairSet frame.activeSubset frame.basisLabel).card := by omega
  refine frame.false_of_diagonal_gram_refined hdiag
    (blockPinSet frame.activeSubset frame.basisLabel)
    (blockPairSet frame.activeSubset frame.basisLabel)
    blockPin_pair_disjoint (fun atom hmem => blockPinSet_singleton hmem)
    (fun atom hmem => blockPairSet_pair hmem)
    (fun atom _ _ => frame.shifted_weight_pos_of_trace_three htrace atom)
    (fun htrace2 => absurd (htrace2 ▸ htrace) (by norm_num)) (fun _ => hbig)

/-- **THE RANK-SIX PROFILE CEILING.**  A rank-six frame with a diagonal
Gram core carries profile mass three or less: mass four fires the
refined kill, and the rank-six interior law supplies the interiority.
Thus the low-profile residue is the WHOLE rank-six diagonal-Gram
branch. -/
theorem RankSixFrame.profile_mass_le_three_of_diagonal_gram {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {gramDiag : Fin 6 → ℝ}
    (hdiag : frame.gram = Matrix.diagonal gramDiag) :
    2 * frame.pinSet.card + frame.pairSet.card ≤ 3 := by
  classical
  by_contra hne
  refine frame.false_of_diagonal_gram_refined hdiag frame.pinSet frame.pairSet
    frame.pin_pair_disjoint (fun atom hmem => frame.pinSet_singleton hmem)
    (fun atom hmem => frame.pairSet_pair hmem)
    (fun atom _ _ => frame.shifted_weight_pos atom) (by omega)

end Gtz
