import Gtz.Wave.OuterCircuitPinResidue
import Gtz.Wave.DenseBlockGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The complement null kill — the basis coverage law and the clone lattice

The rank-four outer datum carries a support-two column on a pair of atoms.  A
circuit label whose block carries that pair puts a SECOND assembly direction
inside the same three atoms.  The assembly range has dimension four, thus two
of its dimensions sit inside a three-atom coordinate space, and the projection
of the range onto the complementary three atoms drops below full.  This module
turns that count into an explicit null direction, and then reads the null
direction against the constant assembly diagonal.

The first layer is the BASIS COVERAGE LAW.  The Gram form prices every
assembly entry by the basis rows, and the constant assembly diagonal is not
zero, thus at every atom some basis column is alive.  The law is generic in the
rank and in the basis size, and it consumes no circuit residue.

The second layer is the NULL CONSTRUCTOR.  Three coordinate rows and two basis
rows fill five rows of a six-by-six square, thus the square is singular and
carries a null direction.  The direction vanishes at the three named atoms and
annihilates two basis columns.  The pair column and the wide label supply the
two remaining slots, thus the direction annihilates the WHOLE basis, the
assembly, and every positive label.

The third layer reads the null direction.  A null direction alive at ONE atom
kills the coverage law, thus every null direction is alive at two atoms or
more.  A null direction alive at exactly TWO atoms clones them: the two basis
rows are proportional, the assembly diagonal prices the ratio at plus or minus
one, and the carried row reading equates the two shifted weights.  If the two
carriers exhaust the slots, the clone row is a left eigenvector of the
coefficient matrix, and idempotence puts the shifted weight at zero — the
boundary.

The last layer narrows the residue.  The rank-one circuit residue of the
landed narrowing follows from the complement null residue, and that residue
splits into the clone residue and the triple residue.  The one-atom branch is
DEAD, unconditionally.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.assembly_entry_of_gramForm` — the assembly entry through the basis rows.
* `Gtz.exists_live_basis_slot` — **THE BASIS COVERAGE LAW.**
* `Gtz.assembly_mulVec_eq_zero_of_basis_dot`,
  `Gtz.dot_eq_zero_of_basis_dot_of_mem_positive` — the null direction kills the
  assembly and every positive label.
* `Gtz.exists_offSlot_coordinate_ne_zero` — a circuit label spends a second
  slot.
* `Gtz.exists_complement_null_of_pair_and_wide` — **THE NULL CONSTRUCTOR.**
* `Gtz.false_of_basis_null_singleton` — **THE ONE-ATOM KILL.**
* `Gtz.basis_row_pair_relation`, `Gtz.basis_row_clone_of_pair_null`,
  `Gtz.clone_scale_sq_eq_one` — **THE CLONE LAW.**
* `Gtz.clone_shifted_weight_eq` — the clone atoms carry one shifted weight.
* `Gtz.clone_leak_vanishes_of_carrier`,
  `Gtz.clone_shifted_weight_eq_zero_of_full_carrier` — **THE CLONE BOUNDARY
  LAW.**
* `Gtz.gap_rankOne_offdiag_product` — **THE REAL-ONLY SIGN LAW.**
* `Gtz.RankFourOuterData.exists_complement_null_of_circuit` — the datum
  reading.
* `Gtz.RankFourOuterComplementNullClosed`,
  `Gtz.RankFourOuterCloneClosed`, `Gtz.RankFourOuterTripleNullClosed` — the
  three narrowed residues.
* `Gtz.rankFourOuterComplementNullClosed_of_clone_triple`,
  `Gtz.rankFourOuterRankOneCircuitClosed_of_complementNull` — **THE
  NARROWING.**
* `Gtz.rankFourSupportTwoClosed_of_complement_interior`,
  `Gtz.rankFourSupportTwoClosed_of_clone_triple_interior` — the rank-four
  discharges through the new lattice.
* `Gtz.RankFourOuterData.clone_carrier_inter_nonempty`,
  `Gtz.RankFourOuterData.clone_big_carrier_of_full` — the clone carriers meet,
  thus a full clone carries a three-slot atom.
* `Gtz.RankFourOuterThinCloneClosed`,
  `Gtz.rankFourOuterCloneClosed_of_thin_interior` — **THE FULL CLONE KILL**:
  the interior residue closes the full half of the clone branch.
* `Gtz.rankFourSupportTwoClosed_of_thinClone_triple_interior` — the sharpened
  rank-four discharge.
* `Gtz.shifted_null_row_relation` — the shifted null reading.
* `Gtz.assembly_cross_of_clone` — the clone cross entry of the assembly.
* `Gtz.RankFourFrame.exists_live_slot`, `Gtz.RankFiveFrame.exists_live_slot`,
  `Gtz.RankSixFrame.exists_live_slot` — the coverage law at the three rungs.
* `Gtz.RankFiveFrame.false_of_basis_null_singleton`,
  `Gtz.RankSixFrame.false_of_basis_null_singleton` — the one-atom kill at the
  two other rungs.
* `Gtz.RankFiveFrame.clone_boundary_of_full_carrier`,
  `Gtz.RankSixFrame.clone_boundary_of_full_carrier` — the clone boundary law at
  the two other rungs.
* `Gtz.RankFourOuterData.exists_live_slot_ne_columnIndex`,
  `Gtz.RankFourOuterData.clone_live_slot_ne_columnIndex`,
  `Gtz.RankFourOuterData.clone_full_carrier_meets_pair_block` — the pair slot
  is dead off the pair.

## Vacuity

The datum statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no datum exists.  Layers one thru four hold at every stationary
datum with a chosen basis.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the assembly through the basis rows, and the coverage law -/

section Coverage

variable {size rank basisCount : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE ASSEMBLY ENTRY.**  The Gram form prices every assembly entry by the
two basis rows at the two atoms. -/
theorem assembly_entry_of_gramForm
    {basisLabel : Fin basisCount → activeIndex}
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    (rowAtom colAtom : Fin size) :
    ∑ slotOne : Fin basisCount, ∑ slotTwo : Fin basisCount,
        tightDir (basisLabel slotOne) rowAtom * gram slotOne slotTwo
          * tightDir (basisLabel slotTwo) colAtom
      = chartMultiplierAssembly activeSet activeWeight tightDir rowAtom
          colAtom := by
  rw [← hHform, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tightBasisColumns,
    Finset.sum_mul]
  exact Finset.sum_comm

/-- **THE BASIS COVERAGE LAW.**  The assembly diagonal is the constant
reciprocal of the size, thus it never vanishes, thus at every atom at least one
basis column is alive.  The law consumes no circuit residue and no interiority.
-/
theorem exists_live_basis_slot
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    (atomIndex : Fin size) :
    ∃ slot : Fin basisCount, tightDir (basisLabel slot) atomIndex ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hsize : 0 < size := size_pos_of_isChartStationaryData hdata
  have hentry := assembly_entry_of_gramForm hHform atomIndex atomIndex
  rw [hdata.assembly_diagonal atomIndex] at hentry
  have hzero : ∑ slotOne : Fin basisCount, ∑ slotTwo : Fin basisCount,
      tightDir (basisLabel slotOne) atomIndex * gram slotOne slotTwo
        * tightDir (basisLabel slotTwo) atomIndex = 0 := by
    refine Finset.sum_eq_zero fun slotOne _ => Finset.sum_eq_zero fun slotTwo _ => ?_
    rw [hnone slotOne, zero_mul, zero_mul]
  rw [hzero] at hentry
  have hpos : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  have : (0 : ℝ) < ((size : ℝ))⁻¹ := inv_pos.mpr hpos
  rw [← hentry] at this
  exact lt_irrefl _ this

/-- A null direction of the whole basis annihilates the assembly. -/
theorem assembly_mulVec_eq_zero_of_basis_dot
    {basisLabel : Fin basisCount → activeIndex}
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    {nullVec : Fin size → ℝ}
    (hnull : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) ⬝ᵥ nullVec = 0) :
    chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ nullVec = 0 := by
  classical
  funext rowAtom
  have hentry : (chartMultiplierAssembly activeSet activeWeight tightDir
      *ᵥ nullVec) rowAtom
      = ∑ colAtom : Fin size,
          chartMultiplierAssembly activeSet activeWeight tightDir rowAtom
            colAtom * nullVec colAtom := rfl
  rw [hentry]
  have hrewrite : ∀ colAtom : Fin size,
      chartMultiplierAssembly activeSet activeWeight tightDir rowAtom colAtom
          * nullVec colAtom
        = ∑ slotOne : Fin basisCount, ∑ slotTwo : Fin basisCount,
            tightDir (basisLabel slotOne) rowAtom * gram slotOne slotTwo
              * tightDir (basisLabel slotTwo) colAtom * nullVec colAtom := by
    intro colAtom
    rw [← assembly_entry_of_gramForm hHform rowAtom colAtom, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_mul _ _ _
  rw [Finset.sum_congr rfl fun colAtom _ => hrewrite colAtom]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun slotOne _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun slotTwo _ => ?_
  have hfactor : ∑ colAtom : Fin size,
      tightDir (basisLabel slotOne) rowAtom * gram slotOne slotTwo
        * tightDir (basisLabel slotTwo) colAtom * nullVec colAtom
      = tightDir (basisLabel slotOne) rowAtom * gram slotOne slotTwo
        * (tightDir (basisLabel slotTwo) ⬝ᵥ nullVec) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hfactor, hnull slotTwo, mul_zero]

/-- A null direction of the whole basis is orthogonal to every positive
label. -/
theorem dot_eq_zero_of_basis_dot_of_mem_positive
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {nullVec : Fin size → ℝ}
    (hnull : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) ⬝ᵥ nullVec = 0)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight) :
    tightDir label ⬝ᵥ nullVec = 0 := by
  classical
  have hrep := tightDir_eq_reconstruction_of_mem_positive hdata basisLabel
    hbasisSpan leftInv hleft hmem
  rw [hrep, dotProduct]
  have hstep : ∀ atomIndex : Fin size,
      (tightBasisColumns tightDir basisLabel *ᵥ (leftInv *ᵥ tightDir label))
          atomIndex * nullVec atomIndex
        = ∑ slot : Fin basisCount, (leftInv *ᵥ tightDir label) slot
            * (tightDir (basisLabel slot) atomIndex * nullVec atomIndex) := by
    intro atomIndex
    have hvalue : (tightBasisColumns tightDir basisLabel
        *ᵥ (leftInv *ᵥ tightDir label)) atomIndex
        = ∑ slot : Fin basisCount,
            tightDir (basisLabel slot) atomIndex
              * (leftInv *ᵥ tightDir label) slot := rfl
    rw [hvalue, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex _ => hstep atomIndex, Finset.sum_comm]
  refine Finset.sum_eq_zero fun slot _ => ?_
  have hinner : ∑ atomIndex : Fin size, (leftInv *ᵥ tightDir label) slot
      * (tightDir (basisLabel slot) atomIndex * nullVec atomIndex)
      = (leftInv *ᵥ tightDir label) slot
        * (tightDir (basisLabel slot) ⬝ᵥ nullVec) := by
    rw [dotProduct, Finset.mul_sum]
  rw [hinner, hnull slot, mul_zero]

/-- A circuit label spends a coefficient at a second slot: a label whose
coordinates live at one slot only is a multiple of that basis column. -/
theorem exists_offSlot_coordinate_ne_zero
    (basisLabel : Fin basisCount → activeIndex) {label : activeIndex}
    {coordVec : Fin basisCount → ℝ}
    (hrep : tightDir label
      = tightBasisColumns tightDir basisLabel *ᵥ coordVec)
    (slotPair : Fin basisCount)
    (hcircuit : ∀ (slot : Fin basisCount) (scale : ℝ),
      tightDir label ≠ scale • tightDir (basisLabel slot)) :
    ∃ slotWide : Fin basisCount, slotWide ≠ slotPair ∧ coordVec slotWide ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  refine hcircuit slotPair (coordVec slotPair) ?_
  funext atomIndex
  rw [hrep]
  have hvalue : (tightBasisColumns tightDir basisLabel *ᵥ coordVec) atomIndex
      = ∑ slot : Fin basisCount,
          tightDir (basisLabel slot) atomIndex * coordVec slot := rfl
  rw [hvalue, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single slotPair]
  · exact mul_comm _ _
  · intro slot _ hne
    rw [hnone slot hne, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ slotPair) hmem

end Coverage

/-! ## Layer 2 — the null constructor at six atoms and four slots -/

section Constructor

variable {activeIndex : Type*} {tightDir : activeIndex → (Fin 6 → ℝ)}

/-- **THE NULL CONSTRUCTOR.**  Three coordinate rows and two basis rows fill
five rows of a six-by-six square, thus the square is singular.  The null
direction of the square vanishes at the three named atoms and annihilates the
two named basis columns. -/
theorem exists_complement_null_of_two_slots
    (basisLabel : Fin 4 → activeIndex) (atomU atomV atomS : Fin 6)
    (slotOne slotTwo : Fin 4) :
    ∃ nullVec : Fin 6 → ℝ, nullVec ≠ 0
      ∧ nullVec atomU = 0 ∧ nullVec atomV = 0 ∧ nullVec atomS = 0
      ∧ tightDir (basisLabel slotOne) ⬝ᵥ nullVec = 0
      ∧ tightDir (basisLabel slotTwo) ⬝ᵥ nullVec = 0 := by
  classical
  set square : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of
    ![fun colAtom => if colAtom = atomU then (1 : ℝ) else 0,
      fun colAtom => if colAtom = atomV then (1 : ℝ) else 0,
      fun colAtom => if colAtom = atomS then (1 : ℝ) else 0,
      fun colAtom => tightDir (basisLabel slotOne) colAtom,
      fun colAtom => tightDir (basisLabel slotTwo) colAtom,
      (0 : Fin 6 → ℝ)] with hsquare
  have hdet : square.det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero 5 fun colAtom => by
      simp [hsquare]
  obtain ⟨nullVec, hne, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨nullVec, hne, ?_, ?_, ?_, ?_, ?_⟩
  · have hrow := congrFun hkernel 0
    simpa [hsquare, Matrix.mulVec, dotProduct] using hrow
  · have hrow := congrFun hkernel 1
    simpa [hsquare, Matrix.mulVec, dotProduct] using hrow
  · have hrow := congrFun hkernel 2
    simpa [hsquare, Matrix.mulVec, dotProduct] using hrow
  · have hrow := congrFun hkernel 3
    simpa [hsquare, Matrix.mulVec, dotProduct] using hrow
  · have hrow := congrFun hkernel 4
    simpa [hsquare, Matrix.mulVec, dotProduct] using hrow

/-- **THE COMPLEMENT NULL DIRECTION.**  A pair column supported inside three
atoms, and a wide direction supported inside the same three atoms whose
coordinates are alive at a second slot, force a nonzero direction that vanishes
at the three atoms and annihilates the WHOLE basis. -/
theorem exists_complement_null_of_pair_and_wide
    (basisLabel : Fin 4 → activeIndex) {atomU atomV atomS : Fin 6}
    {slotPair slotWide : Fin 4} (hslotNe : slotWide ≠ slotPair)
    (hpairSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir (basisLabel slotPair) atomIndex = 0)
    {wideDir : Fin 6 → ℝ} {coordVec : Fin 4 → ℝ}
    (hwideSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → wideDir atomIndex = 0)
    (hwideRep : wideDir = tightBasisColumns tightDir basisLabel *ᵥ coordVec)
    (hcoordNe : coordVec slotWide ≠ 0) :
    ∃ nullVec : Fin 6 → ℝ, nullVec ≠ 0
      ∧ nullVec atomU = 0 ∧ nullVec atomV = 0 ∧ nullVec atomS = 0
      ∧ ∀ slot : Fin 4, tightDir (basisLabel slot) ⬝ᵥ nullVec = 0 := by
  classical
  have hcardPair : ({slotPair, slotWide} : Finset (Fin 4)).card = 2 :=
    Finset.card_pair (Ne.symm hslotNe)
  have hcardRest : ((Finset.univ : Finset (Fin 4)) \ {slotPair, slotWide}).card
      = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, hcardPair, Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨restOne, restTwo, hrestNe, hrest⟩ := Finset.card_eq_two.mp hcardRest
  obtain ⟨nullVec, hne, hU, hV, hS, hdotOne, hdotTwo⟩ :=
    exists_complement_null_of_two_slots (tightDir := tightDir) basisLabel
      atomU atomV atomS restOne restTwo
  have hdotPair : tightDir (basisLabel slotPair) ⬝ᵥ nullVec = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero fun atomIndex _ => ?_
    by_cases hUeq : atomIndex = atomU
    · rw [hUeq, hU, mul_zero]
    · by_cases hVeq : atomIndex = atomV
      · rw [hVeq, hV, mul_zero]
      · rw [hpairSupp atomIndex hUeq hVeq, zero_mul]
  have hdotWideDir : wideDir ⬝ᵥ nullVec = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero fun atomIndex _ => ?_
    by_cases hUeq : atomIndex = atomU
    · rw [hUeq, hU, mul_zero]
    · by_cases hVeq : atomIndex = atomV
      · rw [hVeq, hV, mul_zero]
      · by_cases hSeq : atomIndex = atomS
        · rw [hSeq, hS, mul_zero]
        · rw [hwideSupp atomIndex hUeq hVeq hSeq, zero_mul]
  -- The wide dot product expands over the four slots.
  have hexpand : ∑ slot : Fin 4,
      coordVec slot * (tightDir (basisLabel slot) ⬝ᵥ nullVec) = 0 := by
    rw [← hdotWideDir, hwideRep, dotProduct]
    have hstep : ∀ atomIndex : Fin 6,
        (tightBasisColumns tightDir basisLabel *ᵥ coordVec) atomIndex
            * nullVec atomIndex
          = ∑ slot : Fin 4, coordVec slot
              * (tightDir (basisLabel slot) atomIndex * nullVec atomIndex) := by
      intro atomIndex
      have hvalue : (tightBasisColumns tightDir basisLabel *ᵥ coordVec) atomIndex
          = ∑ slot : Fin 4,
              tightDir (basisLabel slot) atomIndex * coordVec slot := rfl
      rw [hvalue, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hstep atomIndex, Finset.sum_comm]
    refine Finset.sum_congr rfl fun slot _ => ?_
    rw [dotProduct, Finset.mul_sum]
  -- Three of the four slot terms vanish, thus the fourth does too.
  have hsplit : ∑ slot ∈ (Finset.univ : Finset (Fin 4)) \ {slotPair, slotWide},
        coordVec slot * (tightDir (basisLabel slot) ⬝ᵥ nullVec)
      + ∑ slot ∈ ({slotPair, slotWide} : Finset (Fin 4)),
        coordVec slot * (tightDir (basisLabel slot) ⬝ᵥ nullVec)
      = ∑ slot : Fin 4,
        coordVec slot * (tightDir (basisLabel slot) ⬝ᵥ nullVec) :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have hrestZero : ∑ slot ∈ (Finset.univ : Finset (Fin 4)) \ {slotPair, slotWide},
      coordVec slot * (tightDir (basisLabel slot) ⬝ᵥ nullVec) = 0 := by
    rw [hrest, Finset.sum_pair hrestNe, hdotOne, hdotTwo, mul_zero, mul_zero,
      add_zero]
  have hpairSum : ∑ slot ∈ ({slotPair, slotWide} : Finset (Fin 4)),
      coordVec slot * (tightDir (basisLabel slot) ⬝ᵥ nullVec)
      = coordVec slotWide * (tightDir (basisLabel slotWide) ⬝ᵥ nullVec) := by
    rw [Finset.sum_pair (Ne.symm hslotNe), hdotPair, mul_zero, zero_add]
  rw [hrestZero, hpairSum, zero_add, hexpand] at hsplit
  have hdotWide : tightDir (basisLabel slotWide) ⬝ᵥ nullVec = 0 :=
    (mul_eq_zero.mp hsplit).resolve_left hcoordNe
  refine ⟨nullVec, hne, hU, hV, hS, fun slot => ?_⟩
  by_cases hPairEq : slot = slotPair
  · rw [hPairEq]; exact hdotPair
  · by_cases hWideEq : slot = slotWide
    · rw [hWideEq]; exact hdotWide
    · have hmemRest : slot ∈ (Finset.univ : Finset (Fin 4)) \ {slotPair, slotWide} := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ slot, ?_⟩
        simp [hPairEq, hWideEq]
      rw [hrest] at hmemRest
      rcases Finset.mem_insert.mp hmemRest with hEq | hEq
      · rw [hEq]; exact hdotOne
      · rw [Finset.mem_singleton.mp hEq]; exact hdotTwo

end Constructor

/-! ## Layer 3 — the one-atom kill and the clone law -/

section CloneLattice

variable {size rank basisCount : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE ONE-ATOM KILL.**  A null direction of the whole basis that is alive
at exactly one atom kills the coverage law at that atom.  The branch dies with
no further hypothesis. -/
theorem false_of_basis_null_singleton
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    {nullVec : Fin size → ℝ} {liveAtom : Fin size}
    (hlive : nullVec liveAtom ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ liveAtom → nullVec atomIndex = 0)
    (hnull : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) ⬝ᵥ nullVec = 0) :
    False := by
  classical
  obtain ⟨slot, hslot⟩ := exists_live_basis_slot hdata hHform liveAtom
  have hsum := hnull slot
  rw [dotProduct, Finset.sum_eq_single liveAtom] at hsum
  · exact hslot ((mul_eq_zero.mp hsum).resolve_right hlive)
  · intro atomIndex _ hne
    rw [hsupp atomIndex hne, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ liveAtom) hmem

/-- The pair relation of a two-atom null direction: at every slot the two live
coordinates of the basis row are tied. -/
theorem basis_row_pair_relation
    {basisLabel : Fin basisCount → activeIndex}
    {nullVec : Fin size → ℝ} {atomOne atomTwo : Fin size}
    (hne : atomOne ≠ atomTwo)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      nullVec atomIndex = 0)
    (hnull : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) ⬝ᵥ nullVec = 0)
    (slot : Fin basisCount) :
    tightDir (basisLabel slot) atomOne * nullVec atomOne
      + tightDir (basisLabel slot) atomTwo * nullVec atomTwo = 0 := by
  classical
  have hsum := hnull slot
  rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ
    ({atomOne, atomTwo} : Finset (Fin size)))] at hsum
  · rwa [Finset.sum_pair hne] at hsum
  · intro atomIndex _ hnotMem
    have hOne : atomIndex ≠ atomOne := by
      intro hEq; exact hnotMem (by rw [hEq]; simp)
    have hTwo : atomIndex ≠ atomTwo := by
      intro hEq; exact hnotMem (by rw [hEq]; simp)
    rw [hsupp atomIndex hOne hTwo, mul_zero]

/-- **THE CLONE LAW.**  A null direction alive at exactly two atoms makes the
two basis rows proportional. -/
theorem basis_row_clone_of_pair_null
    {basisLabel : Fin basisCount → activeIndex}
    {nullVec : Fin size → ℝ} {atomOne atomTwo : Fin size}
    (hne : atomOne ≠ atomTwo) (hliveTwo : nullVec atomTwo ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      nullVec atomIndex = 0)
    (hnull : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) ⬝ᵥ nullVec = 0)
    (slot : Fin basisCount) :
    tightDir (basisLabel slot) atomTwo
      = (-(nullVec atomOne) / nullVec atomTwo)
        * tightDir (basisLabel slot) atomOne := by
  have hrelation := basis_row_pair_relation hne hsupp hnull slot
  field_simp
  linarith [hrelation]

/-- **THE CLONE RATIO.**  The constant assembly diagonal prices the clone
ratio: its square is one. -/
theorem clone_scale_sq_eq_one
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    {atomOne atomTwo : Fin size} {scale : ℝ}
    (hclone : ∀ slot : Fin basisCount, tightDir (basisLabel slot) atomTwo
      = scale * tightDir (basisLabel slot) atomOne) :
    scale * scale = 1 := by
  classical
  have hsize : 0 < size := size_pos_of_isChartStationaryData hdata
  have hpos : (0 : ℝ) < (size : ℝ) := by exact_mod_cast hsize
  have hentryOne := assembly_entry_of_gramForm hHform atomOne atomOne
  have hentryTwo := assembly_entry_of_gramForm hHform atomTwo atomTwo
  rw [hdata.assembly_diagonal atomOne] at hentryOne
  rw [hdata.assembly_diagonal atomTwo] at hentryTwo
  have hscaled : ∑ slotOne : Fin basisCount, ∑ slotTwo : Fin basisCount,
      tightDir (basisLabel slotOne) atomTwo * gram slotOne slotTwo
        * tightDir (basisLabel slotTwo) atomTwo
      = (scale * scale) * ∑ slotOne : Fin basisCount,
          ∑ slotTwo : Fin basisCount,
            tightDir (basisLabel slotOne) atomOne * gram slotOne slotTwo
              * tightDir (basisLabel slotTwo) atomOne := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun slotOne _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun slotTwo _ => ?_
    rw [hclone slotOne, hclone slotTwo]
    ring
  rw [hentryTwo, hentryOne] at hscaled
  have hinvNe : ((size : ℝ))⁻¹ ≠ 0 := by positivity
  field_simp at hscaled
  linarith [hscaled]

/-- **THE CLONE WEIGHT LAW.**  The carried row reading at a live slot equates
the two shifted weights of a clone pair. -/
theorem clone_shifted_weight_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemAll : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomOne atomTwo : Fin size} {scale : ℝ} (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin basisCount, tightDir (basisLabel slot) atomTwo
      = scale * tightDir (basisLabel slot) atomOne)
    {liveSlot : Fin basisCount}
    (hliveNe : tightDir (basisLabel liveSlot) atomOne ≠ 0) :
    value + weight atomOne = value + weight atomTwo := by
  classical
  have hmemOne : atomOne ∈ activeSubset (basisLabel liveSlot) := by
    by_contra hout
    exact hliveNe (hdata.tightDir_support _ (hmemAll liveSlot) atomOne hout)
  have hliveTwoNe : tightDir (basisLabel liveSlot) atomTwo ≠ 0 := by
    rw [hclone liveSlot]
    exact mul_ne_zero hscaleNe hliveNe
  have hmemTwo : atomTwo ∈ activeSubset (basisLabel liveSlot) := by
    by_contra hout
    exact hliveTwoNe (hdata.tightDir_support _ (hmemAll liveSlot) atomTwo hout)
  have hreadOne := carried_row_reading hdata basisLabel hrepresentation
    (hmemAll liveSlot) hmemOne
  have hreadTwo := carried_row_reading hdata basisLabel hrepresentation
    (hmemAll liveSlot) hmemTwo
  have hrowTwo : ∑ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) atomTwo * coeff columnIndex liveSlot
      = scale * ∑ columnIndex : Fin basisCount,
          tightDir (basisLabel columnIndex) atomOne
            * coeff columnIndex liveSlot := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun columnIndex _ => by
      rw [hclone columnIndex]; ring
  rw [hrowTwo, hreadOne, hclone liveSlot] at hreadTwo
  have hcancel : scale * (((value + weight atomOne)
      - (value + weight atomTwo)) * tightDir (basisLabel liveSlot) atomOne)
      = 0 := by linarith [hreadTwo]
  have hinner := (mul_eq_zero.mp hcancel).resolve_left hscaleNe
  have := (mul_eq_zero.mp hinner).resolve_right hliveNe
  linarith

/-- **THE CLONE LEAK LAW.**  The residue of the carried row reading at the
first clone atom vanishes at every slot whose block carries either clone
atom. -/
theorem clone_leak_vanishes_of_carrier
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemAll : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {atomOne atomTwo : Fin size} {scale : ℝ} (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin basisCount, tightDir (basisLabel slot) atomTwo
      = scale * tightDir (basisLabel slot) atomOne)
    (hweight : value + weight atomOne = value + weight atomTwo)
    {slot : Fin basisCount}
    (hcarrier : atomOne ∈ activeSubset (basisLabel slot)
      ∨ atomTwo ∈ activeSubset (basisLabel slot)) :
    ∑ columnIndex : Fin basisCount,
        tightDir (basisLabel columnIndex) atomOne * coeff columnIndex slot
      = (value + weight atomOne) * tightDir (basisLabel slot) atomOne := by
  classical
  rcases hcarrier with hmemOne | hmemTwo
  · exact carried_row_reading hdata basisLabel hrepresentation
      (hmemAll slot) hmemOne
  · have hreadTwo := carried_row_reading hdata basisLabel hrepresentation
      (hmemAll slot) hmemTwo
    have hrowTwo : ∑ columnIndex : Fin basisCount,
        tightDir (basisLabel columnIndex) atomTwo * coeff columnIndex slot
        = scale * ∑ columnIndex : Fin basisCount,
            tightDir (basisLabel columnIndex) atomOne
              * coeff columnIndex slot := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun columnIndex _ => by
        rw [hclone columnIndex]; ring
    rw [hrowTwo, hclone slot, ← hweight] at hreadTwo
    have hcancel : scale * ((∑ columnIndex : Fin basisCount,
          tightDir (basisLabel columnIndex) atomOne * coeff columnIndex slot)
        - (value + weight atomOne) * tightDir (basisLabel slot) atomOne)
        = 0 := by linarith [hreadTwo]
    have := (mul_eq_zero.mp hcancel).resolve_left hscaleNe
    linarith

/-- **THE CLONE BOUNDARY LAW.**  If the two clone carriers exhaust the slots,
the clone row is a left eigenvector of the coefficient matrix.  Idempotence
puts the eigenvalue at zero or one, and the weight window refuses one, thus the
clone atom sits at the boundary of the shifted weight. -/
theorem clone_shifted_weight_eq_zero_of_full_carrier
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir) (hvalueNeg : value < 0)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemAll : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    (hidempotent : coeff * coeff = coeff)
    {atomOne atomTwo : Fin size} {scale : ℝ} (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin basisCount, tightDir (basisLabel slot) atomTwo
      = scale * tightDir (basisLabel slot) atomOne)
    (hweight : value + weight atomOne = value + weight atomTwo)
    (hfull : ∀ slot : Fin basisCount,
      atomOne ∈ activeSubset (basisLabel slot)
        ∨ atomTwo ∈ activeSubset (basisLabel slot))
    {liveSlot : Fin basisCount}
    (hliveNe : tightDir (basisLabel liveSlot) atomOne ≠ 0) :
    value + weight atomOne = 0 := by
  classical
  set shifted : ℝ := value + weight atomOne with hshifted
  have hrow : ∀ slot : Fin basisCount,
      ∑ columnIndex : Fin basisCount,
          tightDir (basisLabel columnIndex) atomOne * coeff columnIndex slot
        = shifted * tightDir (basisLabel slot) atomOne := fun slot =>
    clone_leak_vanishes_of_carrier hdata hmemAll hrepresentation hscaleNe
      hclone hweight (hfull slot)
  -- Apply the reading twice and compare with idempotence.
  have hsquare : ∀ slot : Fin basisCount,
      ∑ columnIndex : Fin basisCount,
          tightDir (basisLabel columnIndex) atomOne
            * (coeff * coeff) columnIndex slot
        = shifted * (shifted * tightDir (basisLabel slot) atomOne) := by
    intro slot
    have hexpand : ∀ columnIndex : Fin basisCount,
        tightDir (basisLabel columnIndex) atomOne
            * (coeff * coeff) columnIndex slot
          = ∑ middleIndex : Fin basisCount,
              tightDir (basisLabel columnIndex) atomOne
                * coeff columnIndex middleIndex * coeff middleIndex slot := by
      intro columnIndex
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Finset.sum_congr rfl fun columnIndex _ => hexpand columnIndex,
      Finset.sum_comm]
    have hinner : ∀ middleIndex : Fin basisCount,
        ∑ columnIndex : Fin basisCount,
            tightDir (basisLabel columnIndex) atomOne
              * coeff columnIndex middleIndex * coeff middleIndex slot
          = shifted * tightDir (basisLabel middleIndex) atomOne
            * coeff middleIndex slot := by
      intro middleIndex
      rw [← Finset.sum_mul, hrow middleIndex]
    rw [Finset.sum_congr rfl fun middleIndex _ => hinner middleIndex]
    have hfactor : ∑ middleIndex : Fin basisCount,
        shifted * tightDir (basisLabel middleIndex) atomOne
          * coeff middleIndex slot
        = shifted * ∑ middleIndex : Fin basisCount,
            tightDir (basisLabel middleIndex) atomOne
              * coeff middleIndex slot := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hfactor, hrow slot]
  have hidemRow := hsquare liveSlot
  rw [hidempotent, hrow liveSlot] at hidemRow
  have hquadratic : (shifted * shifted - shifted)
      * tightDir (basisLabel liveSlot) atomOne = 0 := by
    linarith [hidemRow]
  have hroot := (mul_eq_zero.mp hquadratic).resolve_right hliveNe
  have hlt : shifted < 1 := shifted_weight_lt_one hdata hvalueNeg atomOne
  nlinarith [hroot, hlt]

end CloneLattice

/-! ## Layer 4 — the real-only sign law of a rank-one gap block -/

section SignLaw

variable {size : ℕ}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ}

/-- **THE REAL-ONLY SIGN LAW.**  On a rank-one shifted gap block the product of
the three off-diagonal gap entries equals the product of the three shifted
diagonals.  Over the reals this pins the sign pattern of the block, and it is
one cofactor relation plus one minor relation away from the definition. -/
theorem gap_rankOne_offdiag_product {atomU atomV atomS : Fin size}
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    chartStationaryGap projection weight atomU atomV
        * chartStationaryGap projection weight atomU atomS
        * chartStationaryGap projection weight atomV atomS
      = (chartStationaryGap projection weight atomU atomU - value)
        * (chartStationaryGap projection weight atomV atomV - value)
        * (chartStationaryGap projection weight atomS atomS - value) := by
  have hminor := hshape.2.2.1
  have hcofactor := hshape.2.2.2.1
  linear_combination (-(chartStationaryGap projection weight atomV atomS))
      * hcofactor
    + (chartStationaryGap projection weight atomU atomU - value) * hminor

/-- The three shifted diagonals of a rank-one gap block are positive at an
all-heavy datum with a negative value. -/
theorem gap_rankOne_shifted_diagonal_pos {atomIndex : Fin size}
    (hvalueNeg : value < 0)
    (hfloor : 0 < chartStationaryGap projection weight atomIndex atomIndex) :
    0 < chartStationaryGap projection weight atomIndex atomIndex - value := by
  linarith

/-- **THE POSITIVE OFF-DIAGONAL PRODUCT.**  On a rank-one gap block over an
all-heavy datum the product of the three off-diagonal entries is strictly
positive, thus an even number of them is negative. -/
theorem gap_rankOne_offdiag_product_pos {atomU atomV atomS : Fin size}
    (hvalueNeg : value < 0)
    (hfloorU : 0 < chartStationaryGap projection weight atomU atomU)
    (hfloorV : 0 < chartStationaryGap projection weight atomV atomV)
    (hfloorS : 0 < chartStationaryGap projection weight atomS atomS)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    0 < chartStationaryGap projection weight atomU atomV
        * chartStationaryGap projection weight atomU atomS
        * chartStationaryGap projection weight atomV atomS := by
  rw [gap_rankOne_offdiag_product hshape]
  have hU := gap_rankOne_shifted_diagonal_pos hvalueNeg hfloorU
  have hV := gap_rankOne_shifted_diagonal_pos hvalueNeg hfloorV
  have hS := gap_rankOne_shifted_diagonal_pos hvalueNeg hfloorS
  positivity

end SignLaw

/-! ## Layer 5 — the readings at the rank-four outer datum -/

section OuterReadings

variable {crux : SixThreeCrux}

/-- **THE DATUM NULL DIRECTION.**  A circuit label whose block carries the pair
of a rank-four outer datum puts a second assembly direction inside the block.
The assembly range then leaves a nonzero direction that vanishes on the block
and annihilates the whole basis. -/
theorem RankFourOuterData.exists_complement_null_of_circuit
    (data : RankFourOuterData crux) {label : data.frame.activeIndex}
    {atomS : Fin 6} (hmem : label ∈ data.frame.activeSet)
    (hpos : 0 < data.frame.reducedWeight label)
    (hcircuit : ∀ (slot : Fin 4) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot))
    (hUblock : data.atomU ∈ data.frame.activeSubset label)
    (hVblock : data.atomV ∈ data.frame.activeSubset label)
    (hSblock : atomS ∈ data.frame.activeSubset label)
    (hSU : atomS ≠ data.atomU) (hSV : atomS ≠ data.atomV) :
    ∃ nullVec : Fin 6 → ℝ, nullVec ≠ 0
      ∧ nullVec data.atomU = 0 ∧ nullVec data.atomV = 0 ∧ nullVec atomS = 0
      ∧ ∀ slot : Fin 4,
          data.frame.tightDir (data.frame.basisLabel slot) ⬝ᵥ nullVec = 0 := by
  classical
  have hmemPos : label ∈ positiveActiveSet data.frame.activeSet
      data.frame.reducedWeight := mem_positiveActiveSet.mpr ⟨hmem, hpos⟩
  have hrep := tightDir_eq_reconstruction_of_mem_positive data.frame.hdata
    data.frame.basisLabel data.frame.hspan data.frame.leftInv data.frame.hleft
    hmemPos
  obtain ⟨slotWide, hslotNe, hcoordNe⟩ :=
    exists_offSlot_coordinate_ne_zero data.frame.basisLabel hrep
      data.columnIndex hcircuit
  -- The label is supported inside its own block, which is exactly the three
  -- named atoms.
  have hcard := data.frame.hdata.activeSubset_card label hmem
  have hblock : data.frame.activeSubset label
      = {data.atomU, data.atomV, atomS} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro atomIndex hmemAtom
      rcases Finset.mem_insert.mp hmemAtom with hEq | hrest
      · rw [hEq]; exact hUblock
      · rcases Finset.mem_insert.mp hrest with hEq | hEq
        · rw [hEq]; exact hVblock
        · rw [Finset.mem_singleton.mp hEq]; exact hSblock
    · rw [hcard]
      have : ({data.atomU, data.atomV, atomS} : Finset (Fin 6)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
        · simp
        · simp [Ne.symm hSV]
        · simp [data.hUV, Ne.symm hSU]
      omega
  have hwideSupp : ∀ atomIndex, atomIndex ≠ data.atomU →
      atomIndex ≠ data.atomV → atomIndex ≠ atomS →
      data.frame.tightDir label atomIndex = 0 := by
    intro atomIndex hU hV hS
    refine data.frame.hdata.tightDir_support label hmem atomIndex ?_
    rw [hblock]
    simp [hU, hV, hS]
  exact exists_complement_null_of_pair_and_wide data.frame.basisLabel hslotNe
    data.hsupp hwideSupp hrep hcoordNe

/-- The rank-four outer datum reads its own assembly through the Gram form. -/
theorem RankFourOuterData.exists_live_slot (data : RankFourOuterData crux)
    (atomIndex : Fin 6) :
    ∃ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomIndex ≠ 0 :=
  exists_live_basis_slot data.frame.hdata data.frame.hHform atomIndex

end OuterReadings

/-! ## Layer 6 — the three narrowed residues and the narrowing -/

/-- **THE COMPLEMENT NULL RESIDUE.**  A nonzero direction that vanishes at the
pair and at a third atom, and that annihilates the whole basis, dies.  The
residue carries NO circuit label, NO gap block and NO rank-one shape. -/
def RankFourOuterComplementNullClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux) (atomS : Fin 6)
    (nullVec : Fin 6 → ℝ),
    atomS ≠ data.atomU → atomS ≠ data.atomV →
    nullVec ≠ 0 →
    nullVec data.atomU = 0 → nullVec data.atomV = 0 → nullVec atomS = 0 →
    (∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) ⬝ᵥ nullVec = 0) →
    False

/-- **THE CLONE RESIDUE.**  Two atoms whose basis rows agree up to a sign, and
whose weights agree, die. -/
def RankFourOuterCloneClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (atomOne atomTwo : Fin 6) (scale : ℝ),
    atomOne ≠ atomTwo →
    atomOne ≠ data.atomU → atomOne ≠ data.atomV →
    atomTwo ≠ data.atomU → atomTwo ≠ data.atomV →
    (scale = 1 ∨ scale = -1) →
    (∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne) →
    (chartPointOfDesign crux.design).weight atomOne
      = (chartPointOfDesign crux.design).weight atomTwo →
    False

/-- **THE TRIPLE NULL RESIDUE.**  A basis null direction alive at exactly three
atoms dies. -/
def RankFourOuterTripleNullClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (nullVec : Fin 6 → ℝ) (atomOne atomTwo atomThree : Fin 6),
    atomOne ≠ atomTwo → atomOne ≠ atomThree → atomTwo ≠ atomThree →
    atomOne ≠ data.atomU → atomOne ≠ data.atomV →
    atomTwo ≠ data.atomU → atomTwo ≠ data.atomV →
    atomThree ≠ data.atomU → atomThree ≠ data.atomV →
    nullVec atomOne ≠ 0 → nullVec atomTwo ≠ 0 → nullVec atomThree ≠ 0 →
    (∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
      atomIndex ≠ atomThree → nullVec atomIndex = 0) →
    (∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) ⬝ᵥ nullVec = 0) →
    False

/-- **THE LIVE-SET DISPATCH.**  A nonzero basis null direction that vanishes at
three named atoms is alive at one, two or three of the remaining atoms.  The
one-atom branch dies at the coverage law, the two-atom branch delivers a clone
pair, and the three-atom branch is the triple residue. -/
theorem rankFourOuterComplementNullClosed_of_clone_triple
    (hclone : RankFourOuterCloneClosed)
    (htriple : RankFourOuterTripleNullClosed) :
    RankFourOuterComplementNullClosed := by
  classical
  intro crux data atomS nullVec hSU hSV hne hU hV hS hnull
  set live : Finset (Fin 6) :=
    Finset.univ.filter fun atomIndex => nullVec atomIndex ≠ 0 with hlive
  have hmemLive : ∀ atomIndex : Fin 6,
      atomIndex ∈ live ↔ nullVec atomIndex ≠ 0 := by
    intro atomIndex
    rw [hlive, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ atomIndex, h⟩⟩
  have hsubset : live ⊆ (Finset.univ : Finset (Fin 6))
      \ {data.atomU, data.atomV, atomS} := by
    intro atomIndex hmemAtom
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ atomIndex, ?_⟩
    intro hbad
    have hzero : nullVec atomIndex = 0 := by
      rcases Finset.mem_insert.mp hbad with hEq | hrest
      · rw [hEq]; exact hU
      · rcases Finset.mem_insert.mp hrest with hEq | hEq
        · rw [hEq]; exact hV
        · rw [Finset.mem_singleton.mp hEq]; exact hS
    exact ((hmemLive atomIndex).mp hmemAtom) hzero
  have hexclude : ∀ atomIndex : Fin 6, atomIndex ∈ live →
      atomIndex ≠ data.atomU ∧ atomIndex ≠ data.atomV := by
    intro atomIndex hmemAtom
    have hmemSdiff := hsubset hmemAtom
    have hnotTriple := (Finset.mem_sdiff.mp hmemSdiff).2
    constructor
    · intro hEq
      exact hnotTriple (by rw [hEq]; simp)
    · intro hEq
      exact hnotTriple (by rw [hEq]; simp)
  have hcardTriple : ({data.atomU, data.atomV, atomS} : Finset (Fin 6)).card
      = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
    · simp
    · simp [Ne.symm hSV]
    · simp [data.hUV, Ne.symm hSU]
  have hcardBound : live.card ≤ 3 := by
    have hle := Finset.card_le_card hsubset
    rw [Finset.card_sdiff, Finset.inter_univ, hcardTriple, Finset.card_univ,
      Fintype.card_fin] at hle
    simpa using hle
  have hnonempty : live.Nonempty := by
    by_contra hempty
    refine hne ?_
    funext atomIndex
    simp only [Pi.zero_apply]
    by_contra hbad
    exact hempty ⟨atomIndex, (hmemLive atomIndex).mpr hbad⟩
  have hcardPos : 1 ≤ live.card := Finset.card_pos.mpr hnonempty
  have hcases : live.card = 1 ∨ live.card = 2 ∨ live.card = 3 := by omega
  rcases hcases with hcard | hcard | hcard
  · -- One live atom: the coverage law kills it.
    obtain ⟨liveAtom, hliveEq⟩ := Finset.card_eq_one.mp hcard
    have hliveNe : nullVec liveAtom ≠ 0 :=
      (hmemLive liveAtom).mp (by rw [hliveEq]; simp)
    refine false_of_basis_null_singleton data.frame.hdata data.frame.hHform
      hliveNe ?_ hnull
    intro atomIndex hneAtom
    by_contra hbad
    have := (hmemLive atomIndex).mpr hbad
    rw [hliveEq, Finset.mem_singleton] at this
    exact hneAtom this
  · -- Two live atoms: the clone law applies.
    obtain ⟨atomOne, atomTwo, hneAtoms, hliveEq⟩ := Finset.card_eq_two.mp hcard
    have hmemOne : atomOne ∈ live := by rw [hliveEq]; simp
    have hmemTwo : atomTwo ∈ live := by rw [hliveEq]; simp
    obtain ⟨hOneU, hOneV⟩ := hexclude atomOne hmemOne
    obtain ⟨hTwoU, hTwoV⟩ := hexclude atomTwo hmemTwo
    have hliveOne : nullVec atomOne ≠ 0 := (hmemLive atomOne).mp hmemOne
    have hliveTwo : nullVec atomTwo ≠ 0 := (hmemLive atomTwo).mp hmemTwo
    have hsupp : ∀ atomIndex, atomIndex ≠ atomOne → atomIndex ≠ atomTwo →
        nullVec atomIndex = 0 := by
      intro atomIndex hOne hTwo
      by_contra hbad
      have := (hmemLive atomIndex).mpr hbad
      rw [hliveEq] at this
      rcases Finset.mem_insert.mp this with hEq | hEq
      · exact hOne hEq
      · exact hTwo (Finset.mem_singleton.mp hEq)
    set scale : ℝ := -(nullVec atomOne) / nullVec atomTwo with hscale
    have hcloneRow : ∀ slot : Fin 4,
        data.frame.tightDir (data.frame.basisLabel slot) atomTwo
          = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne :=
      fun slot => basis_row_clone_of_pair_null hneAtoms hliveTwo hsupp hnull slot
    have hsq : scale * scale = 1 :=
      clone_scale_sq_eq_one data.frame.hdata data.frame.hHform hcloneRow
    have hscaleNe : scale ≠ 0 := by
      intro hzero
      rw [hzero] at hsq
      norm_num at hsq
    obtain ⟨liveSlot, hliveSlot⟩ := data.exists_live_slot atomOne
    have hweight := clone_shifted_weight_eq data.frame.hdata
      data.frame.hmemAll data.frame.hrepresentation hscaleNe hcloneRow
      hliveSlot
    refine hclone crux data atomOne atomTwo scale hneAtoms hOneU hOneV hTwoU
      hTwoV ?_ hcloneRow ?_
    · rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact Or.inl h
      · exact Or.inr h
    · linarith [hweight]
  · -- Three live atoms: the triple residue.
    obtain ⟨atomOne, atomTwo, atomThree, hOneTwo, hOneThree, hTwoThree,
      hliveEq⟩ := Finset.card_eq_three.mp hcard
    have hmemOne : atomOne ∈ live := by rw [hliveEq]; simp
    have hmemTwo : atomTwo ∈ live := by rw [hliveEq]; simp
    have hmemThree : atomThree ∈ live := by rw [hliveEq]; simp
    obtain ⟨hOneU, hOneV⟩ := hexclude atomOne hmemOne
    obtain ⟨hTwoU, hTwoV⟩ := hexclude atomTwo hmemTwo
    obtain ⟨hThreeU, hThreeV⟩ := hexclude atomThree hmemThree
    have hliveOne : nullVec atomOne ≠ 0 := (hmemLive atomOne).mp hmemOne
    have hliveTwo : nullVec atomTwo ≠ 0 := (hmemLive atomTwo).mp hmemTwo
    have hliveThree : nullVec atomThree ≠ 0 := (hmemLive atomThree).mp hmemThree
    refine htriple crux data nullVec atomOne atomTwo atomThree hOneTwo
      hOneThree hTwoThree hOneU hOneV hTwoU hTwoV hThreeU hThreeV hliveOne
      hliveTwo hliveThree ?_ hnull
    intro atomIndex hOne hTwo hThree
    by_contra hbad
    have := (hmemLive atomIndex).mpr hbad
    rw [hliveEq] at this
    rcases Finset.mem_insert.mp this with hEq | hrest
    · exact hOne hEq
    · rcases Finset.mem_insert.mp hrest with hEq | hEq
      · exact hTwo hEq
      · exact hThree (Finset.mem_singleton.mp hEq)

/-- **THE RANK-ONE NARROWING.**  The complement null residue closes the
rank-one circuit residue of the landed narrowing. -/
theorem rankFourOuterRankOneCircuitClosed_of_complementNull
    (hcomplement : RankFourOuterComplementNullClosed) :
    RankFourOuterRankOneCircuitClosed := by
  intro crux data label atomS hmem hpos hcircuit hUblock hVblock hSU hSV
    hSblock _halive _hshape
  obtain ⟨nullVec, hne, hU, hV, hS, hnull⟩ :=
    data.exists_complement_null_of_circuit hmem hpos hcircuit hUblock hVblock
      hSblock hSU hSV
  exact hcomplement crux data atomS nullVec hSU hSV hne hU hV hS hnull

/-- **THE RANK-FOUR DISCHARGE THROUGH THE COMPLEMENT.**  Closure one of the
rank-four rung follows from the off-pair residue, the complement null residue
and the interior residue. -/
theorem rankFourSupportTwoClosed_of_complement_interior
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hcomplement : RankFourOuterComplementNullClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_narrowed_interior hoff
    (rankFourOuterRankOneCircuitClosed_of_complementNull hcomplement) hinterior

/-- **THE RANK-FOUR DISCHARGE THROUGH THE CLONE LATTICE.**  Closure one of the
rank-four rung follows from the off-pair residue, the clone residue, the triple
residue and the interior residue. -/
theorem rankFourSupportTwoClosed_of_clone_triple_interior
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hclone : RankFourOuterCloneClosed)
    (htriple : RankFourOuterTripleNullClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_complement_interior hoff
    (rankFourOuterComplementNullClosed_of_clone_triple hclone htriple) hinterior

/-! ## Layer 7 — the clone carriers and the boundary kill of the full clone -/

section CloneCarriers

variable {crux : SixThreeCrux}

/-- The null direction of a datum annihilates the assembly itself. -/
theorem RankFourOuterData.assembly_mulVec_eq_zero_of_null
    (data : RankFourOuterData crux) {nullVec : Fin 6 → ℝ}
    (hnull : ∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) ⬝ᵥ nullVec = 0) :
    chartMultiplierAssembly data.frame.activeSet data.frame.reducedWeight
        data.frame.tightDir *ᵥ nullVec = 0 :=
  assembly_mulVec_eq_zero_of_basis_dot data.frame.hHform hnull

/-- The null direction of a datum is orthogonal to EVERY positive label, not
only to the basis. -/
theorem RankFourOuterData.positive_dot_eq_zero_of_null
    (data : RankFourOuterData crux) {nullVec : Fin 6 → ℝ}
    (hnull : ∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) ⬝ᵥ nullVec = 0)
    {label : data.frame.activeIndex} (hmem : label ∈ data.frame.activeSet)
    (hpos : 0 < data.frame.reducedWeight label) :
    data.frame.tightDir label ⬝ᵥ nullVec = 0 :=
  dot_eq_zero_of_basis_dot_of_mem_positive data.frame.hdata
    data.frame.basisLabel data.frame.hspan data.frame.leftInv data.frame.hleft
    hnull (mem_positiveActiveSet.mpr ⟨hmem, hpos⟩)

/-- **THE CLONE CARRIERS MEET.**  A clone pair shares a live slot, thus the two
block carriers intersect. -/
theorem RankFourOuterData.clone_carrier_inter_nonempty
    (data : RankFourOuterData crux) {atomOne atomTwo : Fin 6} {scale : ℝ}
    (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne) :
    (blockCarrier data.frame.activeSubset data.frame.basisLabel atomOne
      ∩ blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomTwo).Nonempty := by
  classical
  obtain ⟨liveSlot, hliveSlot⟩ := data.exists_live_slot atomOne
  have hliveTwo : data.frame.tightDir (data.frame.basisLabel liveSlot) atomTwo
      ≠ 0 := by
    rw [hclone liveSlot]
    exact mul_ne_zero hscaleNe hliveSlot
  refine ⟨liveSlot, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · refine blockCarrier_mem.mpr ?_
    by_contra hout
    exact hliveSlot (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll liveSlot) atomOne hout)
  · refine blockCarrier_mem.mpr ?_
    by_contra hout
    exact hliveTwo (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll liveSlot) atomTwo hout)

/-- **THE FULL CLONE CARRIES A BIG ATOM.**  If the two clone carriers exhaust
the four slots, then they meet, thus their cards sum above four, thus one of
the two atoms carries three slots or more. -/
theorem RankFourOuterData.clone_big_carrier_of_full
    (data : RankFourOuterData crux) {atomOne atomTwo : Fin 6} {scale : ℝ}
    (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne)
    (hfull : ∀ slot : Fin 4,
      atomOne ∈ data.frame.activeSubset (data.frame.basisLabel slot)
        ∨ atomTwo ∈ data.frame.activeSubset (data.frame.basisLabel slot)) :
    2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomOne).card
      ∨ 2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomTwo).card := by
  classical
  set carrierOne := blockCarrier data.frame.activeSubset data.frame.basisLabel
    atomOne with hcarrierOne
  set carrierTwo := blockCarrier data.frame.activeSubset data.frame.basisLabel
    atomTwo with hcarrierTwo
  have hunion : carrierOne ∪ carrierTwo = (Finset.univ : Finset (Fin 4)) := by
    refine Finset.eq_univ_iff_forall.mpr fun slot => ?_
    rcases hfull slot with hmemOne | hmemTwo
    · exact Finset.mem_union_left _ (blockCarrier_mem.mpr hmemOne)
    · exact Finset.mem_union_right _ (blockCarrier_mem.mpr hmemTwo)
  have hinter := data.clone_carrier_inter_nonempty hscaleNe hclone
  have hinterCard : 1 ≤ (carrierOne ∩ carrierTwo).card :=
    Finset.card_pos.mpr hinter
  have hcount := Finset.card_union_add_card_inter carrierOne carrierTwo
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hcount
  omega

end CloneCarriers

/-! ## Layer 8 — the thin clone residue and the sharpened discharge -/

/-- **THE THIN CLONE RESIDUE.**  A clone pair whose two carriers leave one slot
free dies.  The full clone pair needs no residue: the boundary law and the
interior residue close it. -/
def RankFourOuterThinCloneClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (atomOne atomTwo : Fin 6) (scale : ℝ) (freeSlot : Fin 4),
    atomOne ≠ atomTwo →
    atomOne ≠ data.atomU → atomOne ≠ data.atomV →
    atomTwo ≠ data.atomU → atomTwo ≠ data.atomV →
    (scale = 1 ∨ scale = -1) →
    (∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne) →
    (chartPointOfDesign crux.design).weight atomOne
      = (chartPointOfDesign crux.design).weight atomTwo →
    atomOne ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot) →
    atomTwo ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot) →
    False

/-- **THE FULL CLONE KILL.**  A clone pair whose carriers exhaust the slots
puts its shifted weight at zero through idempotence, and puts three slots or
more on one of the two atoms.  The interior residue refuses that pair, thus the
clone residue reduces to its THIN half. -/
theorem rankFourOuterCloneClosed_of_thin_interior
    (hthin : RankFourOuterThinCloneClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourOuterCloneClosed := by
  classical
  intro crux data atomOne atomTwo scale hneAtoms hOneU hOneV hTwoU hTwoV
    hscaleUnit hclone hweight
  by_cases hfree : ∃ freeSlot : Fin 4,
      atomOne ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot)
        ∧ atomTwo ∉ data.frame.activeSubset (data.frame.basisLabel freeSlot)
  · obtain ⟨freeSlot, hone, htwo⟩ := hfree
    exact hthin crux data atomOne atomTwo scale freeSlot hneAtoms hOneU hOneV
      hTwoU hTwoV hscaleUnit hclone hweight hone htwo
  · push Not at hfree
    have hfull : ∀ slot : Fin 4,
        atomOne ∈ data.frame.activeSubset (data.frame.basisLabel slot)
          ∨ atomTwo ∈ data.frame.activeSubset (data.frame.basisLabel slot) := by
      intro slot
      by_cases hone : atomOne ∈ data.frame.activeSubset
        (data.frame.basisLabel slot)
      · exact Or.inl hone
      · exact Or.inr (hfree slot hone)
    have hscaleNe : scale ≠ 0 := by
      rcases hscaleUnit with hEq | hEq <;> rw [hEq] <;> norm_num
    obtain ⟨liveSlot, hliveSlot⟩ := data.exists_live_slot atomOne
    have hshiftedWeight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo := by
      rw [hweight]
    have hboundary := clone_shifted_weight_eq_zero_of_full_carrier
      data.frame.hdata data.frame.hvalueNeg data.frame.hmemAll
      data.frame.hrepresentation data.frame.hidempotent hscaleNe hclone
      hshiftedWeight hfull hliveSlot
    rcases data.clone_big_carrier_of_full hscaleNe hclone hfull with
      hbig | hbig
    · have := hinterior crux data atomOne hbig
      linarith [hboundary]
    · have := hinterior crux data atomTwo hbig
      linarith [hboundary, hshiftedWeight]

/-- **THE RANK-FOUR DISCHARGE THROUGH THE THIN LATTICE.**  Closure one of the
rank-four rung follows from the off-pair residue, the THIN clone residue, the
triple residue and the interior residue.  The full clone branch is gone. -/
theorem rankFourSupportTwoClosed_of_thinClone_triple_interior
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hthin : RankFourOuterThinCloneClosed)
    (htriple : RankFourOuterTripleNullClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_clone_triple_interior hoff
    (rankFourOuterCloneClosed_of_thin_interior hthin hinterior) htriple
    hinterior

/-! ## Layer 9 — the shifted null reading and the three-rung frame supply -/

section ShiftedReading

variable {size rank basisCount : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE SHIFTED NULL READING.**  A basis null direction whose live atoms all
sit in one block reads that block twice: once against the basis column, and
once against the SHIFTED WEIGHTS.  The second reading is the carried row law
transported through the null relation. -/
theorem shifted_null_row_relation
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hmemAll : ∀ slot : Fin basisCount, basisLabel slot ∈ activeSet)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {nullVec : Fin size → ℝ}
    (hnull : ∀ slot : Fin basisCount,
      tightDir (basisLabel slot) ⬝ᵥ nullVec = 0)
    {slot : Fin basisCount}
    (hcarry : ∀ atomIndex : Fin size, nullVec atomIndex ≠ 0 →
      atomIndex ∈ activeSubset (basisLabel slot)) :
    ∑ atomIndex : Fin size, nullVec atomIndex
        * ((value + weight atomIndex) * tightDir (basisLabel slot) atomIndex)
      = 0 := by
  classical
  have hswap : ∑ atomIndex : Fin size, nullVec atomIndex
      * ∑ columnIndex : Fin basisCount,
          tightDir (basisLabel columnIndex) atomIndex * coeff columnIndex slot
      = 0 := by
    have hexpand : ∀ atomIndex : Fin size, nullVec atomIndex
        * ∑ columnIndex : Fin basisCount,
            tightDir (basisLabel columnIndex) atomIndex * coeff columnIndex slot
        = ∑ columnIndex : Fin basisCount, coeff columnIndex slot
            * (tightDir (basisLabel columnIndex) atomIndex
              * nullVec atomIndex) := by
      intro atomIndex
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Finset.sum_congr rfl fun atomIndex _ => hexpand atomIndex,
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun columnIndex _ => ?_
    have hinner : ∑ atomIndex : Fin size, coeff columnIndex slot
        * (tightDir (basisLabel columnIndex) atomIndex * nullVec atomIndex)
        = coeff columnIndex slot
          * (tightDir (basisLabel columnIndex) ⬝ᵥ nullVec) := by
      rw [dotProduct, Finset.mul_sum]
    rw [hinner, hnull columnIndex, mul_zero]
  rw [← hswap]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  by_cases hlive : nullVec atomIndex = 0
  · rw [hlive, zero_mul, zero_mul]
  · rw [carried_row_reading hdata basisLabel hrepresentation (hmemAll slot)
      (hcarry atomIndex hlive)]

/-- **THE ASSEMBLY CROSS ENTRY OF A CLONE PAIR.**  The clone ratio prices the
off-diagonal assembly entry of a clone pair by the constant diagonal. -/
theorem assembly_cross_of_clone
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    {gram : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir)
    {atomOne atomTwo : Fin size} {scale : ℝ}
    (hclone : ∀ slot : Fin basisCount, tightDir (basisLabel slot) atomTwo
      = scale * tightDir (basisLabel slot) atomOne) :
    chartMultiplierAssembly activeSet activeWeight tightDir atomOne atomTwo
      = scale * ((size : ℝ))⁻¹ := by
  classical
  have hentryCross := assembly_entry_of_gramForm hHform atomOne atomTwo
  have hentryDiag := assembly_entry_of_gramForm hHform atomOne atomOne
  rw [hdata.assembly_diagonal atomOne] at hentryDiag
  have hscaled : ∑ slotOne : Fin basisCount, ∑ slotTwo : Fin basisCount,
      tightDir (basisLabel slotOne) atomOne * gram slotOne slotTwo
        * tightDir (basisLabel slotTwo) atomTwo
      = scale * ∑ slotOne : Fin basisCount, ∑ slotTwo : Fin basisCount,
          tightDir (basisLabel slotOne) atomOne * gram slotOne slotTwo
            * tightDir (basisLabel slotTwo) atomOne := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun slotOne _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun slotTwo _ => ?_
    rw [hclone slotTwo]
    ring
  rw [hscaled, hentryDiag] at hentryCross
  exact hentryCross.symm

end ShiftedReading

/-! ## Layer 10 — the coverage law at the three rungs -/

section RungSupply

variable {crux : SixThreeCrux}

/-- The rank-four frame covers every atom with a live basis column. -/
theorem RankFourFrame.exists_live_slot (frame : RankFourFrame crux)
    (atomIndex : Fin 6) :
    ∃ slot : Fin 4, frame.tightDir (frame.basisLabel slot) atomIndex ≠ 0 :=
  exists_live_basis_slot frame.hdata frame.hHform atomIndex

/-- The rank-five frame covers every atom with a live basis column. -/
theorem RankFiveFrame.exists_live_slot (frame : RankFiveFrame crux)
    (atomIndex : Fin 6) :
    ∃ slot : Fin 5, frame.tightDir (frame.basisLabel slot) atomIndex ≠ 0 :=
  exists_live_basis_slot frame.hdata frame.hHform atomIndex

/-- The rank-six frame covers every atom with a live basis column. -/
theorem RankSixFrame.exists_live_slot (frame : RankSixFrame crux)
    (atomIndex : Fin 6) :
    ∃ slot : Fin 6, frame.tightDir (frame.basisLabel slot) atomIndex ≠ 0 :=
  exists_live_basis_slot frame.hdata frame.hHform atomIndex

/-- **THE ONE-ATOM KILL AT THE RANK-FIVE FRAME.** -/
theorem RankFiveFrame.false_of_basis_null_singleton (frame : RankFiveFrame crux)
    {nullVec : Fin 6 → ℝ} {liveAtom : Fin 6} (hlive : nullVec liveAtom ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ liveAtom → nullVec atomIndex = 0)
    (hnull : ∀ slot : Fin 5,
      frame.tightDir (frame.basisLabel slot) ⬝ᵥ nullVec = 0) :
    False :=
  _root_.Gtz.false_of_basis_null_singleton frame.hdata frame.hHform hlive hsupp
    hnull

/-- **THE ONE-ATOM KILL AT THE RANK-SIX FRAME.** -/
theorem RankSixFrame.false_of_basis_null_singleton (frame : RankSixFrame crux)
    {nullVec : Fin 6 → ℝ} {liveAtom : Fin 6} (hlive : nullVec liveAtom ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ liveAtom → nullVec atomIndex = 0)
    (hnull : ∀ slot : Fin 6,
      frame.tightDir (frame.basisLabel slot) ⬝ᵥ nullVec = 0) :
    False :=
  _root_.Gtz.false_of_basis_null_singleton frame.hdata frame.hHform hlive hsupp
    hnull

/-- **THE CLONE BOUNDARY LAW AT THE RANK-FIVE FRAME.**  A clone pair whose two
carriers exhaust the five slots sits at the boundary of the shifted weight. -/
theorem RankFiveFrame.clone_boundary_of_full_carrier (frame : RankFiveFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 5, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne)
    (hweight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
    (hfull : ∀ slot : Fin 5,
      atomOne ∈ frame.activeSubset (frame.basisLabel slot)
        ∨ atomTwo ∈ frame.activeSubset (frame.basisLabel slot)) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0 := by
  obtain ⟨liveSlot, hliveSlot⟩ := frame.exists_live_slot atomOne
  exact clone_shifted_weight_eq_zero_of_full_carrier frame.hdata
    frame.hvalueNeg frame.hmemAll frame.hrepresentation frame.hidempotent
    hscaleNe hclone hweight hfull hliveSlot

/-- **THE CLONE BOUNDARY LAW AT THE RANK-SIX FRAME.** -/
theorem RankSixFrame.clone_boundary_of_full_carrier (frame : RankSixFrame crux)
    {atomOne atomTwo : Fin 6} {scale : ℝ} (hscaleNe : scale ≠ 0)
    (hclone : ∀ slot : Fin 6, frame.tightDir (frame.basisLabel slot) atomTwo
      = scale * frame.tightDir (frame.basisLabel slot) atomOne)
    (hweight : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomOne
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomTwo)
    (hfull : ∀ slot : Fin 6,
      atomOne ∈ frame.activeSubset (frame.basisLabel slot)
        ∨ atomTwo ∈ frame.activeSubset (frame.basisLabel slot)) :
    chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomOne = 0 := by
  obtain ⟨liveSlot, hliveSlot⟩ := frame.exists_live_slot atomOne
  exact clone_shifted_weight_eq_zero_of_full_carrier frame.hdata
    frame.hvalueNeg frame.hmemAll frame.hrepresentation frame.hidempotent
    hscaleNe hclone hweight hfull hliveSlot

end RungSupply

/-! ## Layer 11 — the pair slot is dead off the pair -/

section PairSlot

variable {crux : SixThreeCrux}

/-- **THE NON-PAIR LIVE SLOT.**  At an atom outside the pair the pair column is
dead, thus the coverage law supplies a live slot OTHER than the pair slot. -/
theorem RankFourOuterData.exists_live_slot_ne_columnIndex
    (data : RankFourOuterData crux) {atomIndex : Fin 6}
    (hU : atomIndex ≠ data.atomU) (hV : atomIndex ≠ data.atomV) :
    ∃ slot : Fin 4, slot ≠ data.columnIndex
      ∧ data.frame.tightDir (data.frame.basisLabel slot) atomIndex ≠ 0 := by
  obtain ⟨slot, hslot⟩ := data.exists_live_slot atomIndex
  refine ⟨slot, ?_, hslot⟩
  intro hEq
  rw [hEq] at hslot
  exact hslot (data.hsupp atomIndex hU hV)

/-- **THE CLONE MEETS OFF THE PAIR SLOT.**  A clone pair outside the pair atoms
shares a live slot, and that slot is never the pair slot. -/
theorem RankFourOuterData.clone_live_slot_ne_columnIndex
    (data : RankFourOuterData crux) {atomOne atomTwo : Fin 6} {scale : ℝ}
    (hscaleNe : scale ≠ 0)
    (hOneU : atomOne ≠ data.atomU) (hOneV : atomOne ≠ data.atomV)
    (hclone : ∀ slot : Fin 4,
      data.frame.tightDir (data.frame.basisLabel slot) atomTwo
        = scale * data.frame.tightDir (data.frame.basisLabel slot) atomOne) :
    ∃ slot : Fin 4, slot ≠ data.columnIndex
      ∧ slot ∈ blockCarrier data.frame.activeSubset data.frame.basisLabel
          atomOne
      ∧ slot ∈ blockCarrier data.frame.activeSubset data.frame.basisLabel
          atomTwo := by
  obtain ⟨slot, hslotNe, hslot⟩ :=
    data.exists_live_slot_ne_columnIndex hOneU hOneV
  have hliveTwo : data.frame.tightDir (data.frame.basisLabel slot) atomTwo
      ≠ 0 := by
    rw [hclone slot]
    exact mul_ne_zero hscaleNe hslot
  refine ⟨slot, hslotNe, blockCarrier_mem.mpr ?_, blockCarrier_mem.mpr ?_⟩
  · by_contra hout
    exact hslot (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll slot) atomOne hout)
  · by_contra hout
    exact hliveTwo (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll slot) atomTwo hout)

/-- **THE PAIR SLOT CARRIES A CLONE ATOM AT A FULL CARRIER.**  A full clone
carrier forces one of the two clone atoms into the block of the pair column,
thus onto its dead third atom. -/
theorem RankFourOuterData.clone_full_carrier_meets_pair_block
    (data : RankFourOuterData crux) {atomOne atomTwo : Fin 6}
    (hfull : ∀ slot : Fin 4,
      atomOne ∈ data.frame.activeSubset (data.frame.basisLabel slot)
        ∨ atomTwo ∈ data.frame.activeSubset (data.frame.basisLabel slot))
    (hOneU : atomOne ≠ data.atomU) (hOneV : atomOne ≠ data.atomV)
    (hTwoU : atomTwo ≠ data.atomU) (hTwoV : atomTwo ≠ data.atomV) :
    (atomOne ∈ data.frame.activeSubset
        (data.frame.basisLabel data.columnIndex)
      ∧ data.frame.tightDir (data.frame.basisLabel data.columnIndex) atomOne
        = 0)
    ∨ (atomTwo ∈ data.frame.activeSubset
        (data.frame.basisLabel data.columnIndex)
      ∧ data.frame.tightDir (data.frame.basisLabel data.columnIndex) atomTwo
        = 0) := by
  rcases hfull data.columnIndex with hmemOne | hmemTwo
  · exact Or.inl ⟨hmemOne, data.hsupp atomOne hOneU hOneV⟩
  · exact Or.inr ⟨hmemTwo, data.hsupp atomTwo hTwoU hTwoV⟩

end PairSlot

end Gtz
