import Gtz.Wave.OuterDenseCornerKill
import Gtz.Wave.OuterColumnGramFold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The outer circuit residue — the pin coefficient calculus and the rank-one gap block

The three outer data of the assembly-rank route carry one open residue for
closure one: the circuit label.  A circuit label is a positive label that is
parallel to no basis column.  This module supplies the two layers that the
residue map named, and it narrows the residue at each of the three ranks.

The first layer is the COEFFICIENT ROW CALCULUS of a general positive label.
The landed master law reads the coefficient matrix at a basis label only.  The
reconstruction turns the chart into the coefficient image at every positive
label, thus the master law holds for the whole positive family.  At a
block-pinned atom the row collapses to one slot, and the pin row law prices
the coefficient image at the pin slot by the shifted weight.  With the landed
diagonal pin the law becomes an off-diagonal relation on the coefficient
reading.  The landed circuit kill supplies the other branch, thus every
positive label obeys the PIN DICHOTOMY: either its coefficient reading dies at
the pin slot, or its coefficient reading annihilates the off-diagonal pin row.

The second layer is the RANK-ONE GAP BLOCK.  A support-two column forces the
two-by-two shifted gap minor on its pair to vanish.  If a second label carries
the same pair inside a three-atom block, and its pair restriction is
independent of the column, then the five eigen rows solve completely: the
third coordinate is alive, and all six two-by-two minors of the shifted gap
block vanish.  Thus the shifted gap on the block is a rank-one square, and the
block carries a two-dimensional null family.  The solver is division-free and
consumes only two positive gap diagonals.

The last layer narrows the residue.  A circuit label is not parallel to the
pair column, thus its pair restriction is independent whenever its block
carries the pair.  Thus the circuit residue at each rank splits into the
OFF-PAIR residue, where the block misses a pair atom, and the RANK-ONE
residue, where the shifted gap block is a rank-one square.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.mulVec_apply_of_triple_support` — the three-atom row read.
* `Gtz.projection_mulVec_eq_basis_of_mem_positive` — the chart of a positive
  direction is the basis combination of the coefficient image.
* `Gtz.coefficient_row_reading` — **THE GENERAL MASTER LAW.**
* `Gtz.pin_coefficient_row_reading` — **THE PIN ROW LAW.**
* `Gtz.pin_coefficient_offdiag_sum_eq_zero`,
  `Gtz.pin_coefficient_dichotomy` — **THE PIN DICHOTOMY.**
* `Gtz.parallel_of_coefficient_support_le_one`,
  `Gtz.exists_two_live_coefficient_slots` — the circuit reading.
* `Gtz.private_of_blockCarrier_singleton` — the block pin is a private atom.
* `Gtz.exists_block_third_atom_of_card_three` — the third block atom.
* `Gtz.cross_ne_zero_of_not_parallel_pair_column` — the independence law.
* `Gtz.gap_rank_one_of_pair_and_wide` — **THE RANK-ONE CORNER SOLVER.**
* `Gtz.gap_pair_minor_eq_zero_of_pair_supported` — **THE PAIR MINOR LAW.**
* `Gtz.GapBlockRankOne`, `Gtz.gap_block_rank_one_of_pair_wide` — **THE
  RANK-ONE GAP BLOCK.**
* `Gtz.circuit_gap_rank_one_of_pair_column` — **THE CIRCUIT NARROWING AT THE
  DATUM.**
* `Gtz.RankFourOuterData.circuit_pin_dichotomy`,
  `Gtz.RankFiveOuterData.circuit_pin_dichotomy` — the pin readings.
* `Gtz.RankFourOuterOffPairCircuitClosed`,
  `Gtz.RankFourOuterRankOneCircuitClosed` — the two rank-four residues.
* `Gtz.rankFourOuterCircuitClosed_of_narrowed`,
  `Gtz.rankFourSupportTwoClosed_of_narrowed_interior` — **THE RANK-FOUR
  NARROWING.**
* `Gtz.rankFiveOuterCircuitClosed_of_narrowed`,
  `Gtz.rankSixOuterCircuitClosed_of_narrowed` — the two other rungs.
* `Gtz.rankFiveSupportTwoClosed_of_narrowed_refined`,
  `Gtz.rankSixSupportTwoClosed_of_narrowed_lowProfile` — the two other
  discharges.
* `Gtz.gap_rankOne_cross_ne_zero`, `Gtz.gap_rankOne_side_ne_zero` — the live
  cross entries of a rank-one block.
* `Gtz.gap_pair_tight_at_third_of_rankOne` — **THE FOUR-ATOM NULL LAW.**
* `Gtz.exists_pair_null_of_rankOne_block` — **THE PAIR NULL FAMILY.**
* `Gtz.false_of_pair_null_independent` — **THE PAIR NULL KILL.**
* `Gtz.RankFourOuterData.pair_column_tight_at_rankOne_atom`,
  `Gtz.RankFourOuterData.exists_pair_null_of_rankOne`,
  `Gtz.RankFourOuterData.false_of_rankOne_pair_independent` — the rank-one
  readings at the rank-four outer datum.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds: no crux
exists, thus no frame exists.  The statements of layers one and two hold at
every stationary datum with a chosen basis.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the coefficient row calculus of a general positive label -/

section Coefficients

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- The chart of a positive direction is the basis combination of the
coefficient image: the reconstruction carries the representation. -/
theorem projection_mulVec_eq_basis_of_mem_positive
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight) :
    projection *ᵥ tightDir label
      = tightBasisColumns tightDir basisLabel
        *ᵥ (coeff *ᵥ (leftInv *ᵥ tightDir label)) := by
  conv_lhs => rw [tightDir_eq_reconstruction_of_mem_positive hdata basisLabel
    hbasisSpan leftInv hleft hmem]
  rw [Matrix.mulVec_mulVec, hrepresentation, ← Matrix.mulVec_mulVec]

/-- **THE GENERAL MASTER LAW.**  At every atom of a positive label's block,
the basis coordinates contract the coefficient image to the shifted weight
times the same contraction of the coefficient reading. -/
theorem coefficient_row_reading
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    {atomIndex : Fin size} (hatomMem : atomIndex ∈ activeSubset label) :
    ∑ columnIndex : Fin basisCount,
        tightDir (basisLabel columnIndex) atomIndex
          * (coeff *ᵥ (leftInv *ᵥ tightDir label)) columnIndex
      = (value + weight atomIndex)
        * ∑ columnIndex : Fin basisCount,
            tightDir (basisLabel columnIndex) atomIndex
              * (leftInv *ᵥ tightDir label) columnIndex := by
  have hchart := projection_mulVec_eq_basis_of_mem_positive hdata basisLabel
    hbasisSpan leftInv hleft hrepresentation hmem
  have hleftRead : (projection *ᵥ tightDir label) atomIndex
      = ∑ columnIndex : Fin basisCount,
          tightDir (basisLabel columnIndex) atomIndex
            * (coeff *ᵥ (leftInv *ᵥ tightDir label)) columnIndex := by
    rw [hchart]
    rfl
  have hrightRead : tightDir label atomIndex
      = ∑ columnIndex : Fin basisCount,
          tightDir (basisLabel columnIndex) atomIndex
            * (leftInv *ᵥ tightDir label) columnIndex := by
    conv_lhs => rw [tightDir_eq_reconstruction_of_mem_positive hdata basisLabel
      hbasisSpan leftInv hleft hmem]
    rfl
  have htight := projection_mulVec_tightDir_of_mem hdata
    (positiveActiveSet_subset_activeSet hmem) hatomMem
  rw [← hleftRead, ← hrightRead]
  exact htight

/-- **THE PIN ROW LAW.**  At a private atom of a positive label's block the
master law collapses to the private slot: the coefficient image at the slot is
the shifted weight times the coefficient reading at the slot. -/
theorem pin_coefficient_row_reading
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    (hatomMem : privateAtom ∈ activeSubset label) :
    (coeff *ᵥ (leftInv *ᵥ tightDir label)) privateSlot
      = (value + weight privateAtom)
        * (leftInv *ᵥ tightDir label) privateSlot := by
  classical
  have hmaster := coefficient_row_reading hdata basisLabel hbasisSpan leftInv
    hleft hrepresentation hmem hatomMem
  have hcollapseLeft : ∑ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) privateAtom
        * (coeff *ᵥ (leftInv *ᵥ tightDir label)) columnIndex
      = tightDir (basisLabel privateSlot) privateAtom
        * (coeff *ᵥ (leftInv *ᵥ tightDir label)) privateSlot := by
    refine Finset.sum_eq_single privateSlot (fun columnIndex _ hne => ?_)
      (fun habs => absurd (Finset.mem_univ _) habs)
    rw [hprivate columnIndex hne, zero_mul]
  have hcollapseRight : ∑ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) privateAtom
        * (leftInv *ᵥ tightDir label) columnIndex
      = tightDir (basisLabel privateSlot) privateAtom
        * (leftInv *ᵥ tightDir label) privateSlot := by
    refine Finset.sum_eq_single privateSlot (fun columnIndex _ hne => ?_)
      (fun habs => absurd (Finset.mem_univ _) habs)
    rw [hprivate columnIndex hne, zero_mul]
  rw [hcollapseLeft, hcollapseRight] at hmaster
  refine mul_left_cancel₀ hslotNe ?_
  rw [hmaster]
  ring

/-- The off-diagonal form of the pin row law: the coefficient reading
annihilates the off-diagonal part of the pin row of the coefficient matrix. -/
theorem pin_coefficient_offdiag_sum_eq_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0)
    (hdiagonal : coeff privateSlot privateSlot = value + weight privateAtom)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    (hatomMem : privateAtom ∈ activeSubset label) :
    ∑ columnIndex ∈ Finset.univ.erase privateSlot,
        coeff privateSlot columnIndex
          * (leftInv *ᵥ tightDir label) columnIndex = 0 := by
  classical
  have hrow := pin_coefficient_row_reading hdata basisLabel hbasisSpan leftInv
    hleft hrepresentation hprivate hslotNe hmem hatomMem
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun columnIndex : Fin basisCount => coeff privateSlot columnIndex
      * (leftInv *ᵥ tightDir label) columnIndex)
    (Finset.mem_univ privateSlot)
  have himage : (coeff *ᵥ (leftInv *ᵥ tightDir label)) privateSlot
      = ∑ columnIndex : Fin basisCount, coeff privateSlot columnIndex
          * (leftInv *ᵥ tightDir label) columnIndex := rfl
  rw [himage, ← hsplit, hdiagonal] at hrow
  linarith

/-- **THE PIN DICHOTOMY.**  Every positive label either reads zero at the pin
slot, or its coefficient reading annihilates the off-diagonal pin row.  The
landed circuit kill supplies the first branch, the pin row law the second. -/
theorem pin_coefficient_dichotomy
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {coeff : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * coeff)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0)
    (hdiagonal : coeff privateSlot privateSlot = value + weight privateAtom)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight) :
    (leftInv *ᵥ tightDir label) privateSlot = 0
      ∨ ∑ columnIndex ∈ Finset.univ.erase privateSlot,
          coeff privateSlot columnIndex
            * (leftInv *ᵥ tightDir label) columnIndex = 0 := by
  classical
  by_cases hatomMem : privateAtom ∈ activeSubset label
  · exact Or.inr (pin_coefficient_offdiag_sum_eq_zero hdata basisLabel
      hbasisSpan leftInv hleft hrepresentation hprivate hslotNe hdiagonal hmem
      hatomMem)
  · exact Or.inl (coefficientReading_eq_zero_of_private_atom hdata basisLabel
      hbasisSpan leftInv hleft hprivate hslotNe hmem hatomMem)

/-- A positive label whose coefficient reading has at most one live slot is
parallel to a basis column. -/
theorem parallel_of_coefficient_support_le_one
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    (slotZero : Fin basisCount)
    (hsingle : ∀ slotOne slotTwo : Fin basisCount, slotOne ≠ slotTwo →
      (leftInv *ᵥ tightDir label) slotOne = 0
        ∨ (leftInv *ᵥ tightDir label) slotTwo = 0) :
    ∃ (slot : Fin basisCount) (scale : ℝ),
      tightDir label = scale • tightDir (basisLabel slot) := by
  classical
  have hreconstruction := tightDir_eq_reconstruction_of_mem_positive hdata
    basisLabel hbasisSpan leftInv hleft hmem
  rw [tightBasisColumns_mulVec] at hreconstruction
  by_cases hlive : ∃ slot : Fin basisCount,
      (leftInv *ᵥ tightDir label) slot ≠ 0
  · obtain ⟨liveSlot, hliveNe⟩ := hlive
    refine ⟨liveSlot, (leftInv *ᵥ tightDir label) liveSlot, ?_⟩
    conv_lhs => rw [hreconstruction]
    refine Finset.sum_eq_single (f := fun slot : Fin basisCount =>
        (leftInv *ᵥ tightDir label) slot • tightDir (basisLabel slot))
      liveSlot (fun slot _ hne => ?_)
      (fun habs => absurd (Finset.mem_univ _) habs)
    rcases hsingle slot liveSlot hne with hzero | hzero
    · rw [hzero, zero_smul]
    · exact absurd hzero hliveNe
  · refine ⟨slotZero, 0, ?_⟩
    have hallZero : ∀ slot : Fin basisCount,
        (leftInv *ᵥ tightDir label) slot = 0 := by
      intro slot
      by_contra hne
      exact hlive ⟨slot, hne⟩
    rw [hreconstruction, zero_smul]
    refine Finset.sum_eq_zero fun slot _ => ?_
    rw [hallZero slot, zero_smul]

/-- **THE CIRCUIT READING.**  A positive label parallel to no basis column has
two distinct live coefficient slots. -/
theorem exists_two_live_coefficient_slots
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (leftInv : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {label : activeIndex}
    (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    (slotZero : Fin basisCount)
    (hcircuit : ∀ (slot : Fin basisCount) (scale : ℝ),
      tightDir label ≠ scale • tightDir (basisLabel slot)) :
    ∃ slotOne slotTwo : Fin basisCount, slotOne ≠ slotTwo
      ∧ (leftInv *ᵥ tightDir label) slotOne ≠ 0
      ∧ (leftInv *ᵥ tightDir label) slotTwo ≠ 0 := by
  classical
  by_contra hnone
  refine absurd (parallel_of_coefficient_support_le_one hdata basisLabel
    hbasisSpan leftInv hleft hmem slotZero ?_) ?_
  · intro slotOne slotTwo hne
    by_contra hboth
    refine hnone ⟨slotOne, slotTwo, hne, ?_, ?_⟩
    · intro hzero
      exact hboth (Or.inl hzero)
    · intro hzero
      exact hboth (Or.inr hzero)
  · rintro ⟨slot, scale, hpar⟩
    exact hcircuit slot scale hpar

end Coefficients

/-! ## Layer 3 — the block pin is a private atom -/

section BlockPin

variable {rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin 6)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin 6 → ℝ)}
variable {basisCount : ℕ}

/-- **THE PIN PACKAGE.**  A block-pinned atom is a private atom: every other
basis column vanishes there, and the pinned column is alive there. -/
theorem private_of_blockCarrier_singleton
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {basisLabel : Fin basisCount → activeIndex}
    (hmemActive : ∀ slot, basisLabel slot ∈ activeSet)
    (hspan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    {leftInv : Matrix (Fin basisCount) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {pinAtom : Fin 6} {pinSlot : Fin basisCount}
    (hpin : blockCarrier activeSubset basisLabel pinAtom = {pinSlot}) :
    (∀ columnIndex, columnIndex ≠ pinSlot →
        tightDir (basisLabel columnIndex) pinAtom = 0)
      ∧ tightDir (basisLabel pinSlot) pinAtom ≠ 0 := by
  classical
  have houtside : ∀ columnIndex, columnIndex ≠ pinSlot →
      tightDir (basisLabel columnIndex) pinAtom = 0 := by
    intro columnIndex hne
    refine hdata.tightDir_support (basisLabel columnIndex)
      (hmemActive columnIndex) pinAtom ?_
    intro hmemBlock
    have hmemCar : columnIndex ∈ blockCarrier activeSubset basisLabel pinAtom :=
      blockCarrier_mem.mpr hmemBlock
    rw [hpin, Finset.mem_singleton] at hmemCar
    exact hne hmemCar
  refine ⟨houtside, ?_⟩
  obtain ⟨liveSlot, hliveMem⟩ := exists_basisIndex_datumTightSupport hdata
    basisLabel hspan leftInv hleft pinAtom
  have hliveNe := mem_datumTightSupport.mp hliveMem
  by_cases hsame : liveSlot = pinSlot
  · rw [← hsame]
    exact hliveNe
  · exact absurd (houtside liveSlot hsame) hliveNe

end BlockPin

/-! ## Layer 4 — the third block atom and the independence law -/

section Independence

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- A label with a three-atom block and two named block atoms names its third
block atom, and vanishes off the three. -/
theorem exists_block_third_atom_of_card_three
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hUblock : atomU ∈ activeSubset label)
    (hVblock : atomV ∈ activeSubset label) :
    ∃ atomS : Fin size, atomS ≠ atomU ∧ atomS ≠ atomV
      ∧ atomS ∈ activeSubset label
      ∧ ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        atomIndex ≠ atomS → tightDir label atomIndex = 0 := by
  classical
  have hsub : ({atomU, atomV} : Finset (Fin size)) ⊆ activeSubset label := by
    intro atomIndex hmemPair
    rcases Finset.mem_insert.mp hmemPair with rfl | hmemPair'
    · exact hUblock
    · rw [Finset.mem_singleton] at hmemPair'
      subst hmemPair'
      exact hVblock
  have hcardPair : ({atomU, atomV} : Finset (Fin size)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hUV]), Finset.card_singleton]
  have hcardSdiff : (activeSubset label
      \ ({atomU, atomV} : Finset (Fin size))).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      hdata.activeSubset_card label hmem, hcardPair]
  obtain ⟨atomS, hSset⟩ := Finset.card_eq_one.mp hcardSdiff
  have hSmem : atomS ∈ activeSubset label
      ∧ atomS ∉ ({atomU, atomV} : Finset (Fin size)) := by
    refine Finset.mem_sdiff.mp ?_
    rw [hSset]
    exact Finset.mem_singleton_self _
  refine ⟨atomS, ?_, ?_, hSmem.1, ?_⟩
  · intro heq
    refine hSmem.2 ?_
    rw [heq]
    exact Finset.mem_insert_self _ _
  · intro heq
    refine hSmem.2 ?_
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · intro atomIndex h1 h2 h3
    refine hdata.tightDir_support label hmem atomIndex ?_
    intro hmemBlock
    have hsdiff : atomIndex ∈ activeSubset label
        \ ({atomU, atomV} : Finset (Fin size)) := by
      refine Finset.mem_sdiff.mpr ⟨hmemBlock, ?_⟩
      simp [h1, h2]
    rw [hSset, Finset.mem_singleton] at hsdiff
    exact h3 hsdiff

/-- **THE INDEPENDENCE LAW.**  A label whose block carries the pair of a
support-two column, and which is no multiple of that column, has an
independent pair restriction.  A dependent restriction leaves a single-atom
difference, and the landed parallel kill closes it. -/
theorem cross_ne_zero_of_not_parallel_pair_column
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalueNeg : value < 0)
    (hfloor : ∀ atomIndex : Fin size,
      0 < chartStationaryGap projection weight atomIndex atomIndex)
    {pairLabel label : activeIndex}
    (hpairMem : pairLabel ∈ activeSet) (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hneU : tightDir pairLabel atomU ≠ 0)
    (hneV : tightDir pairLabel atomV ≠ 0)
    (hpairSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir pairLabel atomIndex = 0)
    (hUblock : atomU ∈ activeSubset label)
    (hVblock : atomV ∈ activeSubset label)
    (hnotParallel : ∀ scale : ℝ, tightDir label ≠ scale • tightDir pairLabel) :
    tightDir label atomU * tightDir pairLabel atomV
        - tightDir label atomV * tightDir pairLabel atomU ≠ 0 := by
  classical
  intro hzero
  obtain ⟨atomS, hSU, hSV, hSblock, hSsupp⟩ :=
    exists_block_third_atom_of_card_three hdata hmem hUV hUblock hVblock
  have hUpair : atomU ∈ activeSubset pairLabel := by
    by_contra hout
    exact hneU (hdata.tightDir_support pairLabel hpairMem atomU hout)
  have hVpair : atomV ∈ activeSubset pairLabel := by
    by_contra hout
    exact hneV (hdata.tightDir_support pairLabel hpairMem atomV hout)
  have hparU : tightDir label atomU
      = (tightDir label atomU / tightDir pairLabel atomU)
        * tightDir pairLabel atomU := by
    rw [div_mul_cancel₀ _ hneU]
  have hparV : tightDir label atomV
      = (tightDir label atomU / tightDir pairLabel atomU)
        * tightDir pairLabel atomV := by
    rw [div_mul_eq_mul_div, eq_div_iff hneU]
    linear_combination -hzero
  by_cases hSalive : tightDir label atomS = 0
  · refine hnotParallel (tightDir label atomU / tightDir pairLabel atomU) ?_
    funext atomIndex
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases h1 : atomIndex = atomU
    · rw [h1]
      exact hparU
    by_cases h2 : atomIndex = atomV
    · rw [h2]
      exact hparV
    by_cases h3 : atomIndex = atomS
    · rw [h3, hSalive, hpairSupp atomS hSU hSV, mul_zero]
    · rw [hSsupp atomIndex h1 h2 h3, hpairSupp atomIndex h1 h2, mul_zero]
  · exact false_of_parallel_pair_column_combination hdata hvalueNeg hpairMem
      hmem hUV hSU hSV hUpair hVpair hpairSupp hUblock hVblock hSblock hSsupp
      hparU hparV hSalive (hfloor atomS)

end Independence

/-! ## Layer 5 — the rank-one corner solver -/

/-- **THE RANK-ONE CORNER SOLVER.**  Two eigen rows of a pair-supported
direction and three eigen rows of a wide direction on the same three atoms,
with an independent pair restriction, price the six two-by-two minors of the
shifted gap block.  The block is a rank-one square, and the wide direction is
alive at the third atom.  The solver is division-free and uses two positive
diagonals only. -/
theorem gap_rank_one_of_pair_and_wide
    {cornerUU cornerVV cornerSS cornerUV cornerUS cornerVS : ℝ}
    {pairU pairV wideU wideV wideS : ℝ}
    (hUUpos : 0 < cornerUU) (hVVpos : 0 < cornerVV)
    (hpairU : pairU ≠ 0) (hpairV : pairV ≠ 0)
    (hindep : wideV * pairU - wideU * pairV ≠ 0)
    (hpairRowU : cornerUU * pairU + cornerUV * pairV = 0)
    (hpairRowV : cornerUV * pairU + cornerVV * pairV = 0)
    (hwideRowU : cornerUU * wideU + cornerUV * wideV + cornerUS * wideS = 0)
    (hwideRowV : cornerUV * wideU + cornerVV * wideV + cornerVS * wideS = 0)
    (hwideRowS : cornerUS * wideU + cornerVS * wideV + cornerSS * wideS = 0) :
    wideS ≠ 0
      ∧ cornerUV * cornerUV = cornerUU * cornerVV
      ∧ cornerUS * cornerUS = cornerUU * cornerSS
      ∧ cornerVS * cornerVS = cornerVV * cornerSS
      ∧ cornerUU * cornerVS = cornerUV * cornerUS
      ∧ cornerVV * cornerUS = cornerUV * cornerVS
      ∧ cornerSS * cornerUV = cornerUS * cornerVS := by
  -- the pair minor
  have hpairMinor : cornerUV * cornerUV = cornerUU * cornerVV := by
    have hprod : pairU * pairV
        * (cornerUV * cornerUV - cornerUU * cornerVV) = 0 := by
      linear_combination (cornerUV * pairV) * hpairRowV
        - (cornerVV * pairV) * hpairRowU
    have hfac := (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero hpairU hpairV)
    linarith
  -- the two reduced rows of the difference direction
  have hrowU : cornerUV * (wideV * pairU - wideU * pairV)
      + cornerUS * (wideS * pairU) = 0 := by
    linear_combination pairU * hwideRowU - wideU * hpairRowU
  have hrowV : cornerVV * (wideV * pairU - wideU * pairV)
      + cornerVS * (wideS * pairU) = 0 := by
    linear_combination pairU * hwideRowV - wideU * hpairRowV
  -- the third coordinate is alive
  have hthird : wideS * pairU ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, add_zero] at hrowV
    exact hindep ((mul_eq_zero.mp hrowV).resolve_left hVVpos.ne')
  have hwideS : wideS ≠ 0 := by
    intro hzero
    exact hthird (by rw [hzero, zero_mul])
  -- the cross relation of the third row
  have hcross : cornerUS * pairU + cornerVS * pairV = 0 := by
    have hprod : (wideS * pairU) * (cornerUS * pairU + cornerVS * pairV) = 0 := by
      linear_combination pairU * hrowU + pairV * hrowV
        - (wideV * pairU - wideU * pairV) * hpairRowV
    exact (mul_eq_zero.mp hprod).resolve_left hthird
  have hrowS : cornerVS * (wideV * pairU - wideU * pairV)
      + cornerSS * (wideS * pairU) = 0 := by
    linear_combination pairU * hwideRowS - wideU * hcross
  -- the three remaining minors
  have hVSminor : cornerVS * cornerVS = cornerVV * cornerSS := by
    have hprod : (wideS * pairU)
        * (cornerVS * cornerVS - cornerVV * cornerSS) = 0 := by
      linear_combination cornerVS * hrowV - cornerVV * hrowS
    have hfac := (mul_eq_zero.mp hprod).resolve_left hthird
    linarith
  have hSSminor : cornerSS * cornerUV = cornerUS * cornerVS := by
    have hprod : (wideV * pairU - wideU * pairV)
        * (cornerSS * cornerUV - cornerUS * cornerVS) = 0 := by
      linear_combination cornerSS * hrowU - cornerUS * hrowS
    have hfac := (mul_eq_zero.mp hprod).resolve_left hindep
    linarith
  have hVVminor : cornerVV * cornerUS = cornerUV * cornerVS := by
    have hprod : (wideV * pairU - wideU * pairV)
        * (cornerUV * cornerVS - cornerUS * cornerVV) = 0 := by
      linear_combination cornerVS * hrowU - cornerUS * hrowV
    have hfac := (mul_eq_zero.mp hprod).resolve_left hindep
    linarith
  have hUSminor : cornerUS * cornerUS = cornerUU * cornerSS := by
    have hprod : cornerVV
        * (cornerUS * cornerUS - cornerUU * cornerSS) = 0 := by
      linear_combination cornerUS * hVVminor - cornerUV * hSSminor
        + cornerSS * hpairMinor
    have hfac := (mul_eq_zero.mp hprod).resolve_left hVVpos.ne'
    linarith
  have hUVne : cornerUV ≠ 0 := by
    intro hzero
    rw [hzero] at hpairMinor
    nlinarith [hpairMinor, hUUpos, hVVpos]
  have hUUminor : cornerUU * cornerVS = cornerUV * cornerUS := by
    have hprod : cornerUV
        * (cornerUU * cornerVS - cornerUV * cornerUS) = 0 := by
      linear_combination (-cornerUU) * hVVminor - cornerUS * hpairMinor
    have hfac := (mul_eq_zero.mp hprod).resolve_left hUVne
    linarith
  exact ⟨hwideS, hpairMinor, hUSminor, hVSminor, hUUminor, hVVminor, hSSminor⟩

/-! ## Layer 6 — the gap minors at the datum -/

section GapMinors

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE PAIR MINOR LAW.**  A tight direction supported on a pair of atoms,
alive at both, forces the two-by-two shifted gap minor on the pair to
vanish. -/
theorem gap_pair_minor_eq_zero_of_pair_supported
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hUmem : atomU ∈ activeSubset label) (hVmem : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0)
    (hneU : tightDir label atomU ≠ 0) (hneV : tightDir label atomV ≠ 0) :
    chartStationaryGap projection weight atomU atomV
        * chartStationaryGap projection weight atomU atomV
      = (chartStationaryGap projection weight atomU atomU - value)
        * (chartStationaryGap projection weight atomV atomV - value) := by
  have hrowU := hdata.tightDir_isTight label hmem atomU hUmem
  have hrowV := hdata.tightDir_isTight label hmem atomV hVmem
  rw [mulVec_apply_of_pair_support _ hUV hsupp atomU] at hrowU
  rw [mulVec_apply_of_pair_support _ hUV hsupp atomV] at hrowV
  rw [chartStationaryGap_entry_symm hdata atomV atomU] at hrowV
  have hprod : tightDir label atomU * tightDir label atomV
      * (chartStationaryGap projection weight atomU atomV
          * chartStationaryGap projection weight atomU atomV
        - (chartStationaryGap projection weight atomU atomU - value)
          * (chartStationaryGap projection weight atomV atomV - value)) = 0 := by
    linear_combination
      (chartStationaryGap projection weight atomU atomV
        * tightDir label atomV) * hrowV
      - (chartStationaryGap projection weight atomV atomV - value)
        * tightDir label atomV * hrowU
  have hfac := (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hneU hneV)
  linarith

/-- **THE RANK-ONE GAP SHAPE.**  The six two-by-two minors of the shifted gap
block on three atoms vanish, thus the block is a rank-one square. -/
def GapBlockRankOne {size : ℕ} (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (atomU atomV atomS : Fin size) : Prop :=
  chartStationaryGap projection weight atomU atomV
      * chartStationaryGap projection weight atomU atomV
    = (chartStationaryGap projection weight atomU atomU - value)
      * (chartStationaryGap projection weight atomV atomV - value)
  ∧ chartStationaryGap projection weight atomU atomS
      * chartStationaryGap projection weight atomU atomS
    = (chartStationaryGap projection weight atomU atomU - value)
      * (chartStationaryGap projection weight atomS atomS - value)
  ∧ chartStationaryGap projection weight atomV atomS
      * chartStationaryGap projection weight atomV atomS
    = (chartStationaryGap projection weight atomV atomV - value)
      * (chartStationaryGap projection weight atomS atomS - value)
  ∧ (chartStationaryGap projection weight atomU atomU - value)
      * chartStationaryGap projection weight atomV atomS
    = chartStationaryGap projection weight atomU atomV
      * chartStationaryGap projection weight atomU atomS
  ∧ (chartStationaryGap projection weight atomV atomV - value)
      * chartStationaryGap projection weight atomU atomS
    = chartStationaryGap projection weight atomU atomV
      * chartStationaryGap projection weight atomV atomS
  ∧ (chartStationaryGap projection weight atomS atomS - value)
      * chartStationaryGap projection weight atomU atomV
    = chartStationaryGap projection weight atomU atomS
      * chartStationaryGap projection weight atomV atomS

/-- **THE RANK-ONE GAP BLOCK.**  A pair-supported direction and a wide
direction whose block carries the pair, with independent pair restrictions,
force the shifted gap block on the wide block to be a rank-one square.  The
wide direction is alive at its third block atom. -/
theorem gap_block_rank_one_of_pair_wide
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalueNeg : value < 0)
    {pairLabel wideLabel : activeIndex}
    (hpairMem : pairLabel ∈ activeSet) (hwideMem : wideLabel ∈ activeSet)
    {atomU atomV atomS : Fin size}
    (hfloorU : 0 < chartStationaryGap projection weight atomU atomU)
    (hfloorV : 0 < chartStationaryGap projection weight atomV atomV)
    (hUV : atomU ≠ atomV) (hSU : atomS ≠ atomU) (hSV : atomS ≠ atomV)
    (hUpair : atomU ∈ activeSubset pairLabel)
    (hVpair : atomV ∈ activeSubset pairLabel)
    (hpairSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir pairLabel atomIndex = 0)
    (hneU : tightDir pairLabel atomU ≠ 0)
    (hneV : tightDir pairLabel atomV ≠ 0)
    (hUwide : atomU ∈ activeSubset wideLabel)
    (hVwide : atomV ∈ activeSubset wideLabel)
    (hSwide : atomS ∈ activeSubset wideLabel)
    (hwideSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir wideLabel atomIndex = 0)
    (hindep : tightDir wideLabel atomU * tightDir pairLabel atomV
      - tightDir wideLabel atomV * tightDir pairLabel atomU ≠ 0) :
    tightDir wideLabel atomS ≠ 0
      ∧ GapBlockRankOne projection weight value atomU atomV atomS := by
  have hpairRowU := hdata.tightDir_isTight pairLabel hpairMem atomU hUpair
  have hpairRowV := hdata.tightDir_isTight pairLabel hpairMem atomV hVpair
  rw [mulVec_apply_of_pair_support _ hUV hpairSupp atomU] at hpairRowU
  rw [mulVec_apply_of_pair_support _ hUV hpairSupp atomV] at hpairRowV
  rw [chartStationaryGap_entry_symm hdata atomV atomU] at hpairRowV
  have hwideRowU := hdata.tightDir_isTight wideLabel hwideMem atomU hUwide
  have hwideRowV := hdata.tightDir_isTight wideLabel hwideMem atomV hVwide
  have hwideRowS := hdata.tightDir_isTight wideLabel hwideMem atomS hSwide
  rw [mulVec_apply_of_triple_support _ hUV hSU.symm hSV.symm hwideSupp atomU]
    at hwideRowU
  rw [mulVec_apply_of_triple_support _ hUV hSU.symm hSV.symm hwideSupp atomV]
    at hwideRowV
  rw [mulVec_apply_of_triple_support _ hUV hSU.symm hSV.symm hwideSupp atomS]
    at hwideRowS
  rw [chartStationaryGap_entry_symm hdata atomV atomU] at hwideRowV
  rw [chartStationaryGap_entry_symm hdata atomS atomU, chartStationaryGap_entry_symm hdata atomS atomV]
    at hwideRowS
  obtain ⟨hwideS, h1, h2, h3, h4, h5, h6⟩ :=
    gap_rank_one_of_pair_and_wide
      (cornerUU := chartStationaryGap projection weight atomU atomU - value)
      (cornerVV := chartStationaryGap projection weight atomV atomV - value)
      (cornerSS := chartStationaryGap projection weight atomS atomS - value)
      (cornerUV := chartStationaryGap projection weight atomU atomV)
      (cornerUS := chartStationaryGap projection weight atomU atomS)
      (cornerVS := chartStationaryGap projection weight atomV atomS)
      (pairU := tightDir pairLabel atomU) (pairV := tightDir pairLabel atomV)
      (wideU := tightDir wideLabel atomU) (wideV := tightDir wideLabel atomV)
      (wideS := tightDir wideLabel atomS)
      (by linarith) (by linarith) hneU hneV
      (by
        intro hzero
        exact hindep (by linear_combination -hzero))
      (by linear_combination hpairRowU) (by linear_combination hpairRowV)
      (by linear_combination hwideRowU) (by linear_combination hwideRowV)
      (by linear_combination hwideRowS)
  exact ⟨hwideS, h1, h2, h3, h4, h5, h6⟩

/-- **THE CIRCUIT NARROWING AT THE DATUM.**  A circuit label whose block
carries the pair of a support-two column is alive at its third block atom, and
the shifted gap block on its block is a rank-one square. -/
theorem circuit_gap_rank_one_of_pair_column
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalueNeg : value < 0)
    (hfloor : ∀ atomIndex : Fin size,
      0 < chartStationaryGap projection weight atomIndex atomIndex)
    {pairLabel label : activeIndex}
    (hpairMem : pairLabel ∈ activeSet) (hmem : label ∈ activeSet)
    {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    (hneU : tightDir pairLabel atomU ≠ 0)
    (hneV : tightDir pairLabel atomV ≠ 0)
    (hpairSupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir pairLabel atomIndex = 0)
    (hUblock : atomU ∈ activeSubset label)
    (hVblock : atomV ∈ activeSubset label)
    (hnotParallel : ∀ scale : ℝ, tightDir label ≠ scale • tightDir pairLabel) :
    ∃ atomS : Fin size, atomS ≠ atomU ∧ atomS ≠ atomV
      ∧ atomS ∈ activeSubset label
      ∧ tightDir label atomS ≠ 0
      ∧ GapBlockRankOne projection weight value atomU atomV atomS := by
  obtain ⟨atomS, hSU, hSV, hSblock, hSsupp⟩ :=
    exists_block_third_atom_of_card_three hdata hmem hUV hUblock hVblock
  have hUpair : atomU ∈ activeSubset pairLabel := by
    by_contra hout
    exact hneU (hdata.tightDir_support pairLabel hpairMem atomU hout)
  have hVpair : atomV ∈ activeSubset pairLabel := by
    by_contra hout
    exact hneV (hdata.tightDir_support pairLabel hpairMem atomV hout)
  have hindep := cross_ne_zero_of_not_parallel_pair_column hdata hvalueNeg
    hfloor hpairMem hmem hUV hneU hneV hpairSupp hUblock hVblock hnotParallel
  obtain ⟨hwideS, hshape⟩ := gap_block_rank_one_of_pair_wide hdata hvalueNeg
    hpairMem hmem (hfloor atomU) (hfloor atomV) hUV hSU hSV hUpair hVpair
    hpairSupp hneU hneV hUblock hVblock hSblock hSsupp hindep
  exact ⟨atomS, hSU, hSV, hSblock, hwideS, hshape⟩

end GapMinors

/-! ## Layer 7 — the readings at the three outer data -/

section OuterReadings

variable {crux : SixThreeCrux}

/-- **THE RANK-FOUR PAIR MINOR.**  The shifted gap minor on the pair of a
rank-four outer datum vanishes, with no hypothesis. -/
theorem RankFourOuterData.gap_pair_minor (data : RankFourOuterData crux) :
    chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight data.atomU data.atomV
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight data.atomU data.atomV
    = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight data.atomU data.atomU
        - chartObjective (chartPointOfDesign crux.design))
      * (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight data.atomV data.atomV
        - chartObjective (chartPointOfDesign crux.design)) := by
  have hUblock : data.atomU
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneU (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomU hout)
  have hVblock : data.atomV
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneV (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomV hout)
  exact gap_pair_minor_eq_zero_of_pair_supported data.frame.hdata
    (data.frame.hmemAll data.columnIndex) data.hUV hUblock hVblock data.hsupp
    data.hneU data.hneV

/-- **THE RANK-FIVE PAIR MINOR.** -/
theorem RankFiveOuterData.gap_pair_minor (data : RankFiveOuterData crux) :
    chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight data.atomU data.atomV
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight data.atomU data.atomV
    = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight data.atomU data.atomU
        - chartObjective (chartPointOfDesign crux.design))
      * (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight data.atomV data.atomV
        - chartObjective (chartPointOfDesign crux.design)) := by
  have hUblock : data.atomU
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneU (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomU hout)
  have hVblock : data.atomV
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneV (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomV hout)
  exact gap_pair_minor_eq_zero_of_pair_supported data.frame.hdata
    (data.frame.hmemAll data.columnIndex) data.hUV hUblock hVblock data.hsupp
    data.hneU data.hneV

/-- **THE RANK-SIX PAIR MINOR.** -/
theorem RankSixOuterData.gap_pair_minor (data : RankSixOuterData crux) :
    chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight data.atomU data.atomV
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight data.atomU data.atomV
    = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight data.atomU data.atomU
        - chartObjective (chartPointOfDesign crux.design))
      * (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight data.atomV data.atomV
        - chartObjective (chartPointOfDesign crux.design)) := by
  have hUblock : data.atomU
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneU (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomU hout)
  have hVblock : data.atomV
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneV (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomV hout)
  exact gap_pair_minor_eq_zero_of_pair_supported data.frame.hdata
    (data.frame.hmemAll data.columnIndex) data.hUV hUblock hVblock data.hsupp
    data.hneU data.hneV

/-- **THE RANK-FOUR CIRCUIT SHAPE.**  A circuit label whose block carries the
pair of a rank-four outer datum is alive at its third block atom, and the
shifted gap block on its block is a rank-one square. -/
theorem RankFourOuterData.circuit_gap_rank_one (data : RankFourOuterData crux)
    {label : data.frame.activeIndex} (hmem : label ∈ data.frame.activeSet)
    (hUblock : data.atomU ∈ data.frame.activeSubset label)
    (hVblock : data.atomV ∈ data.frame.activeSubset label)
    (hcircuit : ∀ (slot : Fin 4) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) :
    ∃ atomS : Fin 6, atomS ≠ data.atomU ∧ atomS ≠ data.atomV
      ∧ atomS ∈ data.frame.activeSubset label
      ∧ data.frame.tightDir label atomS ≠ 0
      ∧ GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          data.atomU data.atomV atomS :=
  circuit_gap_rank_one_of_pair_column data.frame.hdata data.frame.hvalueNeg
    crux.gap_diagonal_pos_of_allHeavy (data.frame.hmemAll data.columnIndex)
    hmem data.hUV data.hneU data.hneV data.hsupp hUblock hVblock
    (fun scale => hcircuit data.columnIndex scale)

/-- **THE RANK-FIVE CIRCUIT SHAPE.** -/
theorem RankFiveOuterData.circuit_gap_rank_one (data : RankFiveOuterData crux)
    {label : data.frame.activeIndex} (hmem : label ∈ data.frame.activeSet)
    (hUblock : data.atomU ∈ data.frame.activeSubset label)
    (hVblock : data.atomV ∈ data.frame.activeSubset label)
    (hcircuit : ∀ (slot : Fin 5) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) :
    ∃ atomS : Fin 6, atomS ≠ data.atomU ∧ atomS ≠ data.atomV
      ∧ atomS ∈ data.frame.activeSubset label
      ∧ data.frame.tightDir label atomS ≠ 0
      ∧ GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          data.atomU data.atomV atomS :=
  circuit_gap_rank_one_of_pair_column data.frame.hdata data.frame.hvalueNeg
    crux.gap_diagonal_pos_of_allHeavy (data.frame.hmemAll data.columnIndex)
    hmem data.hUV data.hneU data.hneV data.hsupp hUblock hVblock
    (fun scale => hcircuit data.columnIndex scale)

/-- **THE RANK-SIX CIRCUIT SHAPE.** -/
theorem RankSixOuterData.circuit_gap_rank_one (data : RankSixOuterData crux)
    {label : data.frame.activeIndex} (hmem : label ∈ data.frame.activeSet)
    (hUblock : data.atomU ∈ data.frame.activeSubset label)
    (hVblock : data.atomV ∈ data.frame.activeSubset label)
    (hcircuit : ∀ (slot : Fin 6) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) :
    ∃ atomS : Fin 6, atomS ≠ data.atomU ∧ atomS ≠ data.atomV
      ∧ atomS ∈ data.frame.activeSubset label
      ∧ data.frame.tightDir label atomS ≠ 0
      ∧ GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          data.atomU data.atomV atomS :=
  circuit_gap_rank_one_of_pair_column data.frame.hdata data.frame.hvalueNeg
    crux.gap_diagonal_pos_of_allHeavy (data.frame.hmemAll data.columnIndex)
    hmem data.hUV data.hneU data.hneV data.hsupp hUblock hVblock
    (fun scale => hcircuit data.columnIndex scale)

/-- **THE RANK-FOUR PIN DICHOTOMY.**  Every rank-four outer datum carries a
block-pinned atom, and at its pin slot every positive label either reads zero
or annihilates the off-diagonal pin row of the coefficient matrix. -/
theorem RankFourOuterData.circuit_pin_dichotomy (data : RankFourOuterData crux)
    {label : data.frame.activeIndex}
    (hmem : label ∈ positiveActiveSet data.frame.activeSet
      data.frame.reducedWeight) :
    ∃ (pinAtom : Fin 6) (pinSlot : Fin 4),
      blockCarrier data.frame.activeSubset data.frame.basisLabel pinAtom
          = {pinSlot}
        ∧ ((data.frame.leftInv *ᵥ data.frame.tightDir label) pinSlot = 0
          ∨ ∑ columnIndex ∈ Finset.univ.erase pinSlot,
              data.frame.coeff pinSlot columnIndex
                * (data.frame.leftInv *ᵥ data.frame.tightDir label) columnIndex
            = 0) := by
  obtain ⟨pinAtom, pinSlot, hpin⟩ := data.exists_block_pin
  obtain ⟨hprivate, hslotNe⟩ := private_of_blockCarrier_singleton
    data.frame.hdata data.frame.hmemAll data.frame.hspan data.frame.hleft hpin
  exact ⟨pinAtom, pinSlot, hpin, pin_coefficient_dichotomy data.frame.hdata
    data.frame.basisLabel data.frame.hspan data.frame.leftInv data.frame.hleft
    data.frame.hrepresentation hprivate hslotNe
    (data.frame.pin_coeff_diagonal hpin) hmem⟩

end OuterReadings

/-! ## Layer 8 — the two narrowed residues at each rung -/

/-- **THE RANK-FOUR OFF-PAIR RESIDUE.**  A positive label parallel to no basis
column, whose block misses a pair atom of the outer datum, dies. -/
def RankFourOuterOffPairCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 4) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    (data.atomU ∉ data.frame.activeSubset label
      ∨ data.atomV ∉ data.frame.activeSubset label) →
    False

/-- **THE RANK-FOUR RANK-ONE RESIDUE.**  A positive label parallel to no basis
column, whose block carries the pair with a rank-one shifted gap block,
dies. -/
def RankFourOuterRankOneCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
    (label : data.frame.activeIndex) (atomS : Fin 6),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 4) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    data.atomU ∈ data.frame.activeSubset label →
    data.atomV ∈ data.frame.activeSubset label →
    atomS ≠ data.atomU → atomS ≠ data.atomV →
    atomS ∈ data.frame.activeSubset label →
    data.frame.tightDir label atomS ≠ 0 →
    GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      data.atomU data.atomV atomS →
    False

/-- **THE RANK-FIVE OFF-PAIR RESIDUE.** -/
def RankFiveOuterOffPairCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFiveOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 5) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    (data.atomU ∉ data.frame.activeSubset label
      ∨ data.atomV ∉ data.frame.activeSubset label) →
    False

/-- **THE RANK-FIVE RANK-ONE RESIDUE.** -/
def RankFiveOuterRankOneCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankFiveOuterData crux)
    (label : data.frame.activeIndex) (atomS : Fin 6),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 5) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    data.atomU ∈ data.frame.activeSubset label →
    data.atomV ∈ data.frame.activeSubset label →
    atomS ≠ data.atomU → atomS ≠ data.atomV →
    atomS ∈ data.frame.activeSubset label →
    data.frame.tightDir label atomS ≠ 0 →
    GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      data.atomU data.atomV atomS →
    False

/-- **THE RANK-SIX OFF-PAIR RESIDUE.** -/
def RankSixOuterOffPairCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankSixOuterData crux)
    (label : data.frame.activeIndex),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 6) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    (data.atomU ∉ data.frame.activeSubset label
      ∨ data.atomV ∉ data.frame.activeSubset label) →
    False

/-- **THE RANK-SIX RANK-ONE RESIDUE.** -/
def RankSixOuterRankOneCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : RankSixOuterData crux)
    (label : data.frame.activeIndex) (atomS : Fin 6),
    label ∈ data.frame.activeSet →
    0 < data.frame.reducedWeight label →
    (∀ (slot : Fin 6) (scale : ℝ),
      data.frame.tightDir label
        ≠ scale • data.frame.tightDir (data.frame.basisLabel slot)) →
    data.atomU ∈ data.frame.activeSubset label →
    data.atomV ∈ data.frame.activeSubset label →
    atomS ≠ data.atomU → atomS ≠ data.atomV →
    atomS ∈ data.frame.activeSubset label →
    data.frame.tightDir label atomS ≠ 0 →
    GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      data.atomU data.atomV atomS →
    False

/-! ## Layer 9 — the narrowings and the discharges -/

/-- **THE RANK-FOUR NARROWING.**  The two narrowed residues close the
rank-four circuit residue.  A circuit label whose block misses a pair atom
dies at the off-pair residue.  A circuit label whose block carries the pair
has an independent pair restriction, thus a rank-one shifted gap block, and it
dies at the rank-one residue. -/
theorem rankFourOuterCircuitClosed_of_narrowed
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hone : RankFourOuterRankOneCircuitClosed) :
    RankFourOuterCircuitClosed := by
  classical
  intro crux data label hmem hpos hcircuit
  by_cases hUblock : data.atomU ∈ data.frame.activeSubset label
  · by_cases hVblock : data.atomV ∈ data.frame.activeSubset label
    · obtain ⟨atomS, hSU, hSV, hSblock, hSalive, hshape⟩ :=
        data.circuit_gap_rank_one hmem hUblock hVblock hcircuit
      exact hone crux data label atomS hmem hpos hcircuit hUblock hVblock hSU
        hSV hSblock hSalive hshape
    · exact hoff crux data label hmem hpos hcircuit (Or.inr hVblock)
  · exact hoff crux data label hmem hpos hcircuit (Or.inl hUblock)

/-- **THE RANK-FIVE NARROWING.** -/
theorem rankFiveOuterCircuitClosed_of_narrowed
    (hoff : RankFiveOuterOffPairCircuitClosed)
    (hone : RankFiveOuterRankOneCircuitClosed) :
    RankFiveOuterCircuitClosed := by
  classical
  intro crux data label hmem hpos hcircuit
  by_cases hUblock : data.atomU ∈ data.frame.activeSubset label
  · by_cases hVblock : data.atomV ∈ data.frame.activeSubset label
    · obtain ⟨atomS, hSU, hSV, hSblock, hSalive, hshape⟩ :=
        data.circuit_gap_rank_one hmem hUblock hVblock hcircuit
      exact hone crux data label atomS hmem hpos hcircuit hUblock hVblock hSU
        hSV hSblock hSalive hshape
    · exact hoff crux data label hmem hpos hcircuit (Or.inr hVblock)
  · exact hoff crux data label hmem hpos hcircuit (Or.inl hUblock)

/-- **THE RANK-SIX NARROWING.** -/
theorem rankSixOuterCircuitClosed_of_narrowed
    (hoff : RankSixOuterOffPairCircuitClosed)
    (hone : RankSixOuterRankOneCircuitClosed) :
    RankSixOuterCircuitClosed := by
  classical
  intro crux data label hmem hpos hcircuit
  by_cases hUblock : data.atomU ∈ data.frame.activeSubset label
  · by_cases hVblock : data.atomV ∈ data.frame.activeSubset label
    · obtain ⟨atomS, hSU, hSV, hSblock, hSalive, hshape⟩ :=
        data.circuit_gap_rank_one hmem hUblock hVblock hcircuit
      exact hone crux data label atomS hmem hpos hcircuit hUblock hVblock hSU
        hSV hSblock hSalive hshape
    · exact hoff crux data label hmem hpos hcircuit (Or.inr hVblock)
  · exact hoff crux data label hmem hpos hcircuit (Or.inl hUblock)

/-- **THE RANK-FOUR OUTER KILL.**  The two narrowed residues and the interior
residue at the three-plus-carrier atoms kill every rank-four outer datum. -/
theorem rankFourOuterKilled_of_narrowed_interior
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hone : RankFourOuterRankOneCircuitClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourOuterKilled :=
  rankFourOuterKilled_of_circuit_interior
    (rankFourOuterCircuitClosed_of_narrowed hoff hone) hinterior

/-- **THE RANK-FOUR DISCHARGE.**  Closure one of the rank-four rung follows
from the two narrowed residues and the interior residue. -/
theorem rankFourSupportTwoClosed_of_narrowed_interior
    (hoff : RankFourOuterOffPairCircuitClosed)
    (hone : RankFourOuterRankOneCircuitClosed)
    (hinterior : ∀ (crux : SixThreeCrux) (data : RankFourOuterData crux)
      (atomIndex : Fin 6),
      2 < (blockCarrier data.frame.activeSubset data.frame.basisLabel
        atomIndex).card →
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex) :
    RankFourSupportTwoClosed :=
  rankFourSupportTwoClosed_of_outer_killed
    (rankFourOuterKilled_of_narrowed_interior hoff hone hinterior)

/-- **THE RANK-FIVE DISCHARGE.**  Closure one of the second rung follows from
the two narrowed residues and the refined profile data. -/
theorem rankFiveSupportTwoClosed_of_narrowed_refined
    (hoff : RankFiveOuterOffPairCircuitClosed)
    (hone : RankFiveOuterRankOneCircuitClosed)
    (hprofile : ∀ (crux : SixThreeCrux) (data : RankFiveOuterData crux),
      ∃ pinSet pairSet : Finset (Fin 6), Disjoint pinSet pairSet
        ∧ (∀ atom ∈ pinSet, ∃ pinSlot,
            blockCarrier data.frame.activeSubset data.frame.basisLabel atom
              = {pinSlot})
        ∧ (∀ atom ∈ pairSet, ∃ slotOne slotTwo, slotOne ≠ slotTwo ∧
            blockCarrier data.frame.activeSubset data.frame.basisLabel atom
              = {slotOne, slotTwo})
        ∧ (∀ atom, atom ∉ pinSet → atom ∉ pairSet →
            0 < chartObjective (chartPointOfDesign crux.design)
              + (chartPointOfDesign crux.design).weight atom)
        ∧ (Matrix.trace data.frame.coeff = 2 → 1 ≤ pinSet.card)
        ∧ (Matrix.trace data.frame.coeff = 3 →
            4 ≤ 2 * pinSet.card + pairSet.card)) :
    RankFiveSupportTwoClosed := by
  refine rankFiveSupportTwoClosed_of_outer_killed ?_
  intro crux data
  obtain ⟨pinSet, pairSet, hdisjoint, hpinSet, hpairSet, hint, htwo, hthree⟩ :=
    hprofile crux data
  exact data.false_of_circuitClosed_refined
    (rankFiveOuterCircuitClosed_of_narrowed hoff hone) pinSet pairSet hdisjoint
    hpinSet hpairSet hint htwo hthree

/-- **THE RANK-SIX DISCHARGE.**  Closure one of the third rung follows from
the two narrowed residues and the landed low-profile residue. -/
theorem rankSixSupportTwoClosed_of_narrowed_lowProfile
    (hoff : RankSixOuterOffPairCircuitClosed)
    (hone : RankSixOuterRankOneCircuitClosed)
    (hlow : RankSixOuterLowProfileClosed) :
    RankSixSupportTwoClosed :=
  rankSixSupportTwoClosed_of_circuit_and_lowProfile
    (rankSixOuterCircuitClosed_of_narrowed hoff hone) hlow

/-! ## Layer 10 — the null family of a rank-one gap block -/

section NullFamily

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- The left cross entry of a rank-one gap block is alive: its square is the
product of two positive shifted diagonals. -/
theorem gap_rankOne_cross_ne_zero
    (hvalueNeg : value < 0) {atomU atomV atomS : Fin size}
    (hfloorU : 0 < chartStationaryGap projection weight atomU atomU)
    (hfloorV : 0 < chartStationaryGap projection weight atomV atomV)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    chartStationaryGap projection weight atomU atomV ≠ 0 := by
  intro hzero
  have hUV := hshape.1
  rw [hzero] at hUV
  nlinarith [hUV, hfloorU, hfloorV, hvalueNeg]

/-- The right cross entry of a rank-one gap block is alive. -/
theorem gap_rankOne_side_ne_zero
    (hvalueNeg : value < 0) {atomU atomV atomS : Fin size}
    (hfloorU : 0 < chartStationaryGap projection weight atomU atomU)
    (hfloorS : 0 < chartStationaryGap projection weight atomS atomS)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    chartStationaryGap projection weight atomU atomS ≠ 0 := by
  intro hzero
  have hUS := hshape.2.1
  rw [hzero] at hUS
  nlinarith [hUS, hfloorU, hfloorS, hvalueNeg]

/-- **THE FOUR-ATOM NULL LAW.**  Once the shifted gap block on three atoms is
a rank-one square, a direction supported on the first pair is tight at the
third atom as well, although that atom can sit outside its block.  The pair
column of an outer datum thus carries one tight row more than its block
supplies. -/
theorem gap_pair_tight_at_third_of_rankOne
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalueNeg : value < 0) {atomU atomV atomS : Fin size}
    (hUV : atomU ≠ atomV) (hSU : atomS ≠ atomU) (hSV : atomS ≠ atomV)
    (hfloorU : 0 < chartStationaryGap projection weight atomU atomU)
    (hfloorV : 0 < chartStationaryGap projection weight atomV atomV)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS)
    {label : activeIndex} (hmem : label ∈ activeSet)
    (hUmem : atomU ∈ activeSubset label) (hVmem : atomV ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      tightDir label atomIndex = 0) :
    (chartStationaryGap projection weight *ᵥ tightDir label) atomS
      = value * tightDir label atomS := by
  have hDne := gap_rankOne_cross_ne_zero hvalueNeg hfloorU hfloorV hshape
  have hUUmin := hshape.2.2.2.1
  have hVVmin := hshape.2.2.2.2.1
  have hrowU := hdata.tightDir_isTight label hmem atomU hUmem
  have hrowV := hdata.tightDir_isTight label hmem atomV hVmem
  rw [mulVec_apply_of_pair_support _ hUV hsupp atomU] at hrowU
  rw [mulVec_apply_of_pair_support _ hUV hsupp atomV] at hrowV
  rw [chartStationaryGap_entry_symm hdata atomV atomU] at hrowV
  have hzeroS : tightDir label atomS = 0 := hsupp atomS hSU hSV
  rw [mulVec_apply_of_pair_support _ hUV hsupp atomS,
    chartStationaryGap_entry_symm hdata atomS atomU,
    chartStationaryGap_entry_symm hdata atomS atomV, hzeroS, mul_zero]
  have hprod : chartStationaryGap projection weight atomU atomV
      * (chartStationaryGap projection weight atomU atomS
          * tightDir label atomU
        + chartStationaryGap projection weight atomV atomS
          * tightDir label atomV) = 0 := by
    linear_combination (-(tightDir label atomU) / 2) * hUUmin
      - (tightDir label atomV / 2) * hVVmin
      + (chartStationaryGap projection weight atomV atomS / 2) * hrowU
      + (chartStationaryGap projection weight atomU atomS / 2) * hrowV
  exact (mul_eq_zero.mp hprod).resolve_left hDne

/-- **THE PAIR NULL FAMILY.**  A rank-one shifted gap block carries an
explicit null direction on the outer pair of its three atoms.  The direction
is the cross entry at the left atom and the negative shifted diagonal at the
third atom, it vanishes elsewhere, and it is tight at all three block
atoms. -/
theorem exists_pair_null_of_rankOne_block
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (hvalueNeg : value < 0) {atomU atomV atomS : Fin size}
    (hUV : atomU ≠ atomV) (hSU : atomS ≠ atomU) (hSV : atomS ≠ atomV)
    (hfloorU : 0 < chartStationaryGap projection weight atomU atomU)
    (hfloorS : 0 < chartStationaryGap projection weight atomS atomS)
    (hshape : GapBlockRankOne projection weight value atomU atomV atomS) :
    ∃ nullVec : Fin size → ℝ,
      nullVec atomU = chartStationaryGap projection weight atomU atomS
      ∧ nullVec atomS
          = value - chartStationaryGap projection weight atomU atomU
      ∧ nullVec atomU ≠ 0 ∧ nullVec atomS ≠ 0
      ∧ (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomS →
          nullVec atomIndex = 0)
      ∧ (chartStationaryGap projection weight *ᵥ nullVec) atomU
          = value * nullVec atomU
      ∧ (chartStationaryGap projection weight *ᵥ nullVec) atomV
          = value * nullVec atomV
      ∧ (chartStationaryGap projection weight *ᵥ nullVec) atomS
          = value * nullVec atomS := by
  classical
  have hUSmin := hshape.2.1
  have hUUmin := hshape.2.2.2.1
  have hEne := gap_rankOne_side_ne_zero hvalueNeg hfloorU hfloorS hshape
  obtain ⟨nullVec, hvalU, hvalS, hvalOther⟩ :
      ∃ nullVec : Fin size → ℝ,
        nullVec atomU = chartStationaryGap projection weight atomU atomS
        ∧ nullVec atomS
            = value - chartStationaryGap projection weight atomU atomU
        ∧ ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomS →
            nullVec atomIndex = 0 :=
    ⟨fun atomIndex =>
      if atomIndex = atomU then chartStationaryGap projection weight atomU atomS
      else if atomIndex = atomS then
        value - chartStationaryGap projection weight atomU atomU
      else 0, by simp, by simp [hSU], fun atomIndex hU hS => by simp [hU, hS]⟩
  refine ⟨nullVec, hvalU, hvalS, ?_, ?_, hvalOther, ?_, ?_, ?_⟩
  · rw [hvalU]
    exact hEne
  · rw [hvalS]
    intro hzero
    linarith
  · rw [mulVec_apply_of_pair_support _ hSU.symm hvalOther atomU, hvalU, hvalS]
    ring
  · rw [mulVec_apply_of_pair_support _ hSU.symm hvalOther atomV, hvalU, hvalS,
      hvalOther atomV hUV.symm hSV.symm,
      chartStationaryGap_entry_symm hdata atomV atomU]
    linear_combination -hUUmin
  · rw [mulVec_apply_of_pair_support _ hSU.symm hvalOther atomS, hvalU, hvalS,
      chartStationaryGap_entry_symm hdata atomS atomU]
    linear_combination hUSmin

/-- **THE PAIR NULL KILL.**  Two vectors supported inside one atom pair, each
with a tight row at the left atom and with an independent pair restriction,
force the gap diagonal at the left atom to the value, against the floor.  The
law consumes no label, thus it applies to the null family. -/
theorem false_of_pair_null_independent
    (hvalueNeg : value < 0) {atomU atomV : Fin size} (hUV : atomU ≠ atomV)
    {vecOne vecTwo : Fin size → ℝ}
    (hsuppOne : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      vecOne atomIndex = 0)
    (hsuppTwo : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      vecTwo atomIndex = 0)
    (hrowOne : (chartStationaryGap projection weight *ᵥ vecOne) atomU
      = value * vecOne atomU)
    (hrowTwo : (chartStationaryGap projection weight *ᵥ vecTwo) atomU
      = value * vecTwo atomU)
    (hdet : vecOne atomU * vecTwo atomV - vecOne atomV * vecTwo atomU ≠ 0)
    (hfloor : 0 < chartStationaryGap projection weight atomU atomU) :
    False := by
  rw [mulVec_apply_of_pair_support _ hUV hsuppOne atomU] at hrowOne
  rw [mulVec_apply_of_pair_support _ hUV hsuppTwo atomU] at hrowTwo
  have hcancel : (chartStationaryGap projection weight atomU atomU - value)
      * (vecOne atomU * vecTwo atomV - vecOne atomV * vecTwo atomU) = 0 := by
    linear_combination (vecTwo atomV) * hrowOne - (vecOne atomV) * hrowTwo
  have hdiag := (mul_eq_zero.mp hcancel).resolve_right hdet
  linarith

end NullFamily

/-! ## Layer 11 — the rank-one readings at the rank-four outer datum -/

/-- **THE RANK-FOUR FOUR-ATOM NULL LAW.**  At a rank-four outer datum whose
circuit label gives a rank-one shifted gap block, the pair column is tight at
the circuit label's third block atom. -/
theorem RankFourOuterData.pair_column_tight_at_rankOne_atom
    {crux : SixThreeCrux} (data : RankFourOuterData crux) {atomS : Fin 6}
    (hSU : atomS ≠ data.atomU) (hSV : atomS ≠ data.atomV)
    (hshape : GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      data.atomU data.atomV atomS) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
      *ᵥ data.frame.tightDir (data.frame.basisLabel data.columnIndex)) atomS
      = chartObjective (chartPointOfDesign crux.design)
        * data.frame.tightDir (data.frame.basisLabel data.columnIndex)
          atomS := by
  have hUblock : data.atomU
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneU (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomU hout)
  have hVblock : data.atomV
      ∈ data.frame.activeSubset (data.frame.basisLabel data.columnIndex) := by
    by_contra hout
    exact data.hneV (data.frame.hdata.tightDir_support _
      (data.frame.hmemAll data.columnIndex) data.atomV hout)
  exact gap_pair_tight_at_third_of_rankOne data.frame.hdata
    data.frame.hvalueNeg data.hUV hSU hSV
    (crux.gap_diagonal_pos_of_allHeavy data.atomU)
    (crux.gap_diagonal_pos_of_allHeavy data.atomV) hshape
    (data.frame.hmemAll data.columnIndex) hUblock hVblock data.hsupp

/-- **THE RANK-FOUR NULL FAMILY.**  At a rank-four outer datum whose circuit
label gives a rank-one shifted gap block, the block carries an explicit null
direction on the outer pair. -/
theorem RankFourOuterData.exists_pair_null_of_rankOne
    {crux : SixThreeCrux} (data : RankFourOuterData crux) {atomS : Fin 6}
    (hSU : atomS ≠ data.atomU) (hSV : atomS ≠ data.atomV)
    (hshape : GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      data.atomU data.atomV atomS) :
    ∃ nullVec : Fin 6 → ℝ,
      nullVec data.atomU
          = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight data.atomU atomS
      ∧ nullVec atomS = chartObjective (chartPointOfDesign crux.design)
          - chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight data.atomU data.atomU
      ∧ nullVec data.atomU ≠ 0 ∧ nullVec atomS ≠ 0
      ∧ (∀ atomIndex, atomIndex ≠ data.atomU → atomIndex ≠ atomS →
          nullVec atomIndex = 0)
      ∧ (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight *ᵥ nullVec) data.atomU
          = chartObjective (chartPointOfDesign crux.design)
            * nullVec data.atomU
      ∧ (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight *ᵥ nullVec) data.atomV
          = chartObjective (chartPointOfDesign crux.design)
            * nullVec data.atomV
      ∧ (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight *ᵥ nullVec) atomS
          = chartObjective (chartPointOfDesign crux.design) * nullVec atomS :=
  exists_pair_null_of_rankOne_block data.frame.hdata data.frame.hvalueNeg
    data.hUV hSU hSV (crux.gap_diagonal_pos_of_allHeavy data.atomU)
    (crux.gap_diagonal_pos_of_allHeavy atomS) hshape

/-- **THE RANK-ONE PAIR RIGIDITY.**  Every direction supported inside the
outer pair of a rank-one block, with a tight row at the left atom, is a
multiple of the null direction of that pair.  A second independent direction
dies at the gap floor. -/
theorem RankFourOuterData.false_of_rankOne_pair_independent
    {crux : SixThreeCrux} (data : RankFourOuterData crux) {atomS : Fin 6}
    (hSU : atomS ≠ data.atomU) (hSV : atomS ≠ data.atomV)
    (hshape : GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      data.atomU data.atomV atomS)
    {vecOne : Fin 6 → ℝ}
    (hsuppOne : ∀ atomIndex, atomIndex ≠ data.atomU → atomIndex ≠ atomS →
      vecOne atomIndex = 0)
    (hrowOne : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight *ᵥ vecOne) data.atomU
      = chartObjective (chartPointOfDesign crux.design) * vecOne data.atomU)
    (hdet : vecOne data.atomU
          * (chartObjective (chartPointOfDesign crux.design)
            - chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight data.atomU data.atomU)
        - vecOne atomS
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight data.atomU atomS ≠ 0) :
    False := by
  obtain ⟨nullVec, hvalU, hvalS, _, _, hnullSupp, hrowU, _, _⟩ :=
    data.exists_pair_null_of_rankOne hSU hSV hshape
  refine false_of_pair_null_independent data.frame.hvalueNeg hSU.symm hsuppOne
    hnullSupp hrowOne hrowU ?_
    (crux.gap_diagonal_pos_of_allHeavy data.atomU)
  rw [hvalU, hvalS]
  exact hdet

end Gtz
