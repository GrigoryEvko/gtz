import Gtz.Wave.StationaryFinThreeReindex
import Gtz.Wave.PositiveSupportTwoBlockExit
import Gtz.Quantitative.ActiveOverlapPatternsSixThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {projection : Matrix (Fin 6) (Fin 6) ℝ}
variable {weight : Fin 6 → ℝ} {value : ℝ}
variable {activeSubset : Fin 3 → Finset (Fin 6)}
variable {activeWeight : Fin 3 → ℝ}
variable {tightDir : Fin 3 → Fin 6 → ℝ}

/-- The atoms owned by each member of an ordered three-block family. -/
def threeBlockPrivateAtomSet
    (activeSubset : Fin 3 → Finset (Fin 6)) : Fin 3 → Finset (Fin 6) :=
  ![blockPrivatePart (activeSubset 0) (activeSubset 1) (activeSubset 2),
    blockPrivatePart (activeSubset 1) (activeSubset 0) (activeSubset 2),
    blockPrivatePart (activeSubset 2) (activeSubset 0) (activeSubset 1)]

theorem hasPrivateAtomSystem_threeBlockPrivateAtomSet
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) activeSubset activeWeight tightDir) :
    HasPrivateAtomSystem (Finset.univ : Finset (Fin 3)) tightDir
      (threeBlockPrivateAtomSet activeSubset) := by
  apply hasPrivateAtomSystem_of_notMem_activeSubset hdata
  intro ownerLabel _ atomIndex hatomMem otherLabel _ hne
  fin_cases ownerLabel
  · simp [threeBlockPrivateAtomSet, blockPrivatePart] at hatomMem
    fin_cases otherLabel
    · exact (hne rfl).elim
    · exact hatomMem.2.1
    · exact hatomMem.2.2
  · simp [threeBlockPrivateAtomSet, blockPrivatePart] at hatomMem
    fin_cases otherLabel
    · exact hatomMem.2.1
    · exact (hne rfl).elim
    · exact hatomMem.2.2
  · simp [threeBlockPrivateAtomSet, blockPrivatePart] at hatomMem
    fin_cases otherLabel
    · exact hatomMem.2.1
    · exact hatomMem.2.2
    · exact (hne rfl).elim

theorem union_three_activeSubset_eq_univ
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) activeSubset activeWeight tightDir) :
    activeSubset 0 ∪ activeSubset 1 ∪ activeSubset 2 = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro atomIndex _
  obtain ⟨activeLabel, _, hatomMem⟩ :=
    exists_mem_activeSubset_of_isChartStationaryData hdata atomIndex
  fin_cases activeLabel
  · change atomIndex ∈ activeSubset 0 at hatomMem
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hatomMem)
  · change atomIndex ∈ activeSubset 1 at hatomMem
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hatomMem)
  · change atomIndex ∈ activeSubset 2 at hatomMem
    exact Finset.mem_union_right _ hatomMem

/-- If no two of three distinct covering triples are disjoint, every block
owns an atom.  The private-mass dichotomy then excludes the open negative
stationary window. -/
theorem zero_le_value_of_finThree_noDisjoint
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) activeSubset activeWeight tightDir)
    (hzeroOne : activeSubset 0 ≠ activeSubset 1)
    (hzeroTwo : activeSubset 0 ≠ activeSubset 2)
    (honeTwo : activeSubset 1 ≠ activeSubset 2)
    (hnotDisjointZeroOne : ¬ Disjoint (activeSubset 0) (activeSubset 1))
    (hnotDisjointZeroTwo : ¬ Disjoint (activeSubset 0) (activeSubset 2))
    (hnotDisjointOneTwo : ¬ Disjoint (activeSubset 1) (activeSubset 2))
    (hvalueFloor : -(1 / 6 : ℝ) < value) :
    0 ≤ value := by
  have hcardZero := hdata.activeSubset_card 0 (Finset.mem_univ _)
  have hcardOne := hdata.activeSubset_card 1 (Finset.mem_univ _)
  have hcardTwo := hdata.activeSubset_card 2 (Finset.mem_univ _)
  have hcover := union_three_activeSubset_eq_univ hdata
  have hmeetZeroOne : 1 ≤ (activeSubset 0 ∩ activeSubset 1).card := by
    obtain ⟨atomIndex, hzero, hone⟩ := Finset.not_disjoint_iff.mp hnotDisjointZeroOne
    exact Finset.card_pos.mpr ⟨atomIndex, Finset.mem_inter.mpr ⟨hzero, hone⟩⟩
  have hmeetZeroTwo : 1 ≤ (activeSubset 0 ∩ activeSubset 2).card := by
    obtain ⟨atomIndex, hzero, htwo⟩ := Finset.not_disjoint_iff.mp hnotDisjointZeroTwo
    exact Finset.card_pos.mpr ⟨atomIndex, Finset.mem_inter.mpr ⟨hzero, htwo⟩⟩
  have hmeetOneTwo : 1 ≤ (activeSubset 1 ∩ activeSubset 2).card := by
    obtain ⟨atomIndex, hone, htwo⟩ := Finset.not_disjoint_iff.mp hnotDisjointOneTwo
    exact Finset.card_pos.mpr ⟨atomIndex, Finset.mem_inter.mpr ⟨hone, htwo⟩⟩
  have hboundZeroOne :=
    card_inter_lt_of_card_eq_of_ne hcardZero hcardOne hzeroOne
  have hboundZeroTwo :=
    card_inter_lt_of_card_eq_of_ne hcardZero hcardTwo hzeroTwo
  have hboundOneTwo :=
    card_inter_lt_of_card_eq_of_ne hcardOne hcardTwo honeTwo
  have htotal := pairwiseOverlapSum_eq_of_covering_sixThree
    hcardZero hcardOne hcardTwo hcover
  have hsplitZero := card_blockPrivatePart_add_pairwise
    (activeSubset 0) (activeSubset 1) (activeSubset 2)
  have hsplitOne := card_blockPrivatePart_add_pairwise_second
    (activeSubset 0) (activeSubset 1) (activeSubset 2)
  have hsplitTwo := card_blockPrivatePart_add_pairwise_third
    (activeSubset 0) (activeSubset 1) (activeSubset 2)
  have hprivateZero :
      (blockPrivatePart (activeSubset 0) (activeSubset 1) (activeSubset 2)).Nonempty := by
    rw [← Finset.card_pos]
    rw [pairwiseOverlapSum] at htotal
    omega
  have hprivateOne :
      (blockPrivatePart (activeSubset 1) (activeSubset 0) (activeSubset 2)).Nonempty := by
    rw [← Finset.card_pos]
    rw [pairwiseOverlapSum] at htotal
    omega
  have hprivateTwo :
      (blockPrivatePart (activeSubset 2) (activeSubset 0) (activeSubset 1)).Nonempty := by
    rw [← Finset.card_pos]
    rw [pairwiseOverlapSum] at htotal
    omega
  have hprivate := hasPrivateAtomSystem_threeBlockPrivateAtomSet hdata
  have hnonempty : ∀ activeLabel ∈ (Finset.univ : Finset (Fin 3)),
      (threeBlockPrivateAtomSet activeSubset activeLabel).Nonempty := by
    intro activeLabel _
    fin_cases activeLabel
    · exact hprivateZero
    · exact hprivateOne
    · exact hprivateTwo
  rcases value_eq_neg_inv_size_or_zero_le_of_hasPrivateAtomSystem hdata hprivate hnonempty with
      hendpoint | hnonneg
  · norm_num at hendpoint
    linarith
  · exact hnonneg

/-- If rows `1` and `2` sit on disjoint triples, each owns an atom not used by
row `0`.  Their multipliers therefore have the `1/6` floor, their directions
are orthogonal, and the three-row captured-trace dichotomy excludes a negative
value above `-1/6`. -/
theorem zero_le_value_of_finThree_disjoint_lastPair
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) activeSubset activeWeight tightDir)
    (hzeroOne : activeSubset 0 ≠ activeSubset 1)
    (hzeroTwo : activeSubset 0 ≠ activeSubset 2)
    (hdisjoint : Disjoint (activeSubset 1) (activeSubset 2))
    (hactiveWeightPositive : ∀ activeLabel : Fin 3, 0 < activeWeight activeLabel)
    (hvalueFloor : -(1 / 6 : ℝ) < value) :
    0 ≤ value := by
  have hcardZero := hdata.activeSubset_card 0 (Finset.mem_univ _)
  have hcardOne := hdata.activeSubset_card 1 (Finset.mem_univ _)
  have hcardTwo := hdata.activeSubset_card 2 (Finset.mem_univ _)
  have hprivateOne :
      (blockPrivatePart (activeSubset 1) (activeSubset 0) (activeSubset 2)).Nonempty := by
    have hnotSubset : ¬ activeSubset 1 ⊆ activeSubset 0 := by
      intro hsubset
      exact hzeroOne (Finset.eq_of_subset_of_card_le hsubset (by omega)).symm
    obtain ⟨atomIndex, hone, hnotZero⟩ := Finset.not_subset.mp hnotSubset
    have hnotTwo : atomIndex ∉ activeSubset 2 := by
      exact fun htwo => Finset.disjoint_left.mp hdisjoint hone htwo
    exact ⟨atomIndex, by simp [blockPrivatePart, hone, hnotZero, hnotTwo]⟩
  have hprivateTwo :
      (blockPrivatePart (activeSubset 2) (activeSubset 0) (activeSubset 1)).Nonempty := by
    have hnotSubset : ¬ activeSubset 2 ⊆ activeSubset 0 := by
      intro hsubset
      exact hzeroTwo (Finset.eq_of_subset_of_card_le hsubset (by omega)).symm
    obtain ⟨atomIndex, htwo, hnotZero⟩ := Finset.not_subset.mp hnotSubset
    have hnotOne : atomIndex ∉ activeSubset 1 := by
      exact fun hone => Finset.disjoint_left.mp hdisjoint hone htwo
    exact ⟨atomIndex, by simp [blockPrivatePart, htwo, hnotZero, hnotOne]⟩
  have hprivate := hasPrivateAtomSystem_threeBlockPrivateAtomSet hdata
  have honeFloorRaw := card_mul_inv_size_le_activeWeight_of_privateAtomSet hdata hprivate
    (ownerLabel := (1 : Fin 3)) (Finset.mem_univ _)
  have htwoFloorRaw := card_mul_inv_size_le_activeWeight_of_privateAtomSet hdata hprivate
    (ownerLabel := (2 : Fin 3)) (Finset.mem_univ _)
  have honeCard : 1 ≤ (threeBlockPrivateAtomSet activeSubset 1).card := by
    exact Finset.card_pos.mpr hprivateOne
  have htwoCard : 1 ≤ (threeBlockPrivateAtomSet activeSubset 2).card := by
    exact Finset.card_pos.mpr hprivateTwo
  have honeCast : (1 : ℝ) ≤ ((threeBlockPrivateAtomSet activeSubset 1).card : ℝ) := by
    exact_mod_cast honeCard
  have htwoCast : (1 : ℝ) ≤ ((threeBlockPrivateAtomSet activeSubset 2).card : ℝ) := by
    exact_mod_cast htwoCard
  have honeFloor : (6 : ℝ)⁻¹ ≤ activeWeight 1 := by
    have hstep : (6 : ℝ)⁻¹
        ≤ ((threeBlockPrivateAtomSet activeSubset 1).card : ℝ) * (6 : ℝ)⁻¹ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right honeCast (by positivity : (0 : ℝ) ≤ (6 : ℝ)⁻¹)
    exact hstep.trans honeFloorRaw
  have htwoFloor : (6 : ℝ)⁻¹ ≤ activeWeight 2 := by
    have hstep : (6 : ℝ)⁻¹
        ≤ ((threeBlockPrivateAtomSet activeSubset 2).card : ℝ) * (6 : ℝ)⁻¹ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right htwoCast (by positivity : (0 : ℝ) ≤ (6 : ℝ)⁻¹)
    exact hstep.trans htwoFloorRaw
  have horthogonal : tightDir 1 ⬝ᵥ tightDir 2 = 0 := by
    rw [dotProduct]
    apply Finset.sum_eq_zero
    intro atomIndex _
    by_cases hone : atomIndex ∈ activeSubset 1
    · have hnotTwo : atomIndex ∉ activeSubset 2 :=
        fun htwo => Finset.disjoint_left.mp hdisjoint hone htwo
      rw [hdata.tightDir_support 2 (Finset.mem_univ _) atomIndex hnotTwo, mul_zero]
    · rw [hdata.tightDir_support 1 (Finset.mem_univ _) atomIndex hone, zero_mul]
  apply value_nonneg_of_three_active_rows_of_two_orthogonal_floored_rows hdata
  · norm_num at hvalueFloor ⊢
    linarith
  · exact hactiveWeightPositive
  · exact honeFloor
  · exact htwoFloor
  · exact horthogonal

/-- **EVERY SIMPLE THREE-BLOCK STATIONARY DATUM IS CLOSED ABOVE `-1/6`.**
If a pair is disjoint, relabel that pair into slots `1,2` and use the captured
trace theorem.  If no pair is disjoint, use private mass on all three rows. -/
theorem zero_le_value_of_finThree_distinct
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) activeSubset activeWeight tightDir)
    (hzeroOne : activeSubset 0 ≠ activeSubset 1)
    (hzeroTwo : activeSubset 0 ≠ activeSubset 2)
    (honeTwo : activeSubset 1 ≠ activeSubset 2)
    (hactiveWeightPositive : ∀ activeLabel : Fin 3, 0 < activeWeight activeLabel)
    (hvalueFloor : -(1 / 6 : ℝ) < value) :
    0 ≤ value := by
  by_cases honeTwoDisjoint : Disjoint (activeSubset 1) (activeSubset 2)
  · exact zero_le_value_of_finThree_disjoint_lastPair hdata hzeroOne hzeroTwo
      honeTwoDisjoint hactiveWeightPositive hvalueFloor
  by_cases hzeroOneDisjoint : Disjoint (activeSubset 0) (activeSubset 1)
  · have hdata' := isChartStationaryData_finThreeReindex hdata
      (2 : Fin 3) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide) (by decide)
      (by decide)
    apply zero_le_value_of_finThree_disjoint_lastPair hdata'
    · simpa using hzeroTwo.symm
    · simpa using honeTwo.symm
    · simpa using hzeroOneDisjoint
    · intro activeLabel
      fin_cases activeLabel
      · simpa using hactiveWeightPositive 2
      · simpa using hactiveWeightPositive 0
      · simpa using hactiveWeightPositive 1
    · exact hvalueFloor
  by_cases hzeroTwoDisjoint : Disjoint (activeSubset 0) (activeSubset 2)
  · have hdata' := isChartStationaryData_finThreeReindex hdata
      (1 : Fin 3) (0 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
      (by decide)
    apply zero_le_value_of_finThree_disjoint_lastPair hdata'
    · simpa using hzeroOne.symm
    · simpa using honeTwo
    · simpa using hzeroTwoDisjoint
    · intro activeLabel
      fin_cases activeLabel
      · simpa using hactiveWeightPositive 1
      · simpa using hactiveWeightPositive 0
      · simpa using hactiveWeightPositive 2
    · exact hvalueFloor
  exact zero_le_value_of_finThree_noDisjoint hdata hzeroOne hzeroTwo honeTwo
    hzeroOneDisjoint hzeroTwoDisjoint honeTwoDisjoint hvalueFloor

/-- **A SIMPLE STATIONARY ASSEMBLY CANNOT USE EXACTLY THREE POSITIVE
MULTIPLIERS AT A NEGATIVE VALUE ABOVE `-1/6`.**  Zero-multiplier rows are first
discarded; the remaining three labels are reindexed by `Fin 3` and fed to the
coordinate-free three-block closure. -/
theorem zero_le_value_of_positiveActiveSet_card_three
    {activeIndex : Type*} [DecidableEq activeIndex]
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hcard : (positiveActiveSet activeSet activeWeight).card = 3)
    (hsimple : HasSimpleActiveSubsets activeSet activeSubset)
    (hvalueFloor : -(1 / 6 : ℝ) < value) :
    0 ≤ value := by
  let positiveSet := positiveActiveSet activeSet activeWeight
  have hrestricted := hdata.restrict_positiveActiveSet
  obtain ⟨firstLabel, middleLabel, lastLabel, hfirstMiddle, hfirstLast, hmiddleLast,
      hpositiveSet⟩ := Finset.card_eq_three.mp hcard
  have hfirstMem : firstLabel ∈ positiveSet := by
    change firstLabel ∈ positiveActiveSet activeSet activeWeight
    rw [hpositiveSet]
    simp
  have hmiddleMem : middleLabel ∈ positiveSet := by
    change middleLabel ∈ positiveActiveSet activeSet activeWeight
    rw [hpositiveSet]
    simp
  have hlastMem : lastLabel ∈ positiveSet := by
    change lastLabel ∈ positiveActiveSet activeSet activeWeight
    rw [hpositiveSet]
    simp
  have hdata' := isChartStationaryData_finThreeReindex hrestricted
    firstLabel middleLabel lastLabel hfirstMiddle hfirstLast hmiddleLast hpositiveSet
  apply zero_le_value_of_finThree_distinct hdata'
  · change activeSubset firstLabel ≠ activeSubset middleLabel
    intro heq
    exact hfirstMiddle (hsimple firstLabel (Finset.filter_subset _ _ hfirstMem)
      middleLabel (Finset.filter_subset _ _ hmiddleMem) heq)
  · change activeSubset firstLabel ≠ activeSubset lastLabel
    intro heq
    exact hfirstLast (hsimple firstLabel (Finset.filter_subset _ _ hfirstMem)
      lastLabel (Finset.filter_subset _ _ hlastMem) heq)
  · change activeSubset middleLabel ≠ activeSubset lastLabel
    intro heq
    exact hmiddleLast (hsimple middleLabel (Finset.filter_subset _ _ hmiddleMem)
      lastLabel (Finset.filter_subset _ _ hlastMem) heq)
  · intro activeLabel
    fin_cases activeLabel
    · exact (Finset.mem_filter.mp hfirstMem).2
    · exact (Finset.mem_filter.mp hmiddleMem).2
    · exact (Finset.mem_filter.mp hlastMem).2
  · exact hvalueFloor

/-- At a `(6,3)` crux, a simple stationary datum cannot have exactly three
positive multipliers. -/
theorem SixThreeCrux.positiveActiveSet_card_ne_three_of_simple
    (crux : SixThreeCrux)
    {activeIndex : Type*} [DecidableEq activeIndex]
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hsimple : HasSimpleActiveSubsets activeSet activeSubset) :
    (positiveActiveSet activeSet activeWeight).card ≠ 3 := by
  intro hcard
  have hfloor := neg_inv_size_lt_value_of_isChartStationaryData crux.design rfl
    crux.isChartArgmaxValue hdata
  have hnonneg := zero_le_value_of_positiveActiveSet_card_three hdata hcard hsimple (by
    norm_num at hfloor ⊢
    exact hfloor)
  exact (not_le.mpr crux.hasNegativeChartValue) hnonneg

/-- **A SIMPLE CRUX STATIONARY ASSEMBLY USES AT LEAST FOUR POSITIVE
MULTIPLIERS.**  The landed coverage/two-block argument gives three; the
coordinate-free three-block closure makes the inequality strict. -/
theorem SixThreeCrux.four_le_positiveActiveSet_card_of_simple
    (crux : SixThreeCrux)
    {activeIndex : Type*} [DecidableEq activeIndex]
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hsimple : HasSimpleActiveSubsets activeSet activeSubset) :
    4 ≤ (positiveActiveSet activeSet activeWeight).card := by
  have hthree := crux.three_le_positiveActiveSet_card hdata
  have hne := crux.positiveActiveSet_card_ne_three_of_simple hdata hsimple
  omega


end Gtz
