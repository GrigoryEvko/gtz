import Gtz.Wave.ThreeRowAmbientWrapper
import Gtz.Wave.SupportThreeNonzero
import Gtz.Wave.PositiveSupportTwoBlockExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- A three-element finite set containing two distinct specified elements has a
unique remaining element, up to the displayed enumeration. -/
theorem exists_third_of_card_three_of_mem_of_mem
    {alpha : Type*} [DecidableEq alpha] (family : Finset alpha)
    (hcard : family.card = 3) {first second : alpha}
    (hfirst : first ∈ family) (hsecond : second ∈ family)
    (hne : first ≠ second) :
    ∃ third, third ≠ first ∧ third ≠ second ∧
      family = {first, second, third} := by
  have hsecondErase : second ∈ family.erase first :=
    Finset.mem_erase.mpr ⟨hne.symm, hsecond⟩
  have heraseFirstCard : (family.erase first).card = 2 := by
    rw [Finset.card_erase_of_mem hfirst, hcard]
  have heraseBothCard : ((family.erase first).erase second).card = 1 := by
    rw [Finset.card_erase_of_mem hsecondErase, heraseFirstCard]
  obtain ⟨third, hthird⟩ := Finset.card_eq_one.mp heraseBothCard
  have hthirdMemBoth : third ∈ (family.erase first).erase second := by
    rw [hthird]
    simp
  have hthirdNeSecond : third ≠ second := (Finset.mem_erase.mp hthirdMemBoth).1
  have hthirdMemFirstErase : third ∈ family.erase first :=
    Finset.mem_of_mem_erase hthirdMemBoth
  have hthirdNeFirst : third ≠ first :=
    (Finset.mem_erase.mp hthirdMemFirstErase).1
  refine ⟨third, hthirdNeFirst, hthirdNeSecond, ?_⟩
  calc
    family = insert first (family.erase first) :=
      (Finset.insert_erase hfirst).symm
    _ = insert first (insert second ((family.erase first).erase second)) := by
      rw [Finset.insert_erase hsecondErase]
    _ = {first, second, third} := by rw [hthird]

/-- A zero total squared row is a zero ambient tight coordinate. -/
theorem ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (atomIndex : Fin 6)
    (hzero : totalEigenSquareRow tightVec selected atomIndex = 0) :
    ambientTightSelection tightVec selected atomIndex = 0 := by
  rw [totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hcard] at hzero
  exact mul_self_eq_zero.mp hzero

/-- **THE POSITIVE B-SIDE COLLAPSE.**  In the support-three branch, the active
complement has multiplier `1/2` and every other tight row is supported on the
selected triple.  If the selected full row and any other selected-side row both
have positive multiplier, the three-row spectral exit gives a contradiction.
No orbit classification of the remaining two active blocks is needed. -/
theorem SixThreeCrux.false_of_supportThree_complement_of_twoPositiveBside
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (block complementBlock pairBlock : Finset (Fin 6))
    (hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4)
    (hblockCard : block.card = 3) (hcomplementCard : blockᶜ.card = 3)
    (hsupportThree : (totalTightSupport tightVec block).card = 3)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hblockMem : block ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hcomplementMem : complementBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hpairMem : pairBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hcomplementEq : complementBlock = blockᶜ)
    (hpairNeBlock : pairBlock ≠ block)
    (hpairNeComplement : pairBlock ≠ complementBlock)
    (hcomplementRow : totalEigenSquareRow tightVec complementBlock =
      (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3))
    (hcomplementMultiplier : multiplier complementBlock = 1 / 2)
    (hotherZero : ∀ otherBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
        totalEigenSquareRow tightVec otherBlock atomIndex = 0)
    (hblockPositive : 0 < multiplier block)
    (hpairPositive : 0 < multiplier pairBlock) :
    False := by
  classical
  let family := chartArgmaxFamily (chartPointOfDesign crux.design)
  let selection := ambientTightSelection tightVec
  have hblockNeComplement : block ≠ complementBlock := by
    intro heq
    have hselfComplement : block = blockᶜ := heq.trans hcomplementEq
    have hzero := congrArg
      (fun selected : Finset (Fin 6) => (0 : Fin 6) ∈ selected) hselfComplement
    simp only [Finset.mem_compl] at hzero
    tauto
  have heraseCard : (family.erase complementBlock).card = 3 := by
    rw [Finset.card_erase_of_mem hcomplementMem, hfamilyCard]
  have hblockErase : block ∈ family.erase complementBlock := by
    exact Finset.mem_erase.mpr ⟨hblockNeComplement, hblockMem⟩
  have hpairErase : pairBlock ∈ family.erase complementBlock := by
    exact Finset.mem_erase.mpr ⟨hpairNeComplement, hpairMem⟩
  obtain ⟨extraBlock, hextraNeBlock, hextraNePair, heraseEq⟩ :=
    exists_third_of_card_three_of_mem_of_mem
      (family.erase complementBlock) heraseCard hblockErase hpairErase
        hpairNeBlock.symm
  have hextraMem : extraBlock ∈ family := by
    have : extraBlock ∈ family.erase complementBlock := by
      rw [heraseEq]
      simp
    exact Finset.mem_of_mem_erase this
  have hextraNeComplement : extraBlock ≠ complementBlock := by
    have : extraBlock ∈ family.erase complementBlock := by
      rw [heraseEq]
      simp
    exact (Finset.mem_erase.mp this).1
  have hfamilyEq : family = {complementBlock, block, pairBlock, extraBlock} := by
    calc
      family = insert complementBlock (family.erase complementBlock) :=
        (Finset.insert_erase hcomplementMem).symm
      _ = {complementBlock, block, pairBlock, extraBlock} := by rw [heraseEq]
  have hcomplementNotRest :
      complementBlock ∉ ({block, pairBlock, extraBlock} : Finset (Finset (Fin 6))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hblockNeComplement.symm,
      ⟨hpairNeComplement.symm, hextraNeComplement.symm⟩⟩
  have hblockNotRest :
      block ∉ ({pairBlock, extraBlock} : Finset (Finset (Fin 6))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpairNeBlock.symm, hextraNeBlock.symm⟩
  have hpairNotExtra :
      pairBlock ∉ ({extraBlock} : Finset (Finset (Fin 6))) := by
    simpa only [Finset.mem_singleton] using hextraNePair.symm
  have hpairCard : pairBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) pairBlock).mp hpairMem).1
  have hextraCard : extraBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) extraBlock).mp hextraMem).1
  have hcomplementBlockCard : complementBlock.card = 3 := by
    rw [hcomplementEq]
    exact hcomplementCard
  let full := selection block
  let complement := selection complementBlock
  let pair : Fin 3 → ℝ := fun blockIndex =>
    selection pairBlock (block.orderEmbOfFin hblockCard blockIndex)
  let extra : Fin 3 → ℝ := fun blockIndex =>
    selection extraBlock (block.orderEmbOfFin hblockCard blockIndex)
  let fullWeight := multiplier block
  let pairWeight := multiplier pairBlock
  let extraWeight := multiplier extraBlock
  have htightFullRaw : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block full := by
    exact
      { isUnit := hdata.tightDir_unit block hblockMem
        hasSupport := hdata.tightDir_support block hblockMem
        isTight := hdata.tightDir_isTight block hblockMem }
  have htightComplementRaw : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) complementBlock complement := by
    exact
      { isUnit := hdata.tightDir_unit complementBlock hcomplementMem
        hasSupport := hdata.tightDir_support complementBlock hcomplementMem
        isTight := hdata.tightDir_isTight complementBlock hcomplementMem }
  have htightComplement : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) blockᶜ complement := by
    simpa only [hcomplementEq] using htightComplementRaw
  have hfullZeroOff : ∀ atomIndex, atomIndex ∉ block → full atomIndex = 0 :=
    htightFullRaw.hasSupport
  have hpairZeroOff : ∀ atomIndex, atomIndex ∉ block →
      selection pairBlock atomIndex = 0 := by
    intro atomIndex hnotMem
    exact ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero
      tightVec pairBlock hpairCard atomIndex
        (hotherZero pairBlock hpairMem hpairNeComplement atomIndex hnotMem)
  have hextraZeroOff : ∀ atomIndex, atomIndex ∉ block →
      selection extraBlock atomIndex = 0 := by
    intro atomIndex hnotMem
    exact ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero
      tightVec extraBlock hextraCard atomIndex
        (hotherZero extraBlock hextraMem hextraNeComplement atomIndex hnotMem)
  have hcomplementZeroOn : ∀ atomIndex ∈ block, complement atomIndex = 0 := by
    intro atomIndex hmem
    exact htightComplement.hasSupport atomIndex (by
      simp only [Finset.mem_compl, not_not]
      exact hmem)
  have hfullUnit :
      (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) ⬝ᵥ
        (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) = 1 :=
    dotProduct_blockRestriction_eq_one_of_unit_of_zero_off block hblockCard full
      htightFullRaw.isUnit hfullZeroOff
  have hpairUnit : pair ⬝ᵥ pair = 1 :=
    dotProduct_blockRestriction_eq_one_of_unit_of_zero_off block hblockCard
      (selection pairBlock) (hdata.tightDir_unit pairBlock hpairMem) hpairZeroOff
  have hextraUnit : extra ⬝ᵥ extra = 1 :=
    dotProduct_blockRestriction_eq_one_of_unit_of_zero_off block hblockCard
      (selection extraBlock) (hdata.tightDir_unit extraBlock hextraMem) hextraZeroOff
  have hcomplementUnit :
      (fun complementIndex => complement
          (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) ⬝ᵥ
        (fun complementIndex => complement
          (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 1 :=
    dotProduct_complementRestriction_eq_one_of_unit_of_zero_on_block
      block hcomplementCard complement htightComplement.isUnit hcomplementZeroOn
  have hnotSubset : ¬ block ⊆ pairBlock := by
    intro hsubset
    have heq : block = pairBlock :=
      Finset.eq_of_subset_of_card_le hsubset (by rw [hblockCard, hpairCard])
    exact hpairNeBlock heq.symm
  obtain ⟨missingAtom, hmissingMem, hmissingNotPair⟩ :=
    Finset.not_subset.mp hnotSubset
  let missing : Fin 3 :=
    (block.orderIsoOfFin hblockCard).symm ⟨missingAtom, hmissingMem⟩
  have hmissingPick : block.orderEmbOfFin hblockCard missing = missingAtom := by
    change ((block.orderIsoOfFin hblockCard) missing).1 = missingAtom
    simp only [missing, OrderIso.apply_symm_apply]
  have hfullMissing : full (block.orderEmbOfFin hblockCard missing) ≠ 0 := by
    rw [hmissingPick]
    exact ambientTightSelection_ne_zero_of_mem_of_support_card_three
      tightVec block hblockCard hsupportThree hmissingMem
  have hpairMissing : pair missing = 0 := by
    dsimp only [pair]
    rw [hmissingPick]
    exact hdata.tightDir_support pairBlock hpairMem missingAtom hmissingNotPair
  have hfullNonzero : ∀ atomIndex ∈ block, full atomIndex ≠ 0 := by
    intro atomIndex hmem
    exact ambientTightSelection_ne_zero_of_mem_of_support_card_three
      tightVec block hblockCard hsupportThree hmem
  have hcomplementNonzero : ∀ atomIndex, atomIndex ∉ block →
      complement atomIndex ≠ 0 := by
    intro atomIndex hnotMem
    exact ambientTightSelection_ne_zero_of_uniform_complement_row tightVec block
      complementBlock hcomplementBlockCard hcomplementRow hnotMem
  have hextraWeight : 0 ≤ extraWeight :=
    hdata.activeWeight_nonneg extraBlock hextraMem
  have hweightSum : fullWeight + pairWeight + extraWeight = 1 / 2 := by
    have hsum := hdata.activeWeight_sum_one
    change ∑ selected ∈ family, multiplier selected = 1 at hsum
    rw [hfamilyEq] at hsum
    rw [Finset.sum_insert hcomplementNotRest,
      Finset.sum_insert hblockNotRest,
      Finset.sum_insert hpairNotExtra, Finset.sum_singleton] at hsum
    dsimp only [fullWeight, pairWeight, extraWeight]
    rw [hcomplementMultiplier] at hsum
    linarith
  have hmemberCard : ∀ selected ∈ family, selected.card = 3 := by
    intro selected hselected
    exact ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) selected).mp hselected).1
  obtain ⟨hassemblyCross, hassemblyComplement⟩ :=
    chartMultiplierAssembly_blockSplit_of_complement_multiplier_half family
      tightVec multiplier block complementBlock hmemberCard hcomplementMem
      hcomplementEq hcomplementMultiplier hotherZero
  have hassemblyLeft :
      (chartMultiplierAssembly family multiplier selection).submatrix
          (block.orderEmbOfFin hblockCard) (block.orderEmbOfFin hblockCard) =
        fullWeight • atomMatrix
            (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex))
          + pairWeight • atomMatrix pair + extraWeight • atomMatrix extra := by
    ext firstIndex secondIndex
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      atomMatrix, Matrix.vecMulVec_apply]
    rw [chartMultiplierAssembly_apply, hfamilyEq]
    rw [Finset.sum_insert hcomplementNotRest,
      Finset.sum_insert hblockNotRest,
      Finset.sum_insert hpairNotExtra, Finset.sum_singleton]
    have hfirstMem := Finset.orderEmbOfFin_mem block hblockCard firstIndex
    have hsecondMem := Finset.orderEmbOfFin_mem block hblockCard secondIndex
    have hcomplementFirst := hcomplementZeroOn _ hfirstMem
    have hcomplementSecond := hcomplementZeroOn _ hsecondMem
    dsimp only [fullWeight, pairWeight, extraWeight, full, pair, extra, complement]
    change selection complementBlock
      (block.orderEmbOfFin hblockCard firstIndex) = 0 at hcomplementFirst
    change selection complementBlock
      (block.orderEmbOfFin hblockCard secondIndex) = 0 at hcomplementSecond
    rw [hcomplementFirst, hcomplementSecond]
    ring
  exact crux.false_of_threeRow_spectral_blockData family id multiplier selection hdata
    block hblockCard hcomplementCard full complement pair extra missing fullWeight
    pairWeight extraWeight htightFullRaw htightComplement hfullUnit hpairUnit
    hextraUnit hcomplementUnit hfullMissing hpairMissing hblockPositive
    hpairPositive hextraWeight hweightSum hfullNonzero hcomplementNonzero
    hassemblyLeft hassemblyCross hassemblyComplement

/-- If exactly one non-complement multiplier is positive, the assembly diagonal
forces its active triple to be the selected triple.  After zero multipliers are
filtered, the datum is therefore carried by two complementary blocks and the
landed two-block exclusion applies. -/
theorem SixThreeCrux.false_of_complement_of_uniquePositiveBside
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (block complementBlock soleBlock : Finset (Fin 6))
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hblockCard : block.card = 3)
    (hcomplementMem : complementBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hsoleMem : soleBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hcomplementEq : complementBlock = blockᶜ)
    (hsoleNeComplement : soleBlock ≠ complementBlock)
    (hcomplementMultiplier : multiplier complementBlock = 1 / 2)
    (hsolePositive : 0 < multiplier soleBlock)
    (huniqueZero : ∀ otherBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ complementBlock → otherBlock ≠ soleBlock →
        multiplier otherBlock = 0) :
    False := by
  classical
  let family := chartArgmaxFamily (chartPointOfDesign crux.design)
  let selection := ambientTightSelection tightVec
  have hcomplementZeroOn : ∀ atomIndex ∈ block,
      selection complementBlock atomIndex = 0 := by
    intro atomIndex hmem
    exact hdata.tightDir_support complementBlock hcomplementMem atomIndex (by
      simpa only [id_eq, hcomplementEq, Finset.mem_compl, not_not] using hmem)
  have hblockSubset : block ⊆ soleBlock := by
    intro atomIndex hmem
    have hdiag := hdata.assembly_diagonal atomIndex
    rw [chartMultiplierAssembly_apply] at hdiag
    have hcollapse :
        ∑ selected ∈ family,
            multiplier selected * (selection selected atomIndex
              * selection selected atomIndex) =
          multiplier soleBlock * (selection soleBlock atomIndex
            * selection soleBlock atomIndex) := by
      apply Finset.sum_eq_single soleBlock
      · intro otherBlock hotherMem hotherNe
        by_cases hcomp : otherBlock = complementBlock
        · subst otherBlock
          rw [hcomplementZeroOn atomIndex hmem]
          ring
        · rw [huniqueZero otherBlock hotherMem hcomp hotherNe, zero_mul]
      · exact fun hnotMem => (hnotMem hsoleMem).elim
    change ∑ selected ∈ family,
      multiplier selected * (selection selected atomIndex
        * selection selected atomIndex) = (((6 : ℕ) : ℝ))⁻¹ at hdiag
    rw [hcollapse] at hdiag
    have hsoleNonzero : selection soleBlock atomIndex ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hdiag
      norm_num at hdiag
    by_contra hnotMem
    exact hsoleNonzero
      (hdata.tightDir_support soleBlock hsoleMem atomIndex hnotMem)
  have hsoleCard : soleBlock.card = 3 :=
    hdata.activeSubset_card soleBlock hsoleMem
  have hsoleEq : soleBlock = block := by
    exact (Finset.eq_of_subset_of_card_le hblockSubset (by
      rw [hsoleCard, hblockCard])).symm
  have hpositiveFamily :
      positiveActiveSet family multiplier = {soleBlock, complementBlock} := by
    ext selected
    simp only [positiveActiveSet, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hselectedMem, hselectedPositive⟩
      by_cases hcomp : selected = complementBlock
      · exact Or.inr hcomp
      by_cases hsole : selected = soleBlock
      · exact Or.inl hsole
      rw [huniqueZero selected hselectedMem hcomp hsole] at hselectedPositive
      exact (lt_irrefl 0 hselectedPositive).elim
    · intro hselected
      rcases hselected with rfl | rfl
      · exact ⟨hsoleMem, hsolePositive⟩
      · rw [hcomplementMultiplier]
        exact ⟨hcomplementMem, by norm_num⟩
  apply crux.false_of_positiveActiveSet_twoBlock hdata block
  intro selected hselected
  rw [hpositiveFamily] at hselected
  simp only [Finset.mem_insert, Finset.mem_singleton] at hselected
  rcases hselected with rfl | rfl
  · exact Or.inl hsoleEq
  · exact Or.inr hcomplementEq


end Gtz
