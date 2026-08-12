import Gtz.Wave.SupportThreePositiveCollapse
import Gtz.Wave.SharedEdgeSpectralTraceGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

theorem dotProduct_eq_zero_of_zero_off_on
    {size : ℕ} (block : Finset (Fin size)) (left right : Fin size → ℝ)
    (hleft : ∀ atomIndex, atomIndex ∉ block → left atomIndex = 0)
    (hright : ∀ atomIndex ∈ block, right atomIndex = 0) :
    left ⬝ᵥ right = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun atomIndex _ => ?_
  by_cases hmem : atomIndex ∈ block
  · rw [hright atomIndex hmem, mul_zero]
  · rw [hleft atomIndex hmem, zero_mul]

/-- The last zero-multiplier support-three residue in the four-active spine has
an exact `1/6` spectral gap in its multiplier assembly, contradicting the
strictly negative crux trace. -/
theorem SixThreeCrux.false_of_zeroFull_twoPositiveCover_spectral
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (block complementBlock firstBlock secondBlock : Finset (Fin 6))
    (hblockCard : block.card = 3)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hcomplementMem : complementBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hcomplementEq : complementBlock = blockᶜ)
    (hcomplementMultiplier : multiplier complementBlock = 1 / 2)
    (hotherZero : ∀ otherBlock ∈
        chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
        totalEigenSquareRow tightVec otherBlock atomIndex = 0)
    (hfirstMem : firstBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hsecondMem : secondBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hfirstNeBlock : firstBlock ≠ block)
    (hsecondNeBlock : secondBlock ≠ block)
    (hfirstNeComplement : firstBlock ≠ complementBlock)
    (hsecondNeComplement : secondBlock ≠ complementBlock)
    (hfirstNeSecond : firstBlock ≠ secondBlock)
    (hfamilyEq : chartArgmaxFamily (chartPointOfDesign crux.design) =
      {complementBlock, block, firstBlock, secondBlock})
    (hblockZero : multiplier block = 0)
    (hcover : ∀ atomIndex ∈ block,
      ambientTightSelection tightVec firstBlock atomIndex ≠ 0 ∨
        ambientTightSelection tightVec secondBlock atomIndex ≠ 0) :
    False := by
  classical
  let family := chartArgmaxFamily (chartPointOfDesign crux.design)
  let selection := ambientTightSelection tightVec
  let first := selection firstBlock
  let second := selection secondBlock
  let complement := selection complementBlock
  let firstRestricted : Fin 3 → ℝ := fun blockIndex =>
    first (block.orderEmbOfFin hblockCard blockIndex)
  let secondRestricted : Fin 3 → ℝ := fun blockIndex =>
    second (block.orderEmbOfFin hblockCard blockIndex)
  let localAssembly := multiplier firstBlock • atomMatrix firstRestricted
    + multiplier secondBlock • atomMatrix secondRestricted
  let injection := selectionInjection (block.orderEmbOfFin hblockCard)
  let embeddedAssembly := injection * localAssembly * injectionᵀ
  let assembly := chartMultiplierAssembly family multiplier selection
  let projection := (chartPointOfDesign crux.design).chart
  have hfamilyEqLocal : family =
      {complementBlock, block, firstBlock, secondBlock} := hfamilyEq
  have hblockNeComplement : block ≠ complementBlock := by
    intro heq
    have hself : block = blockᶜ := heq.trans hcomplementEq
    have := congrArg (fun selected : Finset (Fin 6) => (0 : Fin 6) ∈ selected) hself
    simp only [Finset.mem_compl] at this
    tauto
  have hfirstCard : firstBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) firstBlock).mp hfirstMem).1
  have hsecondCard : secondBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) secondBlock).mp hsecondMem).1
  have hcomplementCard : complementBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) complementBlock).mp hcomplementMem).1
  have hfirstZeroOff : ∀ atomIndex, atomIndex ∉ block → first atomIndex = 0 := by
    intro atomIndex hnotMem
    exact ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
      firstBlock hfirstCard atomIndex
        (hotherZero firstBlock hfirstMem hfirstNeComplement atomIndex hnotMem)
  have hsecondZeroOff : ∀ atomIndex, atomIndex ∉ block → second atomIndex = 0 := by
    intro atomIndex hnotMem
    exact ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec
      secondBlock hsecondCard atomIndex
        (hotherZero secondBlock hsecondMem hsecondNeComplement atomIndex hnotMem)
  have hcomplementZeroOn : ∀ atomIndex ∈ block, complement atomIndex = 0 := by
    intro atomIndex hmem
    exact hdata.tightDir_support complementBlock hcomplementMem atomIndex (by
      simpa only [id_eq, hcomplementEq, Finset.mem_compl, not_not] using hmem)
  have hfirstUnit : firstRestricted ⬝ᵥ firstRestricted = 1 :=
    dotProduct_blockRestriction_eq_one_of_unit_of_zero_off block hblockCard first
      (hdata.tightDir_unit firstBlock hfirstMem) hfirstZeroOff
  have hsecondUnit : secondRestricted ⬝ᵥ secondRestricted = 1 :=
    dotProduct_blockRestriction_eq_one_of_unit_of_zero_off block hblockCard second
      (hdata.tightDir_unit secondBlock hsecondMem) hsecondZeroOff
  have hnotFirstSubset : ¬ block ⊆ firstBlock := by
    intro hsubset
    have heq : block = firstBlock :=
      Finset.eq_of_subset_of_card_le hsubset (by rw [hblockCard, hfirstCard])
    exact hfirstNeBlock heq.symm
  obtain ⟨firstMissingAtom, hfirstMissingMem, hfirstMissingNot⟩ :=
    Finset.not_subset.mp hnotFirstSubset
  let firstMissing : Fin 3 :=
    (block.orderIsoOfFin hblockCard).symm ⟨firstMissingAtom, hfirstMissingMem⟩
  have hfirstMissingPick :
      block.orderEmbOfFin hblockCard firstMissing = firstMissingAtom := by
    change ((block.orderIsoOfFin hblockCard) firstMissing).1 = firstMissingAtom
    simp only [firstMissing, OrderIso.apply_symm_apply]
  have hfirstMissing : firstRestricted firstMissing = 0 := by
    dsimp only [firstRestricted]
    rw [hfirstMissingPick]
    exact hdata.tightDir_support firstBlock hfirstMem firstMissingAtom hfirstMissingNot
  have hnotSecondSubset : ¬ block ⊆ secondBlock := by
    intro hsubset
    have heq : block = secondBlock :=
      Finset.eq_of_subset_of_card_le hsubset (by rw [hblockCard, hsecondCard])
    exact hsecondNeBlock heq.symm
  obtain ⟨secondMissingAtom, hsecondMissingMem, hsecondMissingNot⟩ :=
    Finset.not_subset.mp hnotSecondSubset
  let secondMissing : Fin 3 :=
    (block.orderIsoOfFin hblockCard).symm ⟨secondMissingAtom, hsecondMissingMem⟩
  have hsecondMissingPick :
      block.orderEmbOfFin hblockCard secondMissing = secondMissingAtom := by
    change ((block.orderIsoOfFin hblockCard) secondMissing).1 = secondMissingAtom
    simp only [secondMissing, OrderIso.apply_symm_apply]
  have hsecondMissing : secondRestricted secondMissing = 0 := by
    dsimp only [secondRestricted]
    rw [hsecondMissingPick]
    exact hdata.tightDir_support secondBlock hsecondMem secondMissingAtom hsecondMissingNot
  have hmissingDistinct : firstMissing ≠ secondMissing := by
    intro heq
    have hatomEq : firstMissingAtom = secondMissingAtom := by
      rw [← hfirstMissingPick, ← hsecondMissingPick, heq]
    rcases hcover firstMissingAtom hfirstMissingMem with hfirstNonzero | hsecondNonzero
    · exact hfirstNonzero (by
        change first firstMissingAtom = 0
        simpa only [firstRestricted, hfirstMissingPick] using hfirstMissing)
    · exact hsecondNonzero (by
        change second firstMissingAtom = 0
        rw [hatomEq]
        simpa only [secondRestricted, hsecondMissingPick] using hsecondMissing)
  have hweightSum : multiplier firstBlock + multiplier secondBlock = 1 / 2 := by
    have hsum := hdata.activeWeight_sum_one
    change ∑ selected ∈ family, multiplier selected = 1 at hsum
    have hcomplementNotRest : complementBlock ∉
        ({block, firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hblockNeComplement.symm,
        ⟨hfirstNeComplement.symm, hsecondNeComplement.symm⟩⟩
    have hblockNotRest : block ∉
        ({firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hfirstNeBlock.symm, hsecondNeBlock.symm⟩
    have hfirstNotSecond : firstBlock ∉ ({secondBlock} : Finset (Finset (Fin 6))) := by
      simpa only [Finset.mem_singleton] using hfirstNeSecond
    rw [hfamilyEqLocal, Finset.sum_insert hcomplementNotRest,
      Finset.sum_insert hblockNotRest, Finset.sum_insert hfirstNotSecond,
      Finset.sum_singleton, hcomplementMultiplier, hblockZero] at hsum
    linarith
  have hdiagonal : ∀ coordinate : Fin 3,
      localAssembly coordinate coordinate = 1 / 6 := by
    intro coordinate
    have hdiag := hdata.assembly_diagonal
      (block.orderEmbOfFin hblockCard coordinate)
    rw [chartMultiplierAssembly_apply] at hdiag
    change ∑ selected ∈ family,
      multiplier selected *
        (selection selected (block.orderEmbOfFin hblockCard coordinate) *
          selection selected (block.orderEmbOfFin hblockCard coordinate)) =
      (((6 : ℕ) : ℝ))⁻¹ at hdiag
    have hpickMem := block.orderEmbOfFin_mem hblockCard coordinate
    have hcomplementAt := hcomplementZeroOn
      (block.orderEmbOfFin hblockCard coordinate) hpickMem
    change selection complementBlock
      (block.orderEmbOfFin hblockCard coordinate) = 0 at hcomplementAt
    have hcomplementNotRest : complementBlock ∉
        ({block, firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hblockNeComplement.symm,
        ⟨hfirstNeComplement.symm, hsecondNeComplement.symm⟩⟩
    have hblockNotRest : block ∉
        ({firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hfirstNeBlock.symm, hsecondNeBlock.symm⟩
    have hfirstNotSecond : firstBlock ∉ ({secondBlock} : Finset (Finset (Fin 6))) := by
      simpa only [Finset.mem_singleton] using hfirstNeSecond
    rw [hfamilyEqLocal, Finset.sum_insert hcomplementNotRest,
      Finset.sum_insert hblockNotRest, Finset.sum_insert hfirstNotSecond,
      Finset.sum_singleton, hcomplementAt, hblockZero] at hdiag
    norm_num at hdiag ⊢
    simpa only [localAssembly, firstRestricted, secondRestricted,
      Matrix.add_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul, first, second, invOf_eq_inv, one_div] using hdiag
  have hlocalFloor :
      (localAssembly * localAssembly - (1 / 6 : ℝ) • localAssembly).PosSemidef := by
    exact twoAtom_square_floor_posSemidef_of_distinct_missing firstRestricted
      secondRestricted (multiplier firstBlock) (multiplier secondBlock)
      firstMissing secondMissing hmissingDistinct hfirstUnit hsecondUnit
      hfirstMissing hsecondMissing hweightSum hdiagonal
  have hembeddedFloor :
      (embeddedAssembly * embeddedAssembly
        - (1 / 6 : ℝ) • embeddedAssembly).PosSemidef := by
    exact embedded_square_floor_posSemidef
      (block.orderEmbOfFin hblockCard) (block.orderEmbOfFin hblockCard).injective
      localAssembly hlocalFloor
  have hfirstSpread : injection *ᵥ firstRestricted = first := by
    symm
    exact eq_selectionInjection_mulVec_of_support block hblockCard hfirstZeroOff
  have hsecondSpread : injection *ᵥ secondRestricted = second := by
    symm
    exact eq_selectionInjection_mulVec_of_support block hblockCard hsecondZeroOff
  have hembeddedEq : embeddedAssembly =
      multiplier firstBlock • atomMatrix first
        + multiplier secondBlock • atomMatrix second := by
    have hfirstEmbed : injection * atomMatrix firstRestricted * injectionᵀ =
        atomMatrix first := by
      dsimp only [injection]
      rw [selectionInjection_mul_atomMatrix_mul_transpose]
      exact congrArg atomMatrix hfirstSpread
    have hsecondEmbed : injection * atomMatrix secondRestricted * injectionᵀ =
        atomMatrix second := by
      dsimp only [injection]
      rw [selectionInjection_mul_atomMatrix_mul_transpose]
      exact congrArg atomMatrix hsecondSpread
    dsimp only [embeddedAssembly, localAssembly]
    calc
      injection *
            (multiplier firstBlock • atomMatrix firstRestricted
              + multiplier secondBlock • atomMatrix secondRestricted) * injectionᵀ =
          multiplier firstBlock •
              (injection * atomMatrix firstRestricted * injectionᵀ)
            + multiplier secondBlock •
              (injection * atomMatrix secondRestricted * injectionᵀ) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.smul_mul]
      _ = multiplier firstBlock • atomMatrix first
          + multiplier secondBlock • atomMatrix second := by
        rw [hfirstEmbed, hsecondEmbed]
  have hfirstComplementOrthogonal : first ⬝ᵥ complement = 0 :=
    dotProduct_eq_zero_of_zero_off_on block first complement hfirstZeroOff
      hcomplementZeroOn
  have hsecondComplementOrthogonal : second ⬝ᵥ complement = 0 :=
    dotProduct_eq_zero_of_zero_off_on block second complement hsecondZeroOff
      hcomplementZeroOn
  have hcrossRight : embeddedAssembly * atomMatrix complement = 0 := by
    rw [hembeddedEq, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      atomMatrix_mul_atomMatrix, atomMatrix_mul_atomMatrix,
      hfirstComplementOrthogonal, hsecondComplementOrthogonal,
      zero_smul]
    simp
  have hcrossLeft : atomMatrix complement * embeddedAssembly = 0 := by
    rw [hembeddedEq, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      atomMatrix_mul_atomMatrix, atomMatrix_mul_atomMatrix,
      dotProduct_comm complement first, dotProduct_comm complement second,
      hfirstComplementOrthogonal, hsecondComplementOrthogonal,
      zero_smul]
    simp
  have hcomplementUnit : complement ⬝ᵥ complement = 1 :=
    hdata.tightDir_unit complementBlock hcomplementMem
  have htotalFloor :
      ((embeddedAssembly + (1 / 2 : ℝ) • atomMatrix complement) *
          (embeddedAssembly + (1 / 2 : ℝ) • atomMatrix complement)
        - (1 / 6 : ℝ) •
          (embeddedAssembly + (1 / 2 : ℝ) • atomMatrix complement)).PosSemidef :=
    add_half_atomMatrix_square_floor_posSemidef embeddedAssembly complement
      hembeddedFloor hcomplementUnit hcrossRight hcrossLeft
  have hassemblyEq : assembly =
      embeddedAssembly + (1 / 2 : ℝ) • atomMatrix complement := by
    rw [hembeddedEq]
    dsimp only [assembly]
    ext rowIndex colIndex
    rw [chartMultiplierAssembly_apply]
    change ∑ selected ∈ family,
        multiplier selected * (selection selected rowIndex * selection selected colIndex) = _
    have hcomplementNotRest : complementBlock ∉
        ({block, firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hblockNeComplement.symm,
        ⟨hfirstNeComplement.symm, hsecondNeComplement.symm⟩⟩
    have hblockNotRest : block ∉
        ({firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hfirstNeBlock.symm, hsecondNeBlock.symm⟩
    have hfirstNotSecond : firstBlock ∉ ({secondBlock} : Finset (Finset (Fin 6))) := by
      simpa only [Finset.mem_singleton] using hfirstNeSecond
    rw [hfamilyEqLocal, Finset.sum_insert hcomplementNotRest,
      Finset.sum_insert hblockNotRest, Finset.sum_insert hfirstNotSecond,
      Finset.sum_singleton, hcomplementMultiplier, hblockZero]
    simp only [zero_mul, Matrix.add_apply, Matrix.smul_apply,
      atomMatrix, Matrix.vecMulVec_apply, first, second, complement]
    ring
  have hfloor : (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef := by
    rw [hassemblyEq]
    exact htotalFloor
  have htraceEq := trace_projection_mul_multiplier_of_isChartStationaryData hdata
  change Matrix.trace (projection * assembly) =
    chartObjective (chartPointOfDesign crux.design) + (((6 : ℕ) : ℝ))⁻¹ at htraceEq
  have htracePositive : 0 < Matrix.trace (projection * assembly) := by
    rw [htraceEq]
    have hstrict := neg_inv_size_lt_value_of_isChartStationaryData
      crux.design rfl crux.isChartArgmaxValue hdata
    norm_num at hstrict ⊢
    linarith
  have htraceFloor : 1 / 6 ≤ Matrix.trace (projection * assembly) := by
    exact sixth_le_trace_projection_mul_of_square_floor projection assembly
      (posSemidef_projectionOfDesign crux.design) hdata.isIdempotent
      hdata.assembly_commutes
      (posSemidef_projection_mul_multiplier_of_isChartStationaryData hdata)
      hfloor htracePositive
  rw [htraceEq] at htraceFloor
  have hnegative := crux.hasNegativeChartValue
  norm_num at htraceFloor
  linarith


end Gtz
