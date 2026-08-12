import Gtz.Wave.PosDefFourActiveExit
import Gtz.Wave.SupportThreePositiveCollapse
import Gtz.Wave.ZeroFullTwoPositiveTraceGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- **THE FOUR-ACTIVE SPINE AFTER THE POSDEF EXIT.**  The second-order witness
is either support two, or it retains support three and a complementary uniform
row while the selected assembly block is necessarily singular.  The singular
branch is split exactly by whether some non-complement multiplier vanishes. -/
theorem SixThreeCrux.exists_stationary_supportTwo_or_singularComplement_of_four
    (crux : SixThreeCrux)
    (hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)) (hblockCard : block.card = 3),
      (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        Matrix.mulVec ((chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard)) (tightVec selected)
          = chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
          (ambientTightSelection tightVec)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ (∀ atomIndex ∈ totalTightSupport tightVec block,
          Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
            (chartArgmaxFamily (chartPointOfDesign crux.design))
            (totalEigenSquareRow tightVec))
      ∧ ((totalTightSupport tightVec block).card = 2
        ∨ (totalTightSupport tightVec block).card = 3
          ∧ ∃ complementBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
            complementBlock = blockᶜ
              ∧ totalEigenSquareRow tightVec complementBlock =
                (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3)
              ∧ multiplier complementBlock = 1 / 2
              ∧ (∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
                  totalEigenSquareRow tightVec otherBlock atomIndex = 0)
              ∧ ¬ ((chartMultiplierAssembly
                  (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier
                  (ambientTightSelection tightVec)).submatrix
                    (block.orderEmbOfFin
                      hblockCard)
                    (block.orderEmbOfFin
                      hblockCard)).PosDef
              ∧ ((∃ otherBlock ∈
                    chartArgmaxFamily (chartPointOfDesign crux.design),
                    otherBlock ≠ complementBlock ∧ multiplier otherBlock = 0)
                ∨ ∀ otherBlock ∈ chartArgmaxFamily
                    (chartPointOfDesign crux.design),
                    otherBlock ≠ complementBlock → 0 < multiplier otherBlock)) := by
  classical
  obtain ⟨tightVec, multiplier, block, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo | ⟨hsupportThree, complementBlock, hcomplementMem,
      hcomplementEq, hcomplementRow, hcomplementMultiplier, hotherZero⟩⟩ :=
    crux.exists_stationary_supportTwo_or_complement_of_four hfamilyCard
  all_goals have hblockCard : block.card = 3 :=
    ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) block).mp hblockMem).1
  · exact ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
      haxes, Or.inl hsupportTwo⟩
  ·
    have hcomplementCard : blockᶜ.card = 3 := by
      rw [← hcomplementEq]
      exact ((mem_chartArgmaxFamily_iff
        (chartPointOfDesign crux.design) complementBlock).mp hcomplementMem).1
    let assemblyBlock :=
      (chartMultiplierAssembly
        (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier
        (ambientTightSelection tightVec)).submatrix
          (block.orderEmbOfFin hblockCard) (block.orderEmbOfFin hblockCard)
    have hnotPosDef : ¬ assemblyBlock.PosDef := by
      intro hposDef
      exact crux.false_of_supportThree_complement_of_assemblyBlock_posDef
        tightVec multiplier block complementBlock hblockCard hcomplementCard
          hsupportThree hdata hblockMem hcomplementMem hcomplementEq
          hcomplementRow hcomplementMultiplier hotherZero hposDef
    have hmultiplierSplit :
        (∃ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
          otherBlock ≠ complementBlock ∧ multiplier otherBlock = 0)
        ∨ ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
          otherBlock ≠ complementBlock → 0 < multiplier otherBlock := by
      by_cases hzero : ∃ otherBlock ∈
          chartArgmaxFamily (chartPointOfDesign crux.design),
          otherBlock ≠ complementBlock ∧ multiplier otherBlock = 0
      · exact Or.inl hzero
      · right
        intro otherBlock hotherMem hotherNe
        have hnonneg := hdata.activeWeight_nonneg otherBlock hotherMem
        have hne : multiplier otherBlock ≠ 0 := by
          intro heq
          exact hzero ⟨otherBlock, hotherMem, hotherNe, heq⟩
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    refine ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
      haxes, Or.inr ⟨hsupportThree, complementBlock, hcomplementMem,
        hcomplementEq, hcomplementRow, hcomplementMultiplier, hotherZero, ?_,
        hmultiplierSplit⟩⟩
    simpa only [assemblyBlock] using hnotPosDef


/-- **THE FOUR-ACTIVE SPINE AFTER THE SPECTRAL AND TWO-BLOCK EXITS.**  Every
support-three branch is closed except the exact pattern in which the selected
full-support row has zero multiplier and the other two selected-side rows both
have positive multiplier.  The constant assembly diagonal forces those two rows
to cover every coordinate of the selected triple. -/
theorem SixThreeCrux.exists_stationary_supportTwo_or_zeroFull_twoPositiveCover_of_four
    (crux : SixThreeCrux)
    (hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)), block.card = 3
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        Matrix.mulVec ((chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard))
            (tightVec selected) =
          chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
          (ambientTightSelection tightVec)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ (∀ atomIndex ∈ totalTightSupport tightVec block,
          Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
            (chartArgmaxFamily (chartPointOfDesign crux.design))
            (totalEigenSquareRow tightVec))
      ∧ ((totalTightSupport tightVec block).card = 2
        ∨ (totalTightSupport tightVec block).card = 3
          ∧ ∃ complementBlock firstBlock secondBlock,
            complementBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
              ∧ complementBlock = blockᶜ
              ∧ totalEigenSquareRow tightVec complementBlock =
                (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3)
              ∧ multiplier complementBlock = 1 / 2
              ∧ (∀ otherBlock ∈
                  chartArgmaxFamily (chartPointOfDesign crux.design),
                otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
                  totalEigenSquareRow tightVec otherBlock atomIndex = 0)
              ∧ firstBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
              ∧ secondBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
              ∧ firstBlock ≠ block ∧ secondBlock ≠ block
              ∧ firstBlock ≠ complementBlock
              ∧ secondBlock ≠ complementBlock
              ∧ firstBlock ≠ secondBlock
              ∧ chartArgmaxFamily (chartPointOfDesign crux.design) =
                {complementBlock, block, firstBlock, secondBlock}
              ∧ multiplier block = 0
              ∧ 0 < multiplier firstBlock
              ∧ 0 < multiplier secondBlock
              ∧ ∀ atomIndex ∈ block,
                ambientTightSelection tightVec firstBlock atomIndex ≠ 0
                  ∨ ambientTightSelection tightVec secondBlock atomIndex ≠ 0) := by
  classical
  obtain ⟨tightVec, multiplier, block, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo | ⟨hsupportThree, complementBlock, hcomplementMem,
      hcomplementEq, hcomplementRow, hcomplementMultiplier, hotherZero⟩⟩ :=
    crux.exists_stationary_supportTwo_or_complement_of_four hfamilyCard
  all_goals have hblockCard : block.card = 3 :=
    ((mem_chartArgmaxFamily_iff
      (chartPointOfDesign crux.design) block).mp hblockMem).1
  · exact ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata,
      hblockMem, haxes, Or.inl hsupportTwo⟩
  ·
    let family := chartArgmaxFamily (chartPointOfDesign crux.design)
    let selection := ambientTightSelection tightVec
    have hblockNeComplement : block ≠ complementBlock := by
      intro heq
      have hselfComplement : block = blockᶜ := heq.trans hcomplementEq
      have hzero := congrArg
        (fun selected : Finset (Fin 6) => (0 : Fin 6) ∈ selected) hselfComplement
      simp only [Finset.mem_compl] at hzero
      tauto
    have hsideCard : (family.erase complementBlock).card = 3 := by
      rw [Finset.card_erase_of_mem hcomplementMem, hfamilyCard]
    have hblockSide : block ∈ family.erase complementBlock :=
      Finset.mem_erase.mpr ⟨hblockNeComplement, hblockMem⟩
    have hrestCard : ((family.erase complementBlock).erase block).card = 2 := by
      rw [Finset.card_erase_of_mem hblockSide, hsideCard]
    obtain ⟨firstBlock, secondBlock, hfirstNeSecond, hrestEq⟩ :=
      Finset.card_eq_two.mp hrestCard
    have hfirstRest : firstBlock ∈ (family.erase complementBlock).erase block := by
      rw [hrestEq]
      simp
    have hsecondRest : secondBlock ∈ (family.erase complementBlock).erase block := by
      rw [hrestEq]
      simp
    have hfirstNeBlock : firstBlock ≠ block := (Finset.mem_erase.mp hfirstRest).1
    have hsecondNeBlock : secondBlock ≠ block :=
      (Finset.mem_erase.mp hsecondRest).1
    have hfirstSide : firstBlock ∈ family.erase complementBlock :=
      Finset.mem_of_mem_erase hfirstRest
    have hsecondSide : secondBlock ∈ family.erase complementBlock :=
      Finset.mem_of_mem_erase hsecondRest
    have hfirstNeComplement : firstBlock ≠ complementBlock :=
      (Finset.mem_erase.mp hfirstSide).1
    have hsecondNeComplement : secondBlock ≠ complementBlock :=
      (Finset.mem_erase.mp hsecondSide).1
    have hfirstMem : firstBlock ∈ family := Finset.mem_of_mem_erase hfirstSide
    have hsecondMem : secondBlock ∈ family := Finset.mem_of_mem_erase hsecondSide
    have hsideEq : family.erase complementBlock = {block, firstBlock, secondBlock} := by
      calc
        family.erase complementBlock =
            insert block ((family.erase complementBlock).erase block) :=
          (Finset.insert_erase hblockSide).symm
        _ = {block, firstBlock, secondBlock} := by rw [hrestEq]
    have hfamilyEq : family = {complementBlock, block, firstBlock, secondBlock} := by
      calc
        family = insert complementBlock (family.erase complementBlock) :=
          (Finset.insert_erase hcomplementMem).symm
        _ = {complementBlock, block, firstBlock, secondBlock} := by rw [hsideEq]
    have hblockNonneg := hdata.activeWeight_nonneg block hblockMem
    have hfirstNonneg := hdata.activeWeight_nonneg firstBlock hfirstMem
    have hsecondNonneg := hdata.activeWeight_nonneg secondBlock hsecondMem
    have hzero_of_not_pos {value : ℝ}
        (hnonneg : 0 ≤ value) (hnotPos : ¬ 0 < value) : value = 0 :=
      le_antisymm (not_lt.mp hnotPos) hnonneg
    have huniqueZero (soleBlock : Finset (Fin 6))
        (hsole : soleBlock = block ∨ soleBlock = firstBlock ∨ soleBlock = secondBlock)
        (hblockZero : soleBlock ≠ block → multiplier block = 0)
        (hfirstZero : soleBlock ≠ firstBlock → multiplier firstBlock = 0)
        (hsecondZero : soleBlock ≠ secondBlock → multiplier secondBlock = 0) :
        ∀ otherBlock ∈ family, otherBlock ≠ complementBlock →
          otherBlock ≠ soleBlock → multiplier otherBlock = 0 := by
      intro otherBlock hotherMem hotherNeComplement hotherNeSole
      rw [hfamilyEq] at hotherMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hotherMem
      rcases hotherMem with rfl | rfl | rfl | rfl
      · exact (hotherNeComplement rfl).elim
      · exact hblockZero hotherNeSole.symm
      · exact hfirstZero hotherNeSole.symm
      · exact hsecondZero hotherNeSole.symm
    by_cases hblockPositive : 0 < multiplier block
    · by_cases hfirstPositive : 0 < multiplier firstBlock
      · exact (crux.false_of_supportThree_complement_of_twoPositiveBside
          tightVec multiplier block complementBlock firstBlock hfamilyCard
          hblockCard (by rw [← hcomplementEq]; exact
            ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design)
              complementBlock).mp hcomplementMem).1)
          hsupportThree hdata hblockMem hcomplementMem hfirstMem hcomplementEq
          hfirstNeBlock hfirstNeComplement hcomplementRow hcomplementMultiplier
          hotherZero hblockPositive hfirstPositive).elim
      · have hfirstZero := hzero_of_not_pos hfirstNonneg hfirstPositive
        by_cases hsecondPositive : 0 < multiplier secondBlock
        · exact (crux.false_of_supportThree_complement_of_twoPositiveBside
            tightVec multiplier block complementBlock secondBlock hfamilyCard
            hblockCard (by rw [← hcomplementEq]; exact
              ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design)
                complementBlock).mp hcomplementMem).1)
            hsupportThree hdata hblockMem hcomplementMem hsecondMem hcomplementEq
            hsecondNeBlock hsecondNeComplement hcomplementRow hcomplementMultiplier
            hotherZero hblockPositive hsecondPositive).elim
        · have hsecondZero := hzero_of_not_pos hsecondNonneg hsecondPositive
          exact (crux.false_of_complement_of_uniquePositiveBside tightVec multiplier
            block complementBlock block hdata hblockCard hcomplementMem hblockMem
            hcomplementEq hblockNeComplement hcomplementMultiplier hblockPositive
            (huniqueZero block (Or.inl rfl) (fun h => (h rfl).elim)
              (fun _ => hfirstZero) (fun _ => hsecondZero))).elim
    · have hblockZero := hzero_of_not_pos hblockNonneg hblockPositive
      by_cases hfirstPositive : 0 < multiplier firstBlock
      · by_cases hsecondPositive : 0 < multiplier secondBlock
        ·
          have hcomplementZeroOn : ∀ atomIndex ∈ block,
              selection complementBlock atomIndex = 0 := by
            intro atomIndex hmem
            exact hdata.tightDir_support complementBlock hcomplementMem atomIndex (by
              simpa only [id_eq, hcomplementEq, Finset.mem_compl, not_not] using hmem)
          have hcomplementNotRest : complementBlock ∉
              ({block, firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hblockNeComplement.symm,
              ⟨hfirstNeComplement.symm, hsecondNeComplement.symm⟩⟩
          have hblockNotRest : block ∉
              ({firstBlock, secondBlock} : Finset (Finset (Fin 6))) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hfirstNeBlock.symm, hsecondNeBlock.symm⟩
          have hfirstNotSecond : firstBlock ∉
              ({secondBlock} : Finset (Finset (Fin 6))) := by
            simpa only [Finset.mem_singleton] using hfirstNeSecond
          have hcover : ∀ atomIndex ∈ block,
              selection firstBlock atomIndex ≠ 0 ∨
                selection secondBlock atomIndex ≠ 0 := by
            intro atomIndex hmem
            by_contra hnone
            push Not at hnone
            have hdiag := hdata.assembly_diagonal atomIndex
            rw [chartMultiplierAssembly_apply] at hdiag
            change ∑ selected ∈ family,
              multiplier selected * (selection selected atomIndex
                * selection selected atomIndex) = (((6 : ℕ) : ℝ))⁻¹ at hdiag
            rw [hfamilyEq, Finset.sum_insert hcomplementNotRest,
              Finset.sum_insert hblockNotRest,
              Finset.sum_insert hfirstNotSecond, Finset.sum_singleton,
              hcomplementZeroOn atomIndex hmem, hblockZero, hnone.1, hnone.2] at hdiag
            norm_num at hdiag
          exact ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata,
            hblockMem, haxes, Or.inr ⟨hsupportThree, complementBlock, firstBlock,
              secondBlock, hcomplementMem, hcomplementEq, hcomplementRow,
              hcomplementMultiplier, hotherZero, hfirstMem, hsecondMem,
              hfirstNeBlock, hsecondNeBlock, hfirstNeComplement,
              hsecondNeComplement, hfirstNeSecond, hfamilyEq, hblockZero,
              hfirstPositive, hsecondPositive, hcover⟩⟩
        · have hsecondZero := hzero_of_not_pos hsecondNonneg hsecondPositive
          exact (crux.false_of_complement_of_uniquePositiveBside tightVec multiplier
            block complementBlock firstBlock hdata hblockCard hcomplementMem hfirstMem
            hcomplementEq hfirstNeComplement hcomplementMultiplier hfirstPositive
            (huniqueZero firstBlock (Or.inr (Or.inl rfl))
              (fun _ => hblockZero) (fun h => (h rfl).elim)
              (fun _ => hsecondZero))).elim
      · have hfirstZero := hzero_of_not_pos hfirstNonneg hfirstPositive
        have hsecondPositive : 0 < multiplier secondBlock := by
          by_contra hnotPositive
          have hsecondZero := hzero_of_not_pos hsecondNonneg hnotPositive
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
          have hfirstNotSecond : firstBlock ∉
              ({secondBlock} : Finset (Finset (Fin 6))) := by
            simpa only [Finset.mem_singleton] using hfirstNeSecond
          rw [hfamilyEq, Finset.sum_insert hcomplementNotRest,
            Finset.sum_insert hblockNotRest, Finset.sum_insert hfirstNotSecond,
            Finset.sum_singleton, hcomplementMultiplier, hblockZero, hfirstZero,
            hsecondZero] at hsum
          norm_num at hsum
        exact (crux.false_of_complement_of_uniquePositiveBside tightVec multiplier
          block complementBlock secondBlock hdata hblockCard hcomplementMem hsecondMem
          hcomplementEq hsecondNeComplement hcomplementMultiplier hsecondPositive
          (huniqueZero secondBlock (Or.inr (Or.inr rfl))
            (fun _ => hblockZero) (fun _ => hfirstZero)
            (fun h => (h rfl).elim))).elim


/-- **THE FOUR-ACTIVE SUPPORT-TWO REDUCTION.**  The complementary support-three
branch now closes in all multiplier patterns.  In the last zero-full pattern,
the two remaining rows have the exact path spectrum `{0,1/6,1/3}`; adjoining
the complementary half-block leaves no commuting projection trace in
`(0,1/6)`. -/
theorem SixThreeCrux.exists_stationary_supportTwo_of_four
    (crux : SixThreeCrux)
    (hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    ∃ (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
      (multiplier : Finset (Fin 6) → ℝ)
      (block : Finset (Fin 6)), block.card = 3
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 →
        tightVec selected ⬝ᵥ tightVec selected = 1)
      ∧ (∀ (selected : Finset (Fin 6)) (hcard : selected.card = 3),
        Matrix.mulVec ((chartPointGap (chartPointOfDesign crux.design)).submatrix
            (selected.orderEmbOfFin hcard) (selected.orderEmbOfFin hcard))
            (tightVec selected) =
          chartBlockValue 3 (((chartPointOfDesign crux.design).chart,
              (chartPointOfDesign crux.design).weight) :
              (Fin 6 → Fin 6 → ℝ) × (Fin 6 → ℝ)) selected • tightVec selected)
      ∧ IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design))
          (chartArgmaxFamily (chartPointOfDesign crux.design))
          (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
          (ambientTightSelection tightVec)
      ∧ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design)
      ∧ (∀ atomIndex ∈ totalTightSupport tightVec block,
          Pi.single atomIndex (1 : ℝ) ∈ finiteRowSpan
            (chartArgmaxFamily (chartPointOfDesign crux.design))
            (totalEigenSquareRow tightVec))
      ∧ (totalTightSupport tightVec block).card = 2 := by
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata,
    hblockMem, haxes, hsupportTwo |
      ⟨_hsupportThree, complementBlock, firstBlock, secondBlock,
        hcomplementMem, hcomplementEq, _hcomplementRow, hcomplementMultiplier,
        hotherZero, hfirstMem, hsecondMem, hfirstNeBlock, hsecondNeBlock,
        hfirstNeComplement, hsecondNeComplement, hfirstNeSecond, hfamilyEq,
        hblockZero, _hfirstPositive, _hsecondPositive, hcover⟩⟩ :=
    crux.exists_stationary_supportTwo_or_zeroFull_twoPositiveCover_of_four hfamilyCard
  · exact ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata,
      hblockMem, haxes, hsupportTwo⟩
  · exact (crux.false_of_zeroFull_twoPositiveCover_spectral tightVec multiplier
      block complementBlock firstBlock secondBlock hblockCard hdata
      hcomplementMem hcomplementEq hcomplementMultiplier hotherZero hfirstMem
      hsecondMem hfirstNeBlock hsecondNeBlock hfirstNeComplement
      hsecondNeComplement hfirstNeSecond hfamilyEq hblockZero hcover).elim


end Gtz
