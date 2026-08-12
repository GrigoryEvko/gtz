import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The TwinPairs family, listed. -/
theorem canonicalTwinPairsFamily_eq_literal :
    canonicalTwinPairsFamily
      = ({{0, 1, 4}, {0, 1, 5}, {1, 2, 3}, {0, 2, 3}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE TWINPAIRS KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalTwinPairsFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalTwinPairsFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 4} ∨ block = {0, 1, 5} ∨ block = {1, 2, 3} ∨ block = {0, 2, 3} := by
    have hmem := hblockMem
    rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  obtain ⟨pairFirst, pairSecond, hpairDistinct, hpairEq⟩ :=
    Finset.card_eq_two.mp hsupportTwo
  have hpairSubset : ({pairFirst, pairSecond} : Finset (Fin 6)) ⊆ block := by
    rw [← hpairEq]
    exact totalTightSupport_subset tightVec hblockCard
  obtain ⟨coefficient, hremainingCard, hcoefficientNonzero, hcombinationNonzero,
    hcancel⟩ :=
    exists_threeActiveEigenSquareRow_cancellation_of_support_pair tightVec hfour
      hblockMem hblockCard hpairDistinct hpairEq
      (haxes pairFirst (by rw [hpairEq]; exact Finset.mem_insert_self _ _))
  rcases hblockCases with rfl | rfl | rfl | rfl
  · -- selected {0, 1, 4}
    have heraseEq : canonicalTwinPairsFamily.erase {0, 1, 4}
        = ({{0, 1, 5}, {1, 2, 3}, {0, 2, 3}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 4})
        (neighborBlock := {0, 1, 5})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov1 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit2 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 3}
      ·
        by_cases hmemSplit3 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          have hcancelAt4 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt5 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt6 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt4 hcancelAt5 hcancelAt6
          have hcoeff7 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt4
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
          have hcoeff8 : coefficient {1, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt5
              (Or.inl hcoeff7)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit2))
          have hcoeff9 : coefficient {0, 2, 3} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt6
              (Or.inl hcoeff7)
              (Or.inl hcoeff8)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff7
          · exact hbadNe hcoeff8
          · exact hbadNe hcoeff9
        ·
          have hpin10 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit3 (by decide)
          have hcancelAt11 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt12 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt13 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt11 hcancelAt12 hcancelAt13
          have hcoeff14 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt11
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
          have hcoeff15 : coefficient {1, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt12
              (Or.inl hcoeff14)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit2))
          have hcoeff16 : coefficient {0, 2, 3} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt13
              (Or.inl hcoeff14)
              (Or.inl hcoeff15)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin10]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff14
          · exact hbadNe hcoeff15
          · exact hbadNe hcoeff16
      ·
        have hpin17 : totalTightSupport tightVec {1, 2, 3} = {2, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 3} (by decide)) hmemSplit2 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {1, 2, 3})
          (neighborBlock := {0, 2, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin17]; decide)
    · -- pair {1, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov18 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit19 : (2 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 3}
      ·
        by_cases hmemSplit20 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          have hcancelAt21 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt22 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt23 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt21 hcancelAt22 hcancelAt23
          have hcoeff24 : coefficient {0, 1, 5} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt21
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov18))
          have hcoeff25 : coefficient {0, 2, 3} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt22
              (Or.inl hcoeff24)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit20))
          have hcoeff26 : coefficient {1, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt23
              (Or.inl hcoeff24)
              (Or.inl hcoeff25)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit19))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff24
          · exact hbadNe hcoeff26
          · exact hbadNe hcoeff25
        ·
          have hpin27 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit20 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 2, 3})
            (neighborBlock := {1, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin27]; decide)
      ·
        have hpin28 : totalTightSupport tightVec {1, 2, 3} = {1, 3} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 3} (by decide)) hmemSplit19 (by decide)
        have hcov29 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
          rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpin28] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
        have hcancelAt30 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt31 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt32 := hcancel 3 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt30 hcancelAt31 hcancelAt32
        have hcoeff33 : coefficient {0, 1, 5} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt30
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov18))
        have hcoeff34 : coefficient {0, 2, 3} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt31
            (Or.inl hcoeff33)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin28] at hmem; exact absurd hmem (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov29))
        have hcoeff35 : coefficient {1, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt32
            (Or.inl hcoeff33)
            (Or.inl hcoeff34)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin28]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff33
        · exact hbadNe hcoeff35
        · exact hbadNe hcoeff34
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 1, 5}
    have heraseEq : canonicalTwinPairsFamily.erase {0, 1, 5}
        = ({{0, 1, 4}, {1, 2, 3}, {0, 2, 3}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 5})
        (neighborBlock := {0, 1, 4})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov36 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit37 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 3}
      ·
        by_cases hmemSplit38 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          have hcancelAt39 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt40 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt41 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt39 hcancelAt40 hcancelAt41
          have hcoeff42 : coefficient {0, 1, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt39
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov36))
          have hcoeff43 : coefficient {1, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt40
              (Or.inl hcoeff42)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit37))
          have hcoeff44 : coefficient {0, 2, 3} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt41
              (Or.inl hcoeff42)
              (Or.inl hcoeff43)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit38))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff42
          · exact hbadNe hcoeff43
          · exact hbadNe hcoeff44
        ·
          have hpin45 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit38 (by decide)
          have hcancelAt46 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt47 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt48 := hcancel 3 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt46 hcancelAt47 hcancelAt48
          have hcoeff49 : coefficient {0, 1, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt46
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov36))
          have hcoeff50 : coefficient {1, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt47
              (Or.inl hcoeff49)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit37))
          have hcoeff51 : coefficient {0, 2, 3} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt48
              (Or.inl hcoeff49)
              (Or.inl hcoeff50)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin45]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff49
          · exact hbadNe hcoeff50
          · exact hbadNe hcoeff51
      ·
        have hpin52 : totalTightSupport tightVec {1, 2, 3} = {2, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 3} (by decide)) hmemSplit37 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {1, 2, 3})
          (neighborBlock := {0, 2, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin52]; decide)
    · -- pair {1, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov53 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit54 : (2 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 3}
      ·
        by_cases hmemSplit55 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
        ·
          have hcancelAt56 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt57 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt58 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt56 hcancelAt57 hcancelAt58
          have hcoeff59 : coefficient {0, 1, 4} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt56
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov53))
          have hcoeff60 : coefficient {0, 2, 3} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt57
              (Or.inl hcoeff59)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit55))
          have hcoeff61 : coefficient {1, 2, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt58
              (Or.inl hcoeff59)
              (Or.inl hcoeff60)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit54))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff59
          · exact hbadNe hcoeff61
          · exact hbadNe hcoeff60
        ·
          have hpin62 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit55 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 2, 3})
            (neighborBlock := {1, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin62]; decide)
      ·
        have hpin63 : totalTightSupport tightVec {1, 2, 3} = {1, 3} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 3} (by decide)) hmemSplit54 (by decide)
        have hcov64 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
          rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin63] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
        have hcancelAt65 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt66 := hcancel 2 (by rw [hpairSetEq]; decide)
        have hcancelAt67 := hcancel 3 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt65 hcancelAt66 hcancelAt67
        have hcoeff68 : coefficient {0, 1, 4} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt65
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov53))
        have hcoeff69 : coefficient {0, 2, 3} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt66
            (Or.inl hcoeff68)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin63] at hmem; exact absurd hmem (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov64))
        have hcoeff70 : coefficient {1, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt67
            (Or.inl hcoeff68)
            (Or.inl hcoeff69)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin63]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff68
        · exact hbadNe hcoeff70
        · exact hbadNe hcoeff69
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {1, 2, 3}
    have heraseEq : canonicalTwinPairsFamily.erase {1, 2, 3}
        = ({{0, 1, 4}, {0, 1, 5}, {0, 2, 3}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov71 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    have hcov72 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    by_cases hmemSplit73 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
    ·
      have hcancelAt74 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt75 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt76 := hcancel 0 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt74 hcancelAt75 hcancelAt76
      have hcoeff77 : coefficient {0, 1, 4} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt74
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov71))
      have hcoeff78 : coefficient {0, 1, 5} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt75
          (Or.inl hcoeff77)
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov72))
      have hcoeff79 : coefficient {0, 2, 3} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt76
          (Or.inl hcoeff77)
          (Or.inl hcoeff78)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit73))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff77
      · exact hbadNe hcoeff78
      · exact hbadNe hcoeff79
    ·
      have hpin80 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
        eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit73 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 3})
        (neighborBlock := {1, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin80]; decide)
  · -- selected {0, 2, 3}
    have heraseEq : canonicalTwinPairsFamily.erase {0, 2, 3}
        = ({{0, 1, 4}, {0, 1, 5}, {1, 2, 3}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov81 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    have hcov82 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalTwinPairsFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    by_cases hmemSplit83 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 3}
    ·
      have hcancelAt84 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt85 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt86 := hcancel 1 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt84 hcancelAt85 hcancelAt86
      have hcoeff87 : coefficient {0, 1, 4} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt84
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov81))
      have hcoeff88 : coefficient {0, 1, 5} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt85
          (Or.inl hcoeff87)
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov82))
      have hcoeff89 : coefficient {1, 2, 3} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt86
          (Or.inl hcoeff87)
          (Or.inl hcoeff88)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit83))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff87
      · exact hbadNe hcoeff88
      · exact hbadNe hcoeff89
    ·
      have hpin90 : totalTightSupport tightVec {1, 2, 3} = {2, 3} :=
        eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 3} (by decide)) hmemSplit83 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {1, 2, 3})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin90]; decide)

end Gtz
