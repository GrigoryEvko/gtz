import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The DoubleDouble family, listed. -/
theorem canonicalDoubleDoubleFamily_eq_literal :
    canonicalDoubleDoubleFamily
      = ({{0, 1, 2}, {0, 1, 3}, {2, 4, 5}, {3, 4, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE DOUBLEDOUBLE KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalDoubleDoubleFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalDoubleDoubleFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 1, 3} ∨ block = {2, 4, 5} ∨ block = {3, 4, 5} := by
    have hmem := hblockMem
    rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hmem
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
  · -- selected {0, 1, 2}
    have heraseEq : canonicalDoubleDoubleFamily.erase {0, 1, 2}
        = ({{0, 1, 3}, {2, 4, 5}, {3, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov1 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit2 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
      ·
        by_cases hmemSplit3 : (3 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5}
        ·
          have hcancelAt4 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt5 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt6 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt4 hcancelAt5 hcancelAt6
          have hcoeff7 : coefficient {0, 1, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt4
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
          have hcoeff8 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt5
              (Or.inl hcoeff7)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
          have hcoeff9 : coefficient {2, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt6
              (Or.inl hcoeff7)
              (Or.inl hcoeff8)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit2))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff7
          · exact hbadNe hcoeff9
          · exact hbadNe hcoeff8
        ·
          have hpin10 : totalTightSupport tightVec {3, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {3, 4, 5} (by decide)) hmemSplit3 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {3, 4, 5})
            (neighborBlock := {2, 4, 5})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin10]; decide)
      ·
        have hpin11 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit2 (by decide)
        have hcov12 : (4 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
          rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpin11] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
        have hcancelAt13 := hcancel 1 (by rw [hpairSetEq]; decide)
        have hcancelAt14 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt15 := hcancel 5 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt13 hcancelAt14 hcancelAt15
        have hcoeff16 : coefficient {0, 1, 3} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt13
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
        have hcoeff17 : coefficient {3, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt14
            (Or.inl hcoeff16)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin11] at hmem; exact absurd hmem (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov12))
        have hcoeff18 : coefficient {2, 4, 5} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt15
            (Or.inl hcoeff16)
            (Or.inl hcoeff17)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin11]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff16
        · exact hbadNe hcoeff18
        · exact hbadNe hcoeff17
    · -- pair {1, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov19 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit20 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
      ·
        by_cases hmemSplit21 : (3 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5}
        ·
          have hcancelAt22 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt23 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt24 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt22 hcancelAt23 hcancelAt24
          have hcoeff25 : coefficient {0, 1, 3} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt22
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov19))
          have hcoeff26 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt23
              (Or.inl hcoeff25)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit21))
          have hcoeff27 : coefficient {2, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt24
              (Or.inl hcoeff25)
              (Or.inl hcoeff26)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit20))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff25
          · exact hbadNe hcoeff27
          · exact hbadNe hcoeff26
        ·
          have hpin28 : totalTightSupport tightVec {3, 4, 5} = {4, 5} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {3, 4, 5} (by decide)) hmemSplit21 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {3, 4, 5})
            (neighborBlock := {2, 4, 5})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin28]; decide)
      ·
        have hpin29 : totalTightSupport tightVec {2, 4, 5} = {2, 5} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit20 (by decide)
        have hcov30 : (4 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
          rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
          · rw [hpin29] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
        have hcancelAt31 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt32 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt33 := hcancel 5 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt31 hcancelAt32 hcancelAt33
        have hcoeff34 : coefficient {0, 1, 3} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt31
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov19))
        have hcoeff35 : coefficient {3, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt32
            (Or.inl hcoeff34)
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin29] at hmem; exact absurd hmem (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov30))
        have hcoeff36 : coefficient {2, 4, 5} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt33
            (Or.inl hcoeff34)
            (Or.inl hcoeff35)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin29]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff34
        · exact hbadNe hcoeff36
        · exact hbadNe hcoeff35
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 1, 3}
    have heraseEq : canonicalDoubleDoubleFamily.erase {0, 1, 3}
        = ({{0, 1, 2}, {2, 4, 5}, {3, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 1}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 1} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 3})
        (neighborBlock := {0, 1, 2})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov37 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 1
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit38 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
      ·
        by_cases hmemSplit39 : (4 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5}
        ·
          have hcancelAt40 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt41 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt42 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt40 hcancelAt41 hcancelAt42
          have hcoeff43 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt40
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov37))
          have hcoeff44 : coefficient {2, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt41
              (Or.inl hcoeff43)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit38))
          have hcoeff45 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt42
              (Or.inl hcoeff43)
              (Or.inl hcoeff44)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit39))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff43
          · exact hbadNe hcoeff44
          · exact hbadNe hcoeff45
        ·
          have hpin46 : totalTightSupport tightVec {3, 4, 5} = {3, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {3, 4, 5} (by decide)) hmemSplit39 (by decide)
          have hcancelAt47 := hcancel 1 (by rw [hpairSetEq]; decide)
          have hcancelAt48 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt49 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt47 hcancelAt48 hcancelAt49
          have hcoeff50 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt47
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov37))
          have hcoeff51 : coefficient {2, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt48
              (Or.inl hcoeff50)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit38))
          have hcoeff52 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt49
              (Or.inl hcoeff50)
              (Or.inl hcoeff51)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin46]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff50
          · exact hbadNe hcoeff51
          · exact hbadNe hcoeff52
      ·
        have hpin53 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit38 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {2, 4, 5})
          (neighborBlock := {3, 4, 5})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin53]; decide)
    · -- pair {1, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov54 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      by_cases hmemSplit55 : (2 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5}
      ·
        by_cases hmemSplit56 : (4 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5}
        ·
          have hcancelAt57 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt58 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt59 := hcancel 4 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt57 hcancelAt58 hcancelAt59
          have hcoeff60 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt57
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov54))
          have hcoeff61 : coefficient {2, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt58
              (Or.inl hcoeff60)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit55))
          have hcoeff62 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt59
              (Or.inl hcoeff60)
              (Or.inl hcoeff61)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit56))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff60
          · exact hbadNe hcoeff61
          · exact hbadNe hcoeff62
        ·
          have hpin63 : totalTightSupport tightVec {3, 4, 5} = {3, 5} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {3, 4, 5} (by decide)) hmemSplit56 (by decide)
          have hcancelAt64 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt65 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt66 := hcancel 5 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt64 hcancelAt65 hcancelAt66
          have hcoeff67 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt64
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov54))
          have hcoeff68 : coefficient {2, 4, 5} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt65
              (Or.inl hcoeff67)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit55))
          have hcoeff69 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt66
              (Or.inl hcoeff67)
              (Or.inl hcoeff68)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin63]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff67
          · exact hbadNe hcoeff68
          · exact hbadNe hcoeff69
      ·
        have hpin70 : totalTightSupport tightVec {2, 4, 5} = {4, 5} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {2, 4, 5} (by decide)) hmemSplit55 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {2, 4, 5})
          (neighborBlock := {3, 4, 5})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin70]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {2, 4, 5}
    have heraseEq : canonicalDoubleDoubleFamily.erase {2, 4, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {3, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {2, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov71 : (5 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      by_cases hmemSplit72 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit73 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          have hcancelAt74 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt75 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt76 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt74 hcancelAt75 hcancelAt76
          have hcoeff77 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt74
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov71))
          have hcoeff78 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt75
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff77)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit73))
          have hcoeff79 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt76
              (Or.inl hcoeff78)
              (Or.inl hcoeff77)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit72))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff79
          · exact hbadNe hcoeff78
          · exact hbadNe hcoeff77
        ·
          have hpin80 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit73 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 3})
            (neighborBlock := {0, 1, 2})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin80]; decide)
      ·
        have hpin81 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit72 (by decide)
        have hcov82 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin81] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt83 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt84 := hcancel 5 (by rw [hpairSetEq]; decide)
        have hcancelAt85 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt83 hcancelAt84 hcancelAt85
        have hcoeff86 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt83
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin81] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov82))
        have hcoeff87 : coefficient {3, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt84
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff86)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov71))
        have hcoeff88 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt85
            (Or.inl hcoeff86)
            (Or.inl hcoeff87)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin81]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff88
        · exact hbadNe hcoeff86
        · exact hbadNe hcoeff87
    · -- pair {2, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov89 : (4 : Fin 6) ∈ totalTightSupport tightVec {3, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      by_cases hmemSplit90 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit91 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          have hcancelAt92 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt93 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt94 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt92 hcancelAt93 hcancelAt94
          have hcoeff95 : coefficient {3, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt92
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov89))
          have hcoeff96 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt93
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff95)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit91))
          have hcoeff97 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt94
              (Or.inl hcoeff96)
              (Or.inl hcoeff95)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit90))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff97
          · exact hbadNe hcoeff96
          · exact hbadNe hcoeff95
        ·
          have hpin98 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit91 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 3})
            (neighborBlock := {0, 1, 2})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin98]; decide)
      ·
        have hpin99 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit90 (by decide)
        have hcov100 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin99] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt101 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt102 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt103 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt101 hcancelAt102 hcancelAt103
        have hcoeff104 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt101
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin99] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov100))
        have hcoeff105 : coefficient {3, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt102
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff104)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov89))
        have hcoeff106 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt103
            (Or.inl hcoeff104)
            (Or.inl hcoeff105)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin99]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff106
        · exact hbadNe hcoeff104
        · exact hbadNe hcoeff105
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {2, 4, 5})
        (neighborBlock := {3, 4, 5})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {3, 4, 5}
    have heraseEq : canonicalDoubleDoubleFamily.erase {3, 4, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {2, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {3, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {3, 4} :=
        hpairEq.symm.trans hpairPin
      have hcov107 : (5 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit108 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit109 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          have hcancelAt110 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt111 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt112 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt110 hcancelAt111 hcancelAt112
          have hcoeff113 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt110
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov107))
          have hcoeff114 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt111
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff113)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit108))
          have hcoeff115 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt112
              (Or.inl hcoeff114)
              (Or.inl hcoeff113)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit109))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff114
          · exact hbadNe hcoeff115
          · exact hbadNe hcoeff113
        ·
          have hpin116 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit109 (by decide)
          have hcancelAt117 := hcancel 5 (by rw [hpairSetEq]; decide)
          have hcancelAt118 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt119 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt117 hcancelAt118 hcancelAt119
          have hcoeff120 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt117
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov107))
          have hcoeff121 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt118
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff120)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit108))
          have hcoeff122 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt119
              (Or.inl hcoeff121)
              (Or.inl hcoeff120)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin116]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff121
          · exact hbadNe hcoeff122
          · exact hbadNe hcoeff120
      ·
        have hpin123 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit108 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 2})
          (neighborBlock := {0, 1, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin123]; decide)
    · -- pair {3, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {3, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov124 : (4 : Fin 6) ∈ totalTightSupport tightVec {2, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalDoubleDoubleFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit125 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit126 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          have hcancelAt127 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt128 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt129 := hcancel 0 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt127 hcancelAt128 hcancelAt129
          have hcoeff130 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt127
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov124))
          have hcoeff131 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt128
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff130)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit125))
          have hcoeff132 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt129
              (Or.inl hcoeff131)
              (Or.inl hcoeff130)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit126))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff131
          · exact hbadNe hcoeff132
          · exact hbadNe hcoeff130
        ·
          have hpin133 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit126 (by decide)
          have hcancelAt134 := hcancel 4 (by rw [hpairSetEq]; decide)
          have hcancelAt135 := hcancel 2 (by rw [hpairSetEq]; decide)
          have hcancelAt136 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt134 hcancelAt135 hcancelAt136
          have hcoeff137 : coefficient {2, 4, 5} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt134
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov124))
          have hcoeff138 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt135
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inl hcoeff137)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit125))
          have hcoeff139 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt136
              (Or.inl hcoeff138)
              (Or.inl hcoeff137)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin133]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff138
          · exact hbadNe hcoeff139
          · exact hbadNe hcoeff137
      ·
        have hpin140 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit125 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 2})
          (neighborBlock := {0, 1, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin140]; decide)
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {3, 4, 5})
        (neighborBlock := {2, 4, 5})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)

end Gtz
