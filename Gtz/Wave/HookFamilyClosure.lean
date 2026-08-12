import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The Hook family, listed. -/
theorem canonicalHookFamily_eq_literal :
    canonicalHookFamily
      = ({{0, 1, 2}, {0, 1, 3}, {1, 2, 4}, {0, 4, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE HOOK KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalHookFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalHookFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 1, 3} ∨ block = {1, 2, 4} ∨ block = {0, 4, 5} := by
    have hmem := hblockMem
    rw [hfamily, canonicalHookFamily_eq_literal] at hmem
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
    have heraseEq : canonicalHookFamily.erase {0, 1, 2}
        = ({{0, 1, 3}, {1, 2, 4}, {0, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov1 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    have hcov2 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit3 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 4}
    ·
      have hcancelAt4 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt5 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt6 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt4 hcancelAt5 hcancelAt6
      have hcoeff7 : coefficient {0, 1, 3} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt4
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
      have hcoeff8 : coefficient {0, 4, 5} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt5
          (Or.inl hcoeff7)
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov2))
      have hcoeff9 : coefficient {1, 2, 4} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt6
          (Or.inl hcoeff7)
          (Or.inl hcoeff8)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff7
      · exact hbadNe hcoeff9
      · exact hbadNe hcoeff8
    ·
      have hpin10 : totalTightSupport tightVec {1, 2, 4} = {1, 2} :=
        eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 4} (by decide)) hmemSplit3 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {1, 2, 4})
        (neighborBlock := {0, 1, 2})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin10]; decide)
  · -- selected {0, 1, 3}
    have heraseEq : canonicalHookFamily.erase {0, 1, 3}
        = ({{0, 1, 2}, {1, 2, 4}, {0, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov11 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit12 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      by_cases hmemSplit13 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 4}
      ·
        have hcancelAt14 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt15 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
        have hcancelAt16 := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt14 hcancelAt15 hcancelAt16
        have hcoeff17 : coefficient {0, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt14
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov11))
        have hcoeff18 : coefficient {1, 2, 4} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt15
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff17)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit13))
        have hcoeff19 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt16
            (Or.inl hcoeff18)
            (Or.inl hcoeff17)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit12))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff19
        · exact hbadNe hcoeff18
        · exact hbadNe hcoeff17
      ·
        have hpin20 : totalTightSupport tightVec {1, 2, 4} = {1, 2} :=
          eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 4} (by decide)) hmemSplit13 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {1, 2, 4})
          (neighborBlock := {0, 1, 2})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin20]; decide)
    ·
      have hpin21 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
        eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit12 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin21]; decide)
  · -- selected {1, 2, 4}
    have heraseEq : canonicalHookFamily.erase {1, 2, 4}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov22 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    have hcov23 : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 4, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
    by_cases hmemSplit24 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      have hcancelAt25 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt26 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt27 := hcancel 0 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt25 hcancelAt26 hcancelAt27
      have hcoeff28 : coefficient {0, 1, 3} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt25
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov22))
      have hcoeff29 : coefficient {0, 4, 5} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt26
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inl hcoeff28)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov23))
      have hcoeff30 : coefficient {0, 1, 2} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt27
          (Or.inl hcoeff28)
          (Or.inl hcoeff29)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit24))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff30
      · exact hbadNe hcoeff28
      · exact hbadNe hcoeff29
    ·
      have hpin31 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
        eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit24 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {1, 2, 4})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin31]; decide)
  · -- selected {0, 4, 5}
    have heraseEq : canonicalHookFamily.erase {0, 4, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {1, 2, 4}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 4} :=
        hpairEq.symm.trans hpairPin
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairPin] at hcoverAtom
        exact absurd hcoverAtom (by decide)
    · -- pair {0, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov32 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      have hcov33 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 4} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit34 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        have hcancelAt35 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt36 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt37 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt35 hcancelAt36 hcancelAt37
        have hcoeff38 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt35
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov32))
        have hcoeff39 : coefficient {1, 2, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt36
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff38)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov33))
        have hcoeff40 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt37
            (Or.inl hcoeff38)
            (Or.inl hcoeff39)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit34))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff40
        · exact hbadNe hcoeff38
        · exact hbadNe hcoeff39
      ·
        have hpin41 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit34 (by decide)
        have hcancelAt42 := hcancel 3 (by rw [hpairSetEq]; decide)
        have hcancelAt43 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt44 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt42 hcancelAt43 hcancelAt44
        have hcoeff45 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt42
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov32))
        have hcoeff46 : coefficient {1, 2, 4} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt43
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff45)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov33))
        have hcoeff47 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt44
            (Or.inl hcoeff45)
            (Or.inl hcoeff46)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin41]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff47
        · exact hbadNe hcoeff45
        · exact hbadNe hcoeff46
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      have hcov48 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
        rw [hfamily, canonicalHookFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
      by_cases hmemSplit49 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit50 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 4}
        ·
          have hcancelAt51 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt52 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt53 := hcancel 1 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt51 hcancelAt52 hcancelAt53
          have hcoeff54 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt51
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov48))
          have hcoeff55 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt52
              (Or.inl hcoeff54)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit49))
          have hcoeff56 : coefficient {1, 2, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt53
              (Or.inl hcoeff55)
              (Or.inl hcoeff54)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit50))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff55
          · exact hbadNe hcoeff54
          · exact hbadNe hcoeff56
        ·
          have hpin57 : totalTightSupport tightVec {1, 2, 4} = {2, 4} :=
            eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 2, 4} (by decide)) hmemSplit50 (by decide)
          have hcancelAt58 := hcancel 3 (by rw [hpairSetEq]; decide)
          have hcancelAt59 := hcancel 0 (by rw [hpairSetEq]; decide)
          have hcancelAt60 := hcancel 2 (by rw [hpairSetEq]; decide)
          rw [hfamily, heraseEq, Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
            at hcancelAt58 hcancelAt59 hcancelAt60
          have hcoeff61 : coefficient {0, 1, 3} = 0 :=
            secondCoeff_eq_zero_of_sum_three hcancelAt58
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov48))
          have hcoeff62 : coefficient {0, 1, 2} = 0 :=
            firstCoeff_eq_zero_of_sum_three hcancelAt59
              (Or.inl hcoeff61)
              (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit49))
          have hcoeff63 : coefficient {1, 2, 4} = 0 :=
            thirdCoeff_eq_zero_of_sum_three hcancelAt60
              (Or.inl hcoeff62)
              (Or.inl hcoeff61)
              (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin57]; decide)))
          obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
          rw [hfamily, heraseEq] at hbadMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
          rcases hbadMem with rfl | rfl | rfl
          · exact hbadNe hcoeff62
          · exact hbadNe hcoeff61
          · exact hbadNe hcoeff63
      ·
        have hpin64 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit49 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 2})
          (neighborBlock := {1, 2, 4})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin64]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)

end Gtz
