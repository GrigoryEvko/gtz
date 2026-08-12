import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The ThreeTriple family, listed. -/
theorem canonicalThreeTripleFamily_eq_literal :
    canonicalThreeTripleFamily
      = ({{0, 1, 2}, {1, 2, 5}, {0, 2, 4}, {0, 1, 3}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE THREETRIPLE KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_canonicalThreeTripleFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalThreeTripleFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {1, 2, 5} ∨ block = {0, 2, 4} ∨ block = {0, 1, 3} := by
    have hmem := hblockMem
    rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hmem
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
    have heraseEq : canonicalThreeTripleFamily.erase {0, 1, 2}
        = ({{1, 2, 5}, {0, 2, 4}, {0, 1, 3}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov1 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    have hcov2 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    have hcov3 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    have hcancelAt4 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelAt5 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelAt6 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
    rw [hfamily, heraseEq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
      at hcancelAt4 hcancelAt5 hcancelAt6
    have hcoeff7 : coefficient {1, 2, 5} = 0 :=
      firstCoeff_eq_zero_of_sum_three hcancelAt4
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov3))
    have hcoeff8 : coefficient {0, 2, 4} = 0 :=
      secondCoeff_eq_zero_of_sum_three hcancelAt5
        (Or.inl hcoeff7)
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov2))
    have hcoeff9 : coefficient {0, 1, 3} = 0 :=
      thirdCoeff_eq_zero_of_sum_three hcancelAt6
        (Or.inl hcoeff7)
        (Or.inl hcoeff8)
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
    obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
    rw [hfamily, heraseEq] at hbadMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
    rcases hbadMem with rfl | rfl | rfl
    · exact hbadNe hcoeff7
    · exact hbadNe hcoeff8
    · exact hbadNe hcoeff9
  · -- selected {1, 2, 5}
    have heraseEq : canonicalThreeTripleFamily.erase {1, 2, 5}
        = ({{0, 1, 2}, {0, 2, 4}, {0, 1, 3}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov10 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
    have hcov11 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    by_cases hmemSplit12 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      have hcancelAt13 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt14 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt15 := hcancel 0 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt13 hcancelAt14 hcancelAt15
      have hcoeff16 : coefficient {0, 2, 4} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt13
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov11))
      have hcoeff17 : coefficient {0, 1, 3} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt14
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inl hcoeff16)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov10))
      have hcoeff18 : coefficient {0, 1, 2} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt15
          (Or.inl hcoeff16)
          (Or.inl hcoeff17)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit12))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff18
      · exact hbadNe hcoeff16
      · exact hbadNe hcoeff17
    ·
      have hpin19 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
        eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit12 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {1, 2, 5})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin19]; decide)
  · -- selected {0, 2, 4}
    have heraseEq : canonicalThreeTripleFamily.erase {0, 2, 4}
        = ({{0, 1, 2}, {1, 2, 5}, {0, 1, 3}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov20 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
    have hcov21 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
    by_cases hmemSplit22 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      have hcancelAt23 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt24 := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt25 := hcancel 1 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt23 hcancelAt24 hcancelAt25
      have hcoeff26 : coefficient {1, 2, 5} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt23
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov21))
      have hcoeff27 : coefficient {0, 1, 3} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt24
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inl hcoeff26)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov20))
      have hcoeff28 : coefficient {0, 1, 2} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt25
          (Or.inl hcoeff26)
          (Or.inl hcoeff27)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit22))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff28
      · exact hbadNe hcoeff26
      · exact hbadNe hcoeff27
    ·
      have hpin29 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
        eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit22 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 2, 4})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin29]; decide)
  · -- selected {0, 1, 3}
    have heraseEq : canonicalThreeTripleFamily.erase {0, 1, 3}
        = ({{0, 1, 2}, {1, 2, 5}, {0, 2, 4}} :
            Finset (Finset (Fin 6))) := by decide
    have hcov30 : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    have hcov31 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 2, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalThreeTripleFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    by_cases hmemSplit32 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
    ·
      have hcancelAt33 := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt34 := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
      have hcancelAt35 := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
      rw [hfamily, heraseEq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
        at hcancelAt33 hcancelAt34 hcancelAt35
      have hcoeff36 : coefficient {1, 2, 5} = 0 :=
        secondCoeff_eq_zero_of_sum_three hcancelAt33
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov31))
      have hcoeff37 : coefficient {0, 2, 4} = 0 :=
        thirdCoeff_eq_zero_of_sum_three hcancelAt34
          (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
          (Or.inl hcoeff36)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov30))
      have hcoeff38 : coefficient {0, 1, 2} = 0 :=
        firstCoeff_eq_zero_of_sum_three hcancelAt35
          (Or.inl hcoeff36)
          (Or.inl hcoeff37)
          (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit32))
      obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
      rw [hfamily, heraseEq] at hbadMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
      rcases hbadMem with rfl | rfl | rfl
      · exact hbadNe hcoeff38
      · exact hbadNe hcoeff36
      · exact hbadNe hcoeff37
    ·
      have hpin39 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
        eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
        (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit32 (by decide)
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpin39]; decide)

end Gtz
