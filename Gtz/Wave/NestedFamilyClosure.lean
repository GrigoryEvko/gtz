import Gtz.Quantitative.FifteenFamilyDispatch
import Gtz.Wave.CrossSupportedTightExit
import Gtz.Wave.FullRowTriangleKill
import Gtz.Wave.FourFamilyTypeEightExit
import Gtz.Wave.WeightedColumnSupportBridge
import Gtz.Wave.StationaryRelabelTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The orbitFour family, listed. -/
theorem orbitFourFamily_eq_literal :
    orbitFourFamily
      = ({{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 4, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE ORBITFOUR KILL.**  No crux selects this family. -/
theorem SixThreeCrux.false_of_family_orbitFourFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = orbitFourFamily) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 1, 3} ∨ block = {0, 2, 3} ∨ block = {1, 4, 5} := by
    have hmem := hblockMem
    rw [hfamily, orbitFourFamily_eq_literal] at hmem
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
    have heraseEq : orbitFourFamily.erase {0, 1, 2}
        = ({{0, 1, 3}, {0, 2, 3}, {1, 4, 5}} :
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
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 2})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {1, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 2} :=
        hpairEq.symm.trans hpairPin
      have hcov1 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      have hcov2 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      by_cases hmemSplit3 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
      ·
        by_cases hmemSplit4 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
        ·
          by_cases hmemSplit5 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
          ·
            by_cases hmemSplit6 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
            ·
              by_cases hmemSplit7 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
              ·
                by_cases hmemSplit8 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
                ·
                  by_cases hmemSplit9 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5}
                  ·
                    have hfullPin10 : totalTightSupport tightVec {0, 1, 3} = {0, 1, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit3
                      · exact hmemSplit4
                      · exact hmemSplit5
                    have hfullPin11 : totalTightSupport tightVec {0, 2, 3} = {0, 2, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit6
                      · exact hmemSplit7
                      · exact hmemSplit8
                    have hfullPin12 : totalTightSupport tightVec {1, 4, 5} = {1, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit9
                      · exact hcov1
                      · exact hcov2
                    have horbitRange : Finset.univ.image orbitFourLabel
                        = chartArgmaxFamily (chartPointOfDesign crux.design) := by
                      rw [hfamily]
                      exact orbitFourLabel_range
                    refine crux.false_of_orbitFour_typeNineSupports hfamily hdata ?_ ?_ ?_ ?_
                    · show orbitFourWeightedColumnSupport
                        (fourFamilyWeightedTightColumns orbitFourLabel multiplier (ambientTightSelection tightVec)) 0 = _
                      rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport horbitRange hfour hdata 0 (by decide)]
                      show totalTightSupport tightVec {0, 1, 2} = _
                      rw [hpairPin]
                    · show orbitFourWeightedColumnSupport
                        (fourFamilyWeightedTightColumns orbitFourLabel multiplier (ambientTightSelection tightVec)) 1 = _
                      rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport horbitRange hfour hdata 1 (by decide)]
                      show totalTightSupport tightVec {0, 1, 3} = _
                      rw [hfullPin10]
                    · show orbitFourWeightedColumnSupport
                        (fourFamilyWeightedTightColumns orbitFourLabel multiplier (ambientTightSelection tightVec)) 2 = _
                      rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport horbitRange hfour hdata 2 (by decide)]
                      show totalTightSupport tightVec {0, 2, 3} = _
                      rw [hfullPin11]
                    · show orbitFourWeightedColumnSupport
                        (fourFamilyWeightedTightColumns orbitFourLabel multiplier (ambientTightSelection tightVec)) 3 = _
                      rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport horbitRange hfour hdata 3 (by decide)]
                      show totalTightSupport tightVec {1, 4, 5} = _
                      rw [hfullPin12]
                  ·
                    have hpin13 : totalTightSupport tightVec {1, 4, 5} = {4, 5} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 4, 5} (by decide)) hmemSplit9 (by decide)
                    have hisoA14 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({1, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 4 = 0 := by
                      intro other hother hne
                      rw [hfamily, orbitFourFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    have hisoB15 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({1, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 5 = 0 := by
                      intro other hother hne
                      rw [hfamily, orbitFourFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin13
                      hisoA14 hisoB15
                ·
                  have hpin16 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit8 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 2, 3})
                    (neighborBlock := {0, 1, 2})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin16]; decide)
              ·
                have hpin17 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit7 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 2, 3})
                  (neighborBlock := {0, 1, 3})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin17]; decide)
            ·
              have hpin18 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit6 (by decide)
              have hcancelAt19 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt20 := hcancel 3 (by rw [hpairSetEq]; decide)
              have hcancelAt21 := hcancel 4 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt19 hcancelAt20 hcancelAt21
              have hcoeff22 : coefficient {0, 1, 3} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt19
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin18] at hmem; exact absurd hmem (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit3))
              have hcoeff23 : coefficient {0, 2, 3} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt20
                  (Or.inl hcoeff22)
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin18]; decide)))
              have hcoeff24 : coefficient {1, 4, 5} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt21
                  (Or.inl hcoeff22)
                  (Or.inl hcoeff23)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff22
              · exact hbadNe hcoeff23
              · exact hbadNe hcoeff24
          ·
            have hpin25 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit5 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 3})
              (neighborBlock := {0, 1, 2})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin25]; decide)
        ·
          have hpin26 : totalTightSupport tightVec {0, 1, 3} = {0, 3} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit4 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 3})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin26]; decide)
      ·
        have hpin27 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit3 (by decide)
        have hcov28 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpin27] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt29 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt30 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt31 := hcancel 3 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt29 hcancelAt30 hcancelAt31
        have hcoeff32 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt29
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin27] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov28))
        have hcoeff33 : coefficient {1, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt30
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff32)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov1))
        have hcoeff34 : coefficient {0, 1, 3} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt31
            (Or.inl hcoeff32)
            (Or.inl hcoeff33)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin27]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff34
        · exact hbadNe hcoeff32
        · exact hbadNe hcoeff33
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 1, 3}
    have heraseEq : orbitFourFamily.erase {0, 1, 3}
        = ({{0, 1, 2}, {0, 2, 3}, {1, 4, 5}} :
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
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 1, 3})
        (neighborBlock := {0, 2, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {1, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov35 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      have hcov36 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact hcoverAtom
      by_cases hmemSplit37 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit38 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
        ·
          by_cases hmemSplit39 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
          ·
            by_cases hmemSplit40 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
            ·
              by_cases hmemSplit41 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
              ·
                by_cases hmemSplit42 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
                ·
                  by_cases hmemSplit43 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5}
                  ·
                    have hfullPin44 : totalTightSupport tightVec {0, 1, 2} = {0, 1, 2} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit37
                      · exact hmemSplit38
                      · exact hmemSplit39
                    have hfullPin45 : totalTightSupport tightVec {0, 2, 3} = {0, 2, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit40
                      · exact hmemSplit41
                      · exact hmemSplit42
                    have hfullPin46 : totalTightSupport tightVec {1, 4, 5} = {1, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit43
                      · exact hcov35
                      · exact hcov36
                    have hdataSwap := crux.isChartStationaryData_relabel
                      (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) hdata
                    refine SixThreeCrux.false_of_orbitFour_typeNineSupports
                      (crux.relabel (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6))) ?_ hdataSwap ?_ ?_ ?_ ?_
                    · have hfamilySwap := chartArgmaxFamily_relabelDesign crux.design
                        (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6))
                      rw [hfamily] at hfamilySwap
                      exact hfamilySwap.trans (by decide)
                    · rw [orbitFourWeightedColumnSupport_relabel_eq (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) tightVec multiplier 0 (by decide)
                        (hpositive _ (by rw [hfamily]; decide)),
                        show ((orbitFourLabel 0).map (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)).toEmbedding)
                          = ({0, 1, 3} : Finset (Fin 6)) from by decide,
                        hpairPin]
                      decide
                    · rw [orbitFourWeightedColumnSupport_relabel_eq (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) tightVec multiplier 1 (by decide)
                        (hpositive _ (by rw [hfamily]; decide)),
                        show ((orbitFourLabel 1).map (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)).toEmbedding)
                          = ({0, 1, 2} : Finset (Fin 6)) from by decide,
                        hfullPin44]
                      decide
                    · rw [orbitFourWeightedColumnSupport_relabel_eq (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) tightVec multiplier 2 (by decide)
                        (hpositive _ (by rw [hfamily]; decide)),
                        show ((orbitFourLabel 2).map (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)).toEmbedding)
                          = ({0, 2, 3} : Finset (Fin 6)) from by decide,
                        hfullPin45]
                      decide
                    · rw [orbitFourWeightedColumnSupport_relabel_eq (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) tightVec multiplier 3 (by decide)
                        (hpositive _ (by rw [hfamily]; decide)),
                        show ((orbitFourLabel 3).map (⟨![0, 1, 3, 2, 4, 5], ![0, 1, 3, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)).toEmbedding)
                          = ({1, 4, 5} : Finset (Fin 6)) from by decide,
                        hfullPin46]
                      decide
                  ·
                    have hpin47 : totalTightSupport tightVec {1, 4, 5} = {4, 5} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 4, 5} (by decide)) hmemSplit43 (by decide)
                    have hisoA48 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({1, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 4 = 0 := by
                      intro other hother hne
                      rw [hfamily, orbitFourFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    have hisoB49 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({1, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 5 = 0 := by
                      intro other hother hne
                      rw [hfamily, orbitFourFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact absurd rfl hne
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin47
                      hisoA48 hisoB49
                ·
                  have hpin50 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit42 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 2, 3})
                    (neighborBlock := {0, 1, 2})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin50]; decide)
              ·
                have hpin51 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit41 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 2, 3})
                  (neighborBlock := {0, 1, 3})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin51]; decide)
            ·
              have hpin52 : totalTightSupport tightVec {0, 2, 3} = {2, 3} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit40 (by decide)
              have hcancelAt53 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt54 := hcancel 2 (by rw [hpairSetEq]; decide)
              have hcancelAt55 := hcancel 4 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt53 hcancelAt54 hcancelAt55
              have hcoeff56 : coefficient {0, 1, 2} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt53
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin52] at hmem; exact absurd hmem (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit37))
              have hcoeff57 : coefficient {0, 2, 3} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt54
                  (Or.inl hcoeff56)
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin52]; decide)))
              have hcoeff58 : coefficient {1, 4, 5} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt55
                  (Or.inl hcoeff56)
                  (Or.inl hcoeff57)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov35))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff56
              · exact hbadNe hcoeff57
              · exact hbadNe hcoeff58
          ·
            have hpin59 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit39 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 2})
              (neighborBlock := {0, 1, 3})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin59]; decide)
        ·
          have hpin60 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit38 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 2})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin60]; decide)
      ·
        have hpin61 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit37 (by decide)
        have hcov62 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin61] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt63 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt64 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt65 := hcancel 2 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt63 hcancelAt64 hcancelAt65
        have hcoeff66 : coefficient {0, 2, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt63
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin61] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov62))
        have hcoeff67 : coefficient {1, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt64
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff66)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov35))
        have hcoeff68 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt65
            (Or.inl hcoeff66)
            (Or.inl hcoeff67)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin61]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff68
        · exact hbadNe hcoeff66
        · exact hbadNe hcoeff67
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {0, 2, 3}
    have heraseEq : orbitFourFamily.erase {0, 2, 3}
        = ({{0, 1, 2}, {0, 1, 3}, {1, 4, 5}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {0, 2}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 2} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 3})
        (neighborBlock := {0, 1, 2})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {0, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {0, 3} :=
        hpairEq.symm.trans hpairPin
      exact crux.false_of_totalTightSupport_subset_neighbor
        (hostBlock := {0, 2, 3})
        (neighborBlock := {0, 1, 3})
        hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
        (by decide) hdata (by rw [hpairPin]; decide)
    · -- pair {2, 3}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {2, 3} :=
        hpairEq.symm.trans hpairPin
      have hcov69 : (4 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
        rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      have hcov70 : (5 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5} := by
        obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
        rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
        rcases hcoverMem with rfl | rfl | rfl | rfl
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        · rw [hpairPin] at hcoverAtom
          exact absurd hcoverAtom (by decide)
        · exact hcoverAtom
      by_cases hmemSplit71 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit72 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
        ·
          by_cases hmemSplit73 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
          ·
            by_cases hmemSplit74 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
            ·
              by_cases hmemSplit75 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
              ·
                by_cases hmemSplit76 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
                ·
                  by_cases hmemSplit77 : (1 : Fin 6) ∈ totalTightSupport tightVec {1, 4, 5}
                  ·
                    have hfullPin78 : totalTightSupport tightVec {0, 1, 2} = {0, 1, 2} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit71
                      · exact hmemSplit72
                      · exact hmemSplit73
                    have hfullPin79 : totalTightSupport tightVec {0, 1, 3} = {0, 1, 3} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit74
                      · exact hmemSplit75
                      · exact hmemSplit76
                    have hfullPin80 : totalTightSupport tightVec {1, 4, 5} = {1, 4, 5} := by
                      refine Finset.Subset.antisymm (totalTightSupport_subset tightVec (by decide)) ?_
                      intro atom hatom
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hatom
                      rcases hatom with rfl | rfl | rfl
                      · exact hmemSplit77
                      · exact hcov69
                      · exact hcov70
                    have hrangeT8 : Finset.univ.image
                        (![{0, 2, 3}, {0, 1, 2}, {0, 1, 3}, {1, 4, 5}] : Fin 4 → Finset (Fin 6))
                        = orbitFourFamily := by decide
                    have hfamilyT8 : chartArgmaxFamily (chartPointOfDesign crux.design) = Finset.univ.image
                        (![{0, 2, 3}, {0, 1, 2}, {0, 1, 3}, {1, 4, 5}] : Fin 4 → Finset (Fin 6)) := by
                      rw [hfamily, hrangeT8]
                    refine crux.false_of_fourFamily_typeEightSupports
                      (chartArgmaxFamily (chartPointOfDesign crux.design))
                      (![{0, 2, 3}, {0, 1, 2}, {0, 1, 3}, {1, 4, 5}] : Fin 4 → Finset (Fin 6))
                      hfamilyT8.symm (by decide)
                      (⟨![1, 2, 3, 0, 4, 5], ![3, 0, 1, 2, 4, 5], by decide, by decide⟩ : Equiv.Perm (Fin 6)) rfl hdata ?_ ?_ ?_ ?_
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 0 (by decide)]
                      show totalTightSupport tightVec {0, 2, 3} = _
                      rw [hpairPin]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 1 (by decide)]
                      show totalTightSupport tightVec {0, 1, 2} = _
                      rw [hfullPin78]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 2 (by decide)]
                      show totalTightSupport tightVec {0, 1, 3} = _
                      rw [hfullPin79]
                      decide
                    · rw [crux.fourFamilyWeightedColumnSupport_eq_totalTightSupport hfamilyT8.symm hfour hdata 3 (by decide)]
                      show totalTightSupport tightVec {1, 4, 5} = _
                      rw [hfullPin80]
                      decide
                  ·
                    have hpin81 : totalTightSupport tightVec {1, 4, 5} = {4, 5} :=
                      eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                      (crux.two_le_card_totalTightSupport tightVec hunit hEigen {1, 4, 5} (by decide)) hmemSplit77 (by decide)
                    have hisoA82 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({1, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 4 = 0 := by
                      intro other hother hne
                      rw [hfamily, orbitFourFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact absurd rfl hne
                    have hisoB83 : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
                        otherBlock ≠ ({1, 4, 5} : Finset (Fin 6)) → totalEigenSquareRow tightVec otherBlock 5 = 0 := by
                      intro other hother hne
                      rw [hfamily, orbitFourFamily_eq_literal] at hother
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hother
                      rcases hother with rfl | rfl | rfl | rfl
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · exact totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide)
                          (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                      · refine totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) ?_
                        rw [hpairPin]
                        decide
                      · exact absurd rfl hne
                    exact crux.false_of_isolated_pair_row (by decide) hdata
                      (by rw [hfamily]; decide)
                      hpin81
                      hisoA82 hisoB83
                ·
                  have hpin84 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit76 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 1, 3})
                    (neighborBlock := {0, 1, 2})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin84]; decide)
              ·
                have hpin85 : totalTightSupport tightVec {0, 1, 3} = {0, 3} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit75 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 1, 3})
                  (neighborBlock := {0, 2, 3})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin85]; decide)
            ·
              have hpin86 : totalTightSupport tightVec {0, 1, 3} = {1, 3} :=
                eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit74 (by decide)
              have hcancelAt87 := hcancel 0 (by rw [hpairSetEq]; decide)
              have hcancelAt88 := hcancel 4 (by rw [hpairSetEq]; decide)
              have hcancelAt89 := hcancel 1 (by rw [hpairSetEq]; decide)
              rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                Finset.sum_insert (by decide), Finset.sum_singleton]
                at hcancelAt87 hcancelAt88 hcancelAt89
              have hcoeff90 : coefficient {0, 1, 2} = 0 :=
                firstCoeff_eq_zero_of_sum_three hcancelAt87
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin86] at hmem; exact absurd hmem (by decide))))
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit71))
              have hcoeff91 : coefficient {1, 4, 5} = 0 :=
                thirdCoeff_eq_zero_of_sum_three hcancelAt88
                  (Or.inl hcoeff90)
                  (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov69))
              have hcoeff92 : coefficient {0, 1, 3} = 0 :=
                secondCoeff_eq_zero_of_sum_three hcancelAt89
                  (Or.inl hcoeff90)
                  (Or.inl hcoeff91)
                  (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin86]; decide)))
              obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
              rw [hfamily, heraseEq] at hbadMem
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
              rcases hbadMem with rfl | rfl | rfl
              · exact hbadNe hcoeff90
              · exact hbadNe hcoeff92
              · exact hbadNe hcoeff91
          ·
            have hpin93 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
              eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit73 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 2})
              (neighborBlock := {0, 1, 3})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin93]; decide)
        ·
          have hpin94 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
            eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit72 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 2})
            (neighborBlock := {0, 2, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin94]; decide)
      ·
        have hpin95 : totalTightSupport tightVec {0, 1, 2} = {1, 2} :=
          eq_pair_of_notMem_first (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit71 (by decide)
        have hcov96 : (0 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
          obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 0
          rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
          rcases hcoverMem with rfl | rfl | rfl | rfl
          · rw [hpin95] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact hcoverAtom
          · rw [hpairPin] at hcoverAtom
            exact absurd hcoverAtom (by decide)
          · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
        have hcancelAt97 := hcancel 0 (by rw [hpairSetEq]; decide)
        have hcancelAt98 := hcancel 4 (by rw [hpairSetEq]; decide)
        have hcancelAt99 := hcancel 1 (by rw [hpairSetEq]; decide)
        rw [hfamily, heraseEq, Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
          at hcancelAt97 hcancelAt98 hcancelAt99
        have hcoeff100 : coefficient {0, 1, 3} = 0 :=
          secondCoeff_eq_zero_of_sum_three hcancelAt97
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => by rw [hpin95] at hmem; exact absurd hmem (by decide))))
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov96))
        have hcoeff101 : coefficient {1, 4, 5} = 0 :=
          thirdCoeff_eq_zero_of_sum_three hcancelAt98
            (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
            (Or.inl hcoeff100)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hcov69))
        have hcoeff102 : coefficient {0, 1, 2} = 0 :=
          firstCoeff_eq_zero_of_sum_three hcancelAt99
            (Or.inl hcoeff100)
            (Or.inl hcoeff101)
            (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) (by rw [hpin95]; decide)))
        obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
        rw [hfamily, heraseEq] at hbadMem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
        rcases hbadMem with rfl | rfl | rfl
        · exact hbadNe hcoeff102
        · exact hbadNe hcoeff100
        · exact hbadNe hcoeff101
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)
  · -- selected {1, 4, 5}
    have heraseEq : orbitFourFamily.erase {1, 4, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 2, 3}} :
            Finset (Finset (Fin 6))) := by decide
    rcases support_quadrichotomy (totalTightSupport_subset tightVec hblockCard)
        (le_of_eq hsupportTwo.symm) (by decide) (by decide) (by decide)
      with hpairPin | hpairPin | hpairPin | hpairPin
    · -- pair {1, 4}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 4} :=
        hpairEq.symm.trans hpairPin
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairPin] at hcoverAtom
        exact absurd hcoverAtom (by decide)
    · -- pair {1, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {1, 5} :=
        hpairEq.symm.trans hpairPin
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, orbitFourFamily_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom) (by decide)
      · rw [hpairPin] at hcoverAtom
        exact absurd hcoverAtom (by decide)
    · -- pair {4, 5}
      have hpairSetEq : ({pairFirst, pairSecond} : Finset (Fin 6)) = {4, 5} :=
        hpairEq.symm.trans hpairPin
      by_cases hmemSplit103 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
      ·
        by_cases hmemSplit104 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2}
        ·
          by_cases hmemSplit105 : (1 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
          ·
            by_cases hmemSplit106 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3}
            ·
              by_cases hmemSplit107 : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
              ·
                by_cases hmemSplit108 : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 2, 3}
                ·
                  have hcancelAt109 := hcancel 1 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt109
                  have hrowZero110 : totalEigenSquareRow tightVec {0, 2, 3} 1 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm111 : coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 1 = 0 := by
                    rw [hrowZero110]; ring
                  have hmeet112 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 1
                      + coefficient {0, 1, 3} * totalEigenSquareRow tightVec {0, 1, 3} 1 = 0 := by
                    linarith [hcancelAt109, hdeadTerm111]
                  have hcancelAt113 := hcancel 3 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt113
                  have hrowZero114 : totalEigenSquareRow tightVec {0, 1, 2} 3 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm115 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 3 = 0 := by
                    rw [hrowZero114]; ring
                  have hmeet116 : coefficient {0, 1, 3} * totalEigenSquareRow tightVec {0, 1, 3} 3
                      + coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 3 = 0 := by
                    linarith [hcancelAt113, hdeadTerm115]
                  have hcancelAt117 := hcancel 2 (by rw [hpairSetEq]; decide)
                  rw [hfamily, heraseEq, Finset.sum_insert (by decide),
                    Finset.sum_insert (by decide), Finset.sum_singleton] at hcancelAt117
                  have hrowZero118 : totalEigenSquareRow tightVec {0, 1, 3} 2 = 0 :=
                    totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec (by decide) (fun hmem => absurd (totalTightSupport_subset tightVec (by decide) hmem) (by decide))
                  have hdeadTerm119 : coefficient {0, 1, 3} * totalEigenSquareRow tightVec {0, 1, 3} 2 = 0 := by
                    rw [hrowZero118]; ring
                  have hmeet120 : coefficient {0, 1, 2} * totalEigenSquareRow tightVec {0, 1, 2} 2
                      + coefficient {0, 2, 3} * totalEigenSquareRow tightVec {0, 2, 3} 2 = 0 := by
                    linarith [hcancelAt117, hdeadTerm119]
                  refine false_of_oppositeSign_triangle hmeet112 hmeet116 hmeet120
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit103)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit105)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit106)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit108)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit104)
                    (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec (by decide) hmemSplit107) ?_
                  obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
                  rw [hfamily, heraseEq] at hbadMem
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
                  rcases hbadMem with rfl | rfl | rfl
                  · exact Or.inl hbadNe
                  · exact Or.inr (Or.inl hbadNe)
                  · exact Or.inr (Or.inr hbadNe)
                ·
                  have hpin121 : totalTightSupport tightVec {0, 2, 3} = {0, 2} :=
                    eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                    (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit108 (by decide)
                  exact crux.false_of_totalTightSupport_subset_neighbor
                    (hostBlock := {0, 2, 3})
                    (neighborBlock := {0, 1, 2})
                    hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                    (by decide) hdata (by rw [hpin121]; decide)
              ·
                have hpin122 : totalTightSupport tightVec {0, 2, 3} = {0, 3} :=
                  eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
                  (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 2, 3} (by decide)) hmemSplit107 (by decide)
                exact crux.false_of_totalTightSupport_subset_neighbor
                  (hostBlock := {0, 2, 3})
                  (neighborBlock := {0, 1, 3})
                  hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                  (by decide) hdata (by rw [hpin122]; decide)
            ·
              have hpin123 : totalTightSupport tightVec {0, 1, 3} = {0, 1} :=
                eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
                (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit106 (by decide)
              exact crux.false_of_totalTightSupport_subset_neighbor
                (hostBlock := {0, 1, 3})
                (neighborBlock := {0, 1, 2})
                hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
                (by decide) hdata (by rw [hpin123]; decide)
          ·
            have hpin124 : totalTightSupport tightVec {0, 1, 3} = {0, 3} :=
              eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
              (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 3} (by decide)) hmemSplit105 (by decide)
            exact crux.false_of_totalTightSupport_subset_neighbor
              (hostBlock := {0, 1, 3})
              (neighborBlock := {0, 2, 3})
              hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
              (by decide) hdata (by rw [hpin124]; decide)
        ·
          have hpin125 : totalTightSupport tightVec {0, 1, 2} = {0, 1} :=
            eq_pair_of_notMem_third (totalTightSupport_subset tightVec (by decide))
            (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit104 (by decide)
          exact crux.false_of_totalTightSupport_subset_neighbor
            (hostBlock := {0, 1, 2})
            (neighborBlock := {0, 1, 3})
            hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
            (by decide) hdata (by rw [hpin125]; decide)
      ·
        have hpin126 : totalTightSupport tightVec {0, 1, 2} = {0, 2} :=
          eq_pair_of_notMem_second (totalTightSupport_subset tightVec (by decide))
          (crux.two_le_card_totalTightSupport tightVec hunit hEigen {0, 1, 2} (by decide)) hmemSplit103 (by decide)
        exact crux.false_of_totalTightSupport_subset_neighbor
          (hostBlock := {0, 1, 2})
          (neighborBlock := {0, 2, 3})
          hfour (by rw [hfamily]; decide) (by rw [hfamily]; decide)
          (by decide) hdata (by rw [hpin126]; decide)
    · -- full support contradicts card two
      rw [hpairPin] at hsupportTwo
      exact absurd hsupportTwo (by decide)

end Gtz
