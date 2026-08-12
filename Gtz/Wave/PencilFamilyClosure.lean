import Gtz.Quantitative.PencilDoorReduction
import Gtz.Wave.CrossSupportedTightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **THE PENCIL FAMILY CLOSES.**  The first of the fifteen canonical
covering four-families dies: on the edge pencil every residual block owns a
private atom outside the selected block, so coverage forces the private atom
into the residual tight support, the three-row cancellation reads zero there
for the other two rows, and all three cancellation coefficients vanish —
against the cancellation's nontriviality.  No support enumeration is needed:
the selected pair stays abstract because the three private atoms lie outside
the whole selected block. -/

/-- The canonical edge pencil, listed. -/
theorem canonicalEdgePencil_eq_literal :
    canonicalEdgePencil
      = ({{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}} :
          Finset (Finset (Fin 6))) := by decide

/-- **THE PENCIL KILL.**  No crux selects the canonical edge pencil. -/
theorem SixThreeCrux.false_of_family_canonicalEdgePencil
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalEdgePencil) :
    False := by
  classical
  have hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]; decide
  obtain ⟨tightVec, multiplier, block, hblockCard, hunit, hEigen, hdata, hblockMem,
    haxes, hsupportTwo, hpositive⟩ :=
    crux.exists_positive_stationary_supportTwo_of_four hfour
  have hcoverage := crux.exists_mem_totalTightSupport_of_positive_multiplier hdata
  have hblockCases : block = {0, 1, 2} ∨ block = {0, 1, 3}
      ∨ block = {0, 1, 4} ∨ block = {0, 1, 5} := by
    have hmem := hblockMem
    rw [hfamily, canonicalEdgePencil_eq_literal] at hmem
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
  · -- selected {0,1,2}: private atoms 3, 4, 5 of {0,1,3}, {0,1,4}, {0,1,5}
    have heraseEq : canonicalEdgePencil.erase {0, 1, 2}
        = ({{0, 1, 3}, {0, 1, 4}, {0, 1, 5}} : Finset (Finset (Fin 6))) := by decide
    have hprivateA : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
    have hprivateB : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
    have hprivateC : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact hcoverAtom
    have hcancelA := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelB := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelC := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
    rw [hfamily, heraseEq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
      at hcancelA hcancelB hcancelC
    have hcoeffA : coefficient {0, 1, 3} = 0 :=
      firstCoeff_eq_zero_of_sum_three hcancelA
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateA))
    have hcoeffB : coefficient {0, 1, 4} = 0 :=
      secondCoeff_eq_zero_of_sum_three hcancelB
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateB))
    have hcoeffC : coefficient {0, 1, 5} = 0 :=
      thirdCoeff_eq_zero_of_sum_three hcancelC
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateC))
    obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
    rw [hfamily, heraseEq] at hbadMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
    rcases hbadMem with rfl | rfl | rfl
    · exact hbadNe hcoeffA
    · exact hbadNe hcoeffB
    · exact hbadNe hcoeffC
  · -- selected {0,1,3}: private atoms 2, 4, 5 of {0,1,2}, {0,1,4}, {0,1,5}
    have heraseEq : canonicalEdgePencil.erase {0, 1, 3}
        = ({{0, 1, 2}, {0, 1, 4}, {0, 1, 5}} : Finset (Finset (Fin 6))) := by decide
    have hprivateA : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
    have hprivateB : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
    have hprivateC : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact hcoverAtom
    have hcancelA := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelB := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelC := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
    rw [hfamily, heraseEq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
      at hcancelA hcancelB hcancelC
    have hcoeffA : coefficient {0, 1, 2} = 0 :=
      firstCoeff_eq_zero_of_sum_three hcancelA
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateA))
    have hcoeffB : coefficient {0, 1, 4} = 0 :=
      secondCoeff_eq_zero_of_sum_three hcancelB
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateB))
    have hcoeffC : coefficient {0, 1, 5} = 0 :=
      thirdCoeff_eq_zero_of_sum_three hcancelC
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateC))
    obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
    rw [hfamily, heraseEq] at hbadMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
    rcases hbadMem with rfl | rfl | rfl
    · exact hbadNe hcoeffA
    · exact hbadNe hcoeffB
    · exact hbadNe hcoeffC
  · -- selected {0,1,4}: private atoms 2, 3, 5 of {0,1,2}, {0,1,3}, {0,1,5}
    have heraseEq : canonicalEdgePencil.erase {0, 1, 4}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 1, 5}} : Finset (Finset (Fin 6))) := by decide
    have hprivateA : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
    have hprivateB : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
    have hprivateC : (5 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 5} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 5
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
      · exact hcoverAtom
    have hcancelA := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelB := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelC := hcancel 5 (fun hmem => absurd (hpairSubset hmem) (by decide))
    rw [hfamily, heraseEq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
      at hcancelA hcancelB hcancelC
    have hcoeffA : coefficient {0, 1, 2} = 0 :=
      firstCoeff_eq_zero_of_sum_three hcancelA
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateA))
    have hcoeffB : coefficient {0, 1, 3} = 0 :=
      secondCoeff_eq_zero_of_sum_three hcancelB
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateB))
    have hcoeffC : coefficient {0, 1, 5} = 0 :=
      thirdCoeff_eq_zero_of_sum_three hcancelC
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateC))
    obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
    rw [hfamily, heraseEq] at hbadMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
    rcases hbadMem with rfl | rfl | rfl
    · exact hbadNe hcoeffA
    · exact hbadNe hcoeffB
    · exact hbadNe hcoeffC
  · -- selected {0,1,5}: private atoms 2, 3, 4 of {0,1,2}, {0,1,3}, {0,1,4}
    have heraseEq : canonicalEdgePencil.erase {0, 1, 5}
        = ({{0, 1, 2}, {0, 1, 3}, {0, 1, 4}} : Finset (Finset (Fin 6))) := by decide
    have hprivateA : (2 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 2} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 2
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    have hprivateB : (3 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 3} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 3
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact hcoverAtom
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    have hprivateC : (4 : Fin 6) ∈ totalTightSupport tightVec {0, 1, 4} := by
      obtain ⟨coverBlock, hcoverMem, hcoverAtom⟩ := hcoverage 4
      rw [hfamily, canonicalEdgePencil_eq_literal] at hcoverMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcoverMem
      rcases hcoverMem with rfl | rfl | rfl | rfl
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact absurd (totalTightSupport_subset tightVec (by decide) hcoverAtom)
          (by decide)
      · exact hcoverAtom
      · rw [hpairEq] at hcoverAtom
        exact absurd (hpairSubset hcoverAtom) (by decide)
    have hcancelA := hcancel 2 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelB := hcancel 3 (fun hmem => absurd (hpairSubset hmem) (by decide))
    have hcancelC := hcancel 4 (fun hmem => absurd (hpairSubset hmem) (by decide))
    rw [hfamily, heraseEq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
      at hcancelA hcancelB hcancelC
    have hcoeffA : coefficient {0, 1, 2} = 0 :=
      firstCoeff_eq_zero_of_sum_three hcancelA
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateA))
    have hcoeffB : coefficient {0, 1, 3} = 0 :=
      secondCoeff_eq_zero_of_sum_three hcancelB
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateB))
    have hcoeffC : coefficient {0, 1, 4} = 0 :=
      thirdCoeff_eq_zero_of_sum_three hcancelC
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (Or.inr (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec
          (by decide) (fun hmem => absurd
            (totalTightSupport_subset tightVec (by decide) hmem) (by decide))))
        (ne_of_gt (totalEigenSquareRow_pos_of_mem_totalTightSupport tightVec
          (by decide) hprivateC))
    obtain ⟨badBlock, hbadMem, hbadNe⟩ := hcoefficientNonzero
    rw [hfamily, heraseEq] at hbadMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbadMem
    rcases hbadMem with rfl | rfl | rfl
    · exact hbadNe hcoeffA
    · exact hbadNe hcoeffB
    · exact hbadNe hcoeffC

end Gtz
