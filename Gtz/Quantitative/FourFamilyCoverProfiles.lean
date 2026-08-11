import Mathlib
import Gtz.Quantitative.FourFamilyCoverBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

/-!
# The multiplicity profiles of a covering four-family

The cover counts of a covering four-family take values in `[1,4]`, six atoms
share them, and they total twelve.  So the profile — how many atoms carry each
count — is one of exactly seven tuples, and this list is the outer case split
of the four-active orbit census.
-/

namespace Gtz

/-- No atom is counted more than four times by four blocks. -/
theorem fourBlockCoverCount_le_four
    (firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6))
    (atomIndex : Fin 6) :
    fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex ≤ 4 := by
  unfold fourBlockCoverCount
  split_ifs <;> omega

/-- The number of atoms carrying a given cover count. -/
def fourBlockCountClass (firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6))
    (countValue : ℕ) : ℕ :=
  (Finset.univ.filter fun atomIndex =>
    fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      = countValue).card

/-- The four count classes of a covering four-family partition the six atoms. -/
theorem sum_fourBlockCountClass_eq_six_of_cover
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ) :
    fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1
        + fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2
        + fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3
        + fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4
      = 6 := by
  classical
  have hclassify : ∀ atomIndex : Fin 6,
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 1
        ∨ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 2
        ∨ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 3
        ∨ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 4 := by
    intro atomIndex
    have hfloor := one_le_fourBlockCoverCount_of_cover hcover atomIndex
    have hceil := fourBlockCoverCount_le_four firstBlock secondBlock thirdBlock fourthBlock
      atomIndex
    omega
  have hcount : ∀ countValue : ℕ,
      fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock countValue
        = ∑ atomIndex : Fin 6,
            (if fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
                = countValue then 1 else 0) := by
    intro countValue
    rw [fourBlockCountClass, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcount, hcount, hcount, hcount, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hterms : ∀ atomIndex ∈ (Finset.univ : Finset (Fin 6)),
      ((if fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 1
          then 1 else 0)
        + (if fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 2
            then 1 else 0)
        + (if fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 3
            then 1 else 0)
        + (if fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 4
            then 1 else 0) : ℕ)
        = 1 := by
    intro atomIndex _
    rcases hclassify atomIndex with hone | htwo | hthree | hfour <;>
      split_ifs <;> omega
  rw [Finset.sum_congr rfl hterms, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

/-- The count classes weigh the twelve incidence slots. -/
theorem weighted_sum_fourBlockCountClass_eq_twelve_of_cover
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3)
    (hthird : thirdBlock.card = 3) (hfourth : fourthBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ) :
    fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1
        + 2 * fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2
        + 3 * fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3
        + 4 * fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4
      = 12 := by
  classical
  have hclassify : ∀ atomIndex : Fin 6,
      fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 1
        ∨ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 2
        ∨ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 3
        ∨ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex = 4 := by
    intro atomIndex
    have hfloor := one_le_fourBlockCoverCount_of_cover hcover atomIndex
    have hceil := fourBlockCoverCount_le_four firstBlock secondBlock thirdBlock fourthBlock
      atomIndex
    omega
  have hcount : ∀ weightValue countValue : ℕ,
      weightValue * fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock countValue
        = ∑ atomIndex : Fin 6,
            (if fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
                = countValue then weightValue else 0) := by
    intro weightValue countValue
    rw [fourBlockCountClass, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    split_ifs <;> omega
  have hone := hcount 1 1
  rw [one_mul] at hone
  rw [hone, hcount 2 2, hcount 3 3, hcount 4 4, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have htotal := sum_fourBlockCoverCount_eq_twelve hfirst hsecond hthird hfourth
  rw [← htotal]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rcases hclassify atomIndex with hone' | htwo' | hthree' | hfour' <;>
    split_ifs <;> omega

/-- The arithmetic core of the profile classification: six parts in `[0,∞)`
summing to six and weighing twelve realise one of seven profiles. -/
theorem fourCoverProfile_arith (quadCount tripleCount doubleCount singleCount : ℕ)
    (hsum : singleCount + doubleCount + tripleCount + quadCount = 6)
    (hweight : singleCount + 2 * doubleCount + 3 * tripleCount + 4 * quadCount = 12) :
    (quadCount, tripleCount, doubleCount, singleCount) = (0, 0, 6, 0)
      ∨ (quadCount, tripleCount, doubleCount, singleCount) = (0, 1, 4, 1)
      ∨ (quadCount, tripleCount, doubleCount, singleCount) = (0, 2, 2, 2)
      ∨ (quadCount, tripleCount, doubleCount, singleCount) = (0, 3, 0, 3)
      ∨ (quadCount, tripleCount, doubleCount, singleCount) = (1, 0, 3, 2)
      ∨ (quadCount, tripleCount, doubleCount, singleCount) = (1, 1, 1, 3)
      ∨ (quadCount, tripleCount, doubleCount, singleCount) = (2, 0, 0, 4) := by
  have hquadBound : quadCount ≤ 2 := by omega
  have htripleBound : tripleCount ≤ 3 := by omega
  rcases quadCount with _ | _ | _ | quadRest <;>
    rcases tripleCount with _ | _ | _ | _ | tripleRest <;>
    first
    | (left; simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)
    | (right; left; simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)
    | (right; right; left; simp only [Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)
    | (right; right; right; left; simp only [Prod.mk.injEq];
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)
    | (right; right; right; right; left; simp only [Prod.mk.injEq];
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)
    | (right; right; right; right; right; left; simp only [Prod.mk.injEq];
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)
    | (right; right; right; right; right; right; simp only [Prod.mk.injEq];
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | omega)

/-- **THE SEVEN MULTIPLICITY PROFILES.**  A covering four-family of card-three
blocks realises exactly one of seven count profiles `(#4s, #3s, #2s, #1s)` —
the outer case split of the four-active orbit census. -/
theorem fourBlockCountClass_profile_of_cover
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3)
    (hthird : thirdBlock.card = 3) (hfourth : fourthBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ) :
    (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
      fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
      fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
      fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
        = (0, 0, 6, 0)
      ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
        = (0, 1, 4, 1)
      ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
        = (0, 2, 2, 2)
      ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
        = (0, 3, 0, 3)
      ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
        = (1, 0, 3, 2)
      ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
        = (1, 1, 1, 3)
      ∨ (fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 4,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 3,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 2,
          fourBlockCountClass firstBlock secondBlock thirdBlock fourthBlock 1)
        = (2, 0, 0, 4) := by
  have hpartition := sum_fourBlockCountClass_eq_six_of_cover hcover
  have hweighted := weighted_sum_fourBlockCountClass_eq_twelve_of_cover
    hfirst hsecond hthird hfourth hcover
  exact fourCoverProfile_arith _ _ _ _ hpartition hweighted

end Gtz
