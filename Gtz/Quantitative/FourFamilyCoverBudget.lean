import Mathlib
import Gtz.Quantitative.ActiveOverlapPatternsSixThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The four-block cover budget at `(6,3)`

Four card-three blocks carry twelve incidence slots over six atoms, so the
cover counts sum to twelve; under covering every atom is hit at least once,
leaving exactly six units of forced multiplicity.  These are the enumeration
pre-filters of the four-active orbit classifier.
-/

namespace Gtz

/-- The cover count of an atom against four explicit blocks. -/
def fourBlockCoverCount (firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6))
    (atomIndex : Fin 6) : ℕ :=
  (if atomIndex ∈ firstBlock then 1 else 0) + (if atomIndex ∈ secondBlock then 1 else 0)
    + (if atomIndex ∈ thirdBlock then 1 else 0) + (if atomIndex ∈ fourthBlock then 1 else 0)

/-- **Twelve incidence slots**: four card-three blocks have cover counts summing
to twelve, covering or not. -/
theorem sum_fourBlockCoverCount_eq_twelve
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3)
    (hthird : thirdBlock.card = 3) (hfourth : fourthBlock.card = 3) :
    ∑ atomIndex : Fin 6,
        fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      = 12 := by
  simp only [fourBlockCoverCount, Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
  rw [hfirst, hsecond, hthird, hfourth]

/-- Under covering every atom is hit at least once. -/
theorem one_le_fourBlockCoverCount_of_cover
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ)
    (atomIndex : Fin 6) :
    1 ≤ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex := by
  have hmem : atomIndex ∈ firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock := by
    rw [hcover]
    exact Finset.mem_univ atomIndex
  simp only [Finset.mem_union] at hmem
  rcases hmem with ((hbranch | hbranch) | hbranch) | hbranch <;>
    simp [fourBlockCoverCount, hbranch] <;> omega

/-- **The forced-multiplicity budget**: a covering four-family of card-three
blocks spends exactly six units of multiplicity above the floor of one. -/
theorem sum_fourBlockCoverCount_sub_one_eq_six_of_cover
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3)
    (hthird : thirdBlock.card = 3) (hfourth : fourthBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ) :
    ∑ atomIndex : Fin 6,
        (fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex - 1)
      = 6 := by
  have hfloor : ∀ atomIndex : Fin 6,
      1 ≤ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex :=
    one_le_fourBlockCoverCount_of_cover hcover
  have htotal := sum_fourBlockCoverCount_eq_twelve hfirst hsecond hthird hfourth
  have hsplit : ∑ atomIndex : Fin 6,
        fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex
      = ∑ atomIndex : Fin 6,
          ((fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex - 1)
            + 1) := by
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    have := hfloor atomIndex
    omega
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at htotal
  omega

/-- **The doubled-atom pigeonhole**: some atom lies in at least two blocks of a
covering four-family. -/
theorem exists_two_le_fourBlockCoverCount_of_cover
    {firstBlock secondBlock thirdBlock fourthBlock : Finset (Fin 6)}
    (hfirst : firstBlock.card = 3) (hsecond : secondBlock.card = 3)
    (hthird : thirdBlock.card = 3) (hfourth : fourthBlock.card = 3)
    (hcover : firstBlock ∪ secondBlock ∪ thirdBlock ∪ fourthBlock = Finset.univ) :
    ∃ atomIndex : Fin 6,
      2 ≤ fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex := by
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hbudget := sum_fourBlockCoverCount_sub_one_eq_six_of_cover
    hfirst hsecond hthird hfourth hcover
  have hvanish : ∑ atomIndex : Fin 6,
      (fourBlockCoverCount firstBlock secondBlock thirdBlock fourthBlock atomIndex - 1)
        = 0 := by
    refine Finset.sum_eq_zero fun atomIndex _ => ?_
    have := hnone atomIndex
    omega
  rw [hvanish] at hbudget
  exact absurd hbudget (by norm_num)

end Gtz
