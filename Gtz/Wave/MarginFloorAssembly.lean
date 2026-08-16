import Gtz.Wave.QuantitativeMarginBounds
import Gtz.Wave.ProjectionMinorShift
import Gtz.Design.TripleGramSylvester

/-!
# The margin floor, assembled end to end

`Gtz.QuantitativeMarginBounds` converts a block determinant into a margin level.
This file supplies the two things that conversion still needed to reach the
campaign's scalar vocabulary, and then reads off two exact averaged laws that say
how much room a floor argument actually has.

**The Gram identification.**  The projection block determinant is the selected
Gram determinant scaled by the weight product, and the selected Gram determinant
is `Gtz.tripleGapDet`.  The first half is shipped.  The second half was named as
an open gap — matching `Gtz.selectedAtomRows` to `Gtz.tripleGram` entrywise — and
`Gtz.selectedAtomRows_mul_transpose_eq_tripleGram` closes it.  Composing the two
gives `Gtz.det_pickBlockGap_eq_weightProd_mul_tripleGapDet`, so every scalar cell
in surplus-and-pairing vocabulary reaches the margin object.

**The end-to-end floor.**  `Gtz.marginReaches_of_lt_weightProd_mul_signFreeMargin`
turns a sign-free margin into a margin level, and the shipped sharp sum cell then
supplies an explicit number for it.  That is a polynomial cell producing a
quantitative floor, which is what a conditional-floor argument consumes.

**How much room there is.**  Two exact laws bound the arithmetic.  The weighted
pair-minor mass is exactly `(rank - 1)` times `Gtz.shiftLeverage`
(`Gtz.sum_weighted_pairMinor_eq`), and `Gtz.shiftLeverage` is at most one.  The
shipped Cauchy-Binet total puts the block-determinant mass at exactly one.  So
the mass a linear bound subtracts can reach twice the mass it adds, and
`Gtz.linearMass_le_and_two_mul_shiftLeverage` states that comparison.  This is
why the linear reading cannot be certified by averaging, and it is an exact
statement rather than a census.

**A counting law.**  At `(6,3)` the six excesses total two, so a selection and
its complement split that total.  One of the two always carries at least one
(`Gtz.one_le_excessSum_or_compl`), so at least half of the twenty selections have
a positive first Sylvester minor with room to spare.
-/

namespace Gtz

open Matrix Finset

variable {size : ℕ}

/-! ## 1. The Gram identification -/

/-- **THE NAMED GAP, CLOSED.**  The selected row matrix times its transpose IS
the triple Gram of the three selected atoms.  Both sides are the pairwise dot
products, and three-by-three case analysis identifies them. -/
theorem selectedAtomRows_mul_transpose_eq_tripleGram (design : WeightedDesign size 3)
    (pick : Fin 3 → Fin size) :
    selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ
      = tripleGram (design.atom (pick 0)) (design.atom (pick 1)) (design.atom (pick 2)) := by
  ext left right
  rw [tripleGram_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selectedAtomRows, Matrix.of_apply,
    dotProduct]
  fin_cases left <;> fin_cases right <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **THE FULL DETERMINANT CHAIN.**  The block gap determinant is the weight
product times the scalar third minor of the three selected atoms. -/
theorem det_pickBlockGap_eq_weightProd_mul_tripleGapDet (design : WeightedDesign size 3)
    (pick : Fin 3 → Fin size) :
    (pickBlockGap design pick).det
      = (∏ slot, design.weight (pick slot))
        * tripleGapDet (design.atom (pick 0)) (design.atom (pick 1)) (design.atom (pick 2)) := by
  rw [det_pickBlockGap_eq_weightProd_mul_gramDet design pick,
    selectedAtomRows_mul_transpose_eq_tripleGram design pick, det_tripleGram_sub_one]

/-- The same, read in surplus-and-pairing vocabulary. -/
theorem det_pickBlockGap_eq_weightProd_mul_tripleDetForm (design : WeightedDesign size 3)
    (pick : Fin 3 → Fin size) :
    (pickBlockGap design pick).det
      = (∏ slot, design.weight (pick slot))
        * tripleDetForm (leverageOf (design.atom (pick 0)) - 1)
            (leverageOf (design.atom (pick 1)) - 1) (leverageOf (design.atom (pick 2)) - 1)
            (design.atom (pick 0) ⬝ᵥ design.atom (pick 1))
            (design.atom (pick 0) ⬝ᵥ design.atom (pick 2))
            (design.atom (pick 1) ⬝ᵥ design.atom (pick 2)) := by
  rw [det_pickBlockGap_eq_weightProd_mul_tripleGapDet design pick, tripleGapDet_eq_tripleDetForm]

/-! ## 2. The sign-free margin reaches the margin object -/

/-- **THE END-TO-END FLOOR.**  A sign-free margin at the three selected atoms,
scaled by the weight product, is a margin level for the whole design. -/
theorem marginReaches_of_lt_weightProd_mul_signFreeMargin (design : WeightedDesign size 3)
    (pick : Fin 3 → Fin size) (hinj : Function.Injective pick)
    (hpsd : (pickBlockGap design pick).PosSemidef) {level : ℝ}
    (hlevel : level < (∏ slot, design.weight (pick slot))
      * signFreeMargin (leverageOf (design.atom (pick 0)) - 1)
          (leverageOf (design.atom (pick 1)) - 1) (leverageOf (design.atom (pick 2)) - 1)
          (design.atom (pick 0) ⬝ᵥ design.atom (pick 1))
          (design.atom (pick 0) ⬝ᵥ design.atom (pick 2))
          (design.atom (pick 1) ⬝ᵥ design.atom (pick 2))) :
    MarginReaches (projectionOfDesign design) design.weight 3 level := by
  refine marginReaches_of_lt_det_pickBlockGap design pick hinj hpsd ?_
  rw [det_pickBlockGap_eq_weightProd_mul_tripleDetForm design pick]
  refine lt_of_lt_of_le hlevel ?_
  exact mul_le_mul_of_nonneg_left (signFreeMargin_le_tripleDetForm _ _ _ _ _ _)
    (weightProd_pos design pick).le

/-! ## 3. Two exact averaged laws -/

variable {rank : ℕ}

/-- **THE WEIGHTED PAIR-MINOR MASS.**  Summing the pair minors of the projection
against their own row weight gives exactly `(rank - 1)` times the weighted
leverage.  The engine is the shipped row law, which is where idempotence enters. -/
theorem sum_weighted_pairMinor_eq (design : WeightedDesign size rank) :
    ∑ label : Fin size, ∑ other : Fin size,
        design.weight label * pairMinorAt (projectionOfDesign design) label other
      = ((rank : ℝ) - 1) * shiftLeverage design := by
  rw [shiftLeverage, Finset.mul_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [← Finset.mul_sum, sum_pairMinor_projection design label]
  ring

/-- The weighted leverage is at most one: the diagonal entries of a projection sit
in the unit interval and the weights sum to one. -/
theorem shiftLeverage_le_one (design : WeightedDesign size rank) :
    shiftLeverage design ≤ 1 := by
  have hbound : ∀ label : Fin size,
      design.weight label * projectionOfDesign design label label ≤ design.weight label := by
    intro label
    have hdiag := projectionDiagonal_le_one' design label
    nlinarith [design.weight_pos label, hdiag]
  calc shiftLeverage design
      = ∑ label : Fin size, design.weight label * projectionOfDesign design label label := rfl
    _ ≤ ∑ label : Fin size, design.weight label :=
        Finset.sum_le_sum fun label _ => hbound label
    _ = 1 := design.weight_sum_one

/-- **THE MASS COMPARISON.**  The shipped Cauchy-Binet total puts the
block-determinant mass at exactly one.  The mass a linear reading subtracts is
exactly `(rank - 1)` times the weighted leverage, hence at most `rank - 1`.  At
rank three that is two against one, so the subtracted mass can be twice the added
mass and an averaged certificate of the linear reading is impossible. -/
theorem linearMass_le_and_two_mul_shiftLeverage (design : WeightedDesign size rank)
    (hrank : 1 ≤ rank) :
    ∑ label : Fin size, ∑ other : Fin size,
        design.weight label * pairMinorAt (projectionOfDesign design) label other
      ≤ (rank : ℝ) - 1 := by
  rw [sum_weighted_pairMinor_eq design]
  have hnonneg : (0 : ℝ) ≤ (rank : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
    linarith
  nlinarith [shiftLeverage_le_one design, hnonneg]

/-! ## 4. The complementary split of the excess total -/

/-- The six excesses of a `(6,3)` design total exactly two: the projection
diagonal sums to the rank and the weights sum to one. -/
theorem sum_excess_sixThree (design : WeightedDesign 6 3) :
    ∑ label : Fin 6,
        (projectionOfDesign design label label - design.weight label) = 2 := by
  rw [Finset.sum_sub_distrib, sum_projectionDiagonal_eq_rank design, design.weight_sum_one]
  norm_num

/-- **THE COMPLEMENTARY SPLIT.**  A selection and its complement divide the
excess total of two, so one of them always carries at least one.  At least half
of the twenty selections therefore clear the first Sylvester minor with a full
unit of room. -/
theorem one_le_excessSum_or_compl (design : WeightedDesign 6 3) (selected : Finset (Fin 6)) :
    1 ≤ ∑ label ∈ selected,
          (projectionOfDesign design label label - design.weight label)
      ∨ 1 ≤ ∑ label ∈ selectedᶜ,
          (projectionOfDesign design label label - design.weight label) := by
  have hsplit : (∑ label ∈ selected,
        (projectionOfDesign design label label - design.weight label))
      + ∑ label ∈ selectedᶜ,
        (projectionOfDesign design label label - design.weight label) = 2 := by
    rw [Finset.sum_add_sum_compl]
    exact sum_excess_sixThree design
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hleft, hright⟩ := hcontra
  linarith

end Gtz
