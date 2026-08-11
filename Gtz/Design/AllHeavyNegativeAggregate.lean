import Gtz.Design.LineBranchFreePairAggregateBridge
import Gtz.Design.TightLineBranchLivePairBridge
import Gtz.Design.UThreeSixStratumWitness
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.KFourChartClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# An all-heavy design whose free-pair row aggregate is negative

`Gtz.exists_live_freePair_of_atMostOneNonheavy_of_rowAggregate_pos` turns a
POSITIVE free-pair row aggregate into a live free pair, and the conditional
tight-line hinge wants exactly that.  What the tree could not answer is whether
the aggregate is positive whenever it is needed.  The only design it could point
at was `Gtz.freePairKillerDesign`, whose aggregate is `-315/128` but which
carries FIVE strictly dominating one-slot swaps -- and a design that already wins
on a one-slot swap says nothing about the branch where no one-slot swap wins.  It
also has an atom at leverage exactly one, so it does not even meet the all-heavy
hypothesis.

This file supplies the missing design.  Every one of its six atoms is HEAVY
(leverage strictly above one), so the "at most one nonheavy" hypothesis holds in
its strongest form; the aggregate is `-619627/2610432`, strictly negative; the
base triple `{0,1,2}` dominates with a singular gap and the tight direction
`(1,1,6)` in its kernel; the design is line-free and off-conic; and NO one-slot
swap strictly dominates, while the distance-two exchange `{1,3,5}` does.

WHAT THIS REFUTES, PRECISELY.  Not the landed bridge -- that bridge is an
implication out of a positive aggregate and stays true.  What dies is the
conjecture that the aggregate is positive on the branch, in the flat form and in
the all-heavy repair alike.  The strict triples here are all DISTANCE-TWO, so the
branch conclusion is reached by a route the aggregate never sees.

WHAT THIS IS NOT.  It is not a counterexample to GTZ: a strict card-three subset
exists, so the design dominates strictly.  It refutes one proposed mechanism for
producing such a subset, not its existence.

THE LEVERAGES are `3/2, 55/2, 43/2, 31/18, 65/36, 43/18` and the strict triples
are exactly `{1,3,5}`, `{1,4,5}`, `{2,3,5}`, `{2,4,5}`.
-/

namespace Gtz

open Matrix

/-- The six atoms.  All lie on the affine plane `z = 1`. -/
noncomputable def allHeavyNegativeAggregateAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![-(1 / 2), 1 / 2, 1]
  | 1 => ![-(9 / 2), -(5 / 2), 1]
  | 2 => ![-(1 / 2), -(9 / 2), 1]
  | 3 => ![5 / 6, -(1 / 6), 1]
  | 4 => ![5 / 6, -(1 / 3), 1]
  | 5 => ![-(5 / 6), 5 / 6, 1]

/-- The six weights.  They sum to one exactly. -/
noncomputable def allHeavyNegativeAggregateWeight : Fin 6 → ℝ
  | 0 => 19817 / 90640
  | 1 => 193 / 9064
  | 2 => 697 / 22660
  | 3 => 5913 / 18128
  | 4 => 387 / 2266
  | 5 => 1053 / 4532

/-- The all-heavy negative-aggregate design: Parseval exact, all weights positive. -/
noncomputable def allHeavyNegativeAggregateDesign : WeightedDesign 6 3 where
  atom := allHeavyNegativeAggregateAtom
  weight := allHeavyNegativeAggregateWeight
  weight_pos := by
    intro label; fin_cases label <;> norm_num [allHeavyNegativeAggregateWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]; norm_num [allHeavyNegativeAggregateWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [allHeavyNegativeAggregateAtom, allHeavyNegativeAggregateWeight, atomMatrix,
        Matrix.cons_val_two] <;>
      norm_num

/-! ## The antecedent: line-free, off-conic, dominating base, tight direction -/

/-- **LINE-FREE.**  All twenty triples have nonzero bracket; the smallest in
absolute value is `1/6`, at the triple `{0,4,5}`. -/
theorem allHeavyNegativeAggregateDesign_hasLinePattern :
    HasLinePattern allHeavyNegativeAggregateDesign
      (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, allHeavyNegativeAggregateDesign,
            allHeavyNegativeAggregateAtom, Matrix.cons_val_two])
          (by decide)

/-- **OFF-CONIC.**  The only symmetric form annihilating all six atoms is zero.
For the record the Veronese determinant is `22660/243` IN THIS TREE'S
CONVENTION, which is the UNDOUBLED one: `Gtz.veroneseCoords` is
`(x^2, y^2, z^2, xy, xz, yz)` with no factor two on the cross terms.  The
previously published figure here was `181280/243`, which is the same
determinant taken in the DOUBLED convention `(.., 2xy, 2xz, 2yz)`; the two
differ by exactly `2^3 = 8`, since doubling three of the six coordinates
multiplies the six-by-six coordinate determinant by `2^3`.  Both are nonzero, so
off-conicity was never in doubt -- only the label was. -/
theorem allHeavyNegativeAggregateDesign_hasNoCommonQuadric :
    HasNoCommonQuadric allHeavyNegativeAggregateDesign.atom := by
  intro form hsymmetric hquadric
  have hsym : ∀ rowIndex colIndex : Fin 3, form colIndex rowIndex = form rowIndex colIndex :=
    fun rowIndex colIndex => congrFun (congrFun hsymmetric rowIndex) colIndex
  have hzero := hquadric 0
  have hone := hquadric 1
  have htwo := hquadric 2
  have hthree := hquadric 3
  have hfour := hquadric 4
  have hfive := hquadric 5
  simp only [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, dotProduct,
    Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hzero hone htwo hthree hfour hfive
  simp only [hsym 0 1, hsym 0 2, hsym 1 2] at hzero hone htwo hthree hfour hfive
  have hcornerZero : form 0 0 = 0 := by linarith
  have hmidZero : form 1 1 = 0 := by linarith
  have hlastZero : form 2 2 = 0 := by linarith
  have hcrossZero : form 0 1 = 0 := by linarith
  have hupZero : form 0 2 = 0 := by linarith
  have hsideZero : form 1 2 = 0 := by linarith
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.zero_apply] <;>
    first
      | exact hcornerZero
      | exact hmidZero
      | exact hlastZero
      | exact hcrossZero
      | exact hupZero
      | exact hsideZero
      | exact (hsym 0 1).trans hcrossZero
      | exact (hsym 0 2).trans hupZero
      | exact (hsym 1 2).trans hsideZero

/-- The base gap in closed form. -/
theorem allHeavyNegativeAggregateDesign_baseGap_eq :
    subsetSum allHeavyNegativeAggregateDesign {0, 1, 2} - 1
      = !![79 / 4, 53 / 4, -(11 / 2);
           53 / 4, 103 / 4, -(13 / 2);
           -(11 / 2), -(13 / 2), 2] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.cons_val_two] <;>
    norm_num

/-- The base gap as a sum of two squares, with a vanishing third pivot.  The two
pivots are `79/4` and `1332/79`; the third is exactly zero, which is why the base
triple is tight rather than strict. -/
theorem allHeavyNegativeAggregateDesign_baseGap_form (probeVec : Fin 3 → ℝ) :
    probeVec ⬝ᵥ ((subsetSum allHeavyNegativeAggregateDesign {0, 1, 2} - 1) *ᵥ probeVec)
      = (79 / 4) * (probeVec 0 + (53 / 79) * probeVec 1 - (22 / 79) * probeVec 2) ^ 2
        + (1332 / 79) * (probeVec 1 - (1 / 6) * probeVec 2) ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]
  ring

/-- **THE BASE TRIPLE DOMINATES.** -/
theorem allHeavyNegativeAggregateDesign_dominates_base :
    Dominates allHeavyNegativeAggregateDesign {0, 1, 2} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 6)) fun baseLabel _ =>
      posSemidef_atomMatrix (allHeavyNegativeAggregateDesign.atom baseLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, allHeavyNegativeAggregateDesign_baseGap_form]
    positivity

/-- **THE TIGHT DIRECTION.**  The base gap kills `(1,1,6)`: both pivots vanish
there simultaneously. -/
theorem allHeavyNegativeAggregateDesign_isTightDirection :
    IsTightDirectionOf allHeavyNegativeAggregateDesign {0, 1, 2} ![1, 1, 6] := by
  rw [IsTightDirectionOf, allHeavyNegativeAggregateDesign_baseGap_form]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-! ## Every atom is heavy -/

/-- **ALL SIX ATOMS ARE HEAVY.**  The leverages are
`3/2, 55/2, 43/2, 31/18, 65/36, 43/18`, every one strictly above one, so the
"at most one nonheavy" hypothesis of the aggregate route holds in its strongest
possible form. -/
theorem allHeavyNegativeAggregateDesign_allHeavy (label : Fin 6) :
    0 < gapExcessOf allHeavyNegativeAggregateDesign label := by
  fin_cases label <;>
    simp [gapExcessOf, leverageOf, allHeavyNegativeAggregateDesign,
      allHeavyNegativeAggregateAtom, Fin.sum_univ_three] <;>
    norm_num

/-! ## The aggregate is on the wrong side -/

/-- **THE FREE-PAIR ROW AGGREGATE IS NEGATIVE**, at `-619627/2610432`. -/
theorem allHeavyNegativeAggregateDesign_freePairRowAggregate_neg :
    freePairRowAggregate allHeavyNegativeAggregateDesign < 0 := by
  simp only [freePairRowAggregate, pairRowAggregateOn, freeThreeLabel, pairGapExcessOf,
    gapExcessOf, gapPairingOf, leverageOf, Fin.sum_univ_three, Finset.sum_erase_eq_sub,
    Finset.mem_univ, dotProduct, allHeavyNegativeAggregateDesign,
    allHeavyNegativeAggregateAtom, allHeavyNegativeAggregateWeight, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-! ## The branch holds: a distance-two exchange strictly dominates -/

/-- The distance-two triple `{1,3,5}` has gap with leading minors
`743/36`, `1195/81`, `299/27`. -/
theorem allHeavyNegativeAggregateDesign_gap_oneThreeFive_eq :
    subsetSum allHeavyNegativeAggregateDesign {1, 3, 5} - 1
      = !![743 / 36, 125 / 12, -(9 / 2);
           125 / 12, 215 / 36, -(11 / 6);
           -(9 / 2), -(11 / 6), 2] := by
  rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.cons_val_two] <;>
    norm_num

/-- **THE BRANCH HOLDS.**  The distance-two exchange `{1,3,5}` strictly
dominates, so this design is NOT a counterexample to GTZ -- it is a
counterexample to the aggregate mechanism only. -/
theorem allHeavyNegativeAggregateDesign_gap_oneThreeFive_posDef :
    (subsetSum allHeavyNegativeAggregateDesign {1, 3, 5} - 1).PosDef := by
  rw [allHeavyNegativeAggregateDesign_gap_oneThreeFive_eq]
  exact posDef_of_leadingMinors_fin_three _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)

/-- A strict card-three subset exists. -/
theorem allHeavyNegativeAggregateDesign_exists_posDef_cardThree :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (subsetSum allHeavyNegativeAggregateDesign selected - 1).PosDef :=
  ⟨{1, 3, 5}, by decide, allHeavyNegativeAggregateDesign_gap_oneThreeFive_posDef⟩

/-! ## No one-slot swap wins -/

/-- **NO ONE-SLOT SWAP STRICTLY DOMINATES.**  Each of the nine candidates is
killed by an explicit probe of nonpositive Rayleigh value.  The candidate
`{1,2,5}` is killed by the tight direction `(1,1,6)` itself, at Rayleigh exactly
zero.  This is the conjunct `Gtz.freePairKillerDesign` cannot supply. -/
theorem allHeavyNegativeAggregateDesign_not_tightLineOneSlotFamily :
    ¬ TightLineOneSlotFamily allHeavyNegativeAggregateDesign := by
  rintro ⟨swapOut, hswapOut, swapIn, hswapIn, hposDef⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hswapOut hswapIn
  have hswapInCases : swapIn = 3 ∨ swapIn = 4 ∨ swapIn = 5 := by
    fin_cases swapIn <;> simp_all
  obtain rfl | rfl | rfl := hswapOut <;>
    obtain rfl | rfl | rfl := hswapInCases
  · -- swapOut = 0, swapIn = 3: the triple is {1,2,3}, Rayleigh -5/9
    rw [show (insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0))
        = ({1, 2, 3} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![0, 2, 7]
      (fun hzero => absurd (congrFun hzero 1) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 0, swapIn = 4: the triple is {1,2,4}, Rayleigh -7/18
    rw [show (insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0))
        = ({1, 2, 4} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![0, 1, 3]
      (fun hzero => absurd (congrFun hzero 1) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 0, swapIn = 5: the triple is {1,2,5}, Rayleigh 0
    rw [show (insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 0))
        = ({1, 2, 5} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![1, 1, 6]
      (fun hzero => absurd (congrFun hzero 0) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 1, swapIn = 3: the triple is {0,2,3}, Rayleigh -5/36
    rw [show (insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1))
        = ({0, 2, 3} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-(6), 1, 1]
      (fun hzero => absurd (congrFun hzero 0) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 1, swapIn = 4: the triple is {0,2,4}, Rayleigh -5/36
    rw [show (insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1))
        = ({0, 2, 4} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-(15), 2, 3]
      (fun hzero => absurd (congrFun hzero 0) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 1, swapIn = 5: the triple is {0,2,5}, Rayleigh -53/36
    rw [show (insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 1))
        = ({0, 2, 5} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![1, 0, 1]
      (fun hzero => absurd (congrFun hzero 0) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 2, swapIn = 3: the triple is {0,1,3}, Rayleigh -41/36
    rw [show (insert (3 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2))
        = ({0, 1, 3} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![1, -(2), 0]
      (fun hzero => absurd (congrFun hzero 0) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 2, swapIn = 4: the triple is {0,1,4}, Rayleigh -1/4
    rw [show (insert (4 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2))
        = ({0, 1, 4} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![1, -(2), 0]
      (fun hzero => absurd (congrFun hzero 0) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · -- swapOut = 2, swapIn = 5: the triple is {0,1,5}, Rayleigh -14/9
    rw [show (insert (5 : Fin 6) ((({0, 1, 2} : Finset (Fin 6))).erase 2))
        = ({0, 1, 5} : Finset (Fin 6)) from by decide] at hposDef
    revert hposDef
    refine not_posDef_of_dotProduct_mulVec_nonpos _ ![1, -(1), 1]
      (fun hzero => absurd (congrFun hzero 0) (by norm_num)) ?_
    rw [subsetSum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num [allHeavyNegativeAggregateDesign, allHeavyNegativeAggregateAtom, atomMatrix,
      Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      Matrix.add_apply, Matrix.one_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

end Gtz
