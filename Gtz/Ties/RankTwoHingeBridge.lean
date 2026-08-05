/-
# The rank-two hinge, unconditional

Bridges the band lane's tie theorem `not_isTie_of_fourNonParallel` to
`RankTwoFourDirectionHinge`: the `IsTie` disjunction closes via `gtz_rank_two`,
and Lagrange's identity converts `pairBracket /= 0` into `unitPairGram /= 1`
(one direction only; the converse is refuted by `zeroAtomDesign`).
-/
import Mathlib
import Gtz.Ties.RankTwoBand
import Gtz.Design.RankTwoTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Bridge to the branch-(iii) hinge

Two gaps separate the band lane's tie theorem `not_isTie_of_fourNonParallel` from
`RankTwoFourDirectionHinge`, the statement branch (iii) of the `(6,3)` stress
trichotomy actually consumes.  Both close here, unconditionally.

**The disjunction gap.**  `IsTie` is a CONJUNCTION: a weak dominator exists AND no
`k`-subset dominates strictly.  So `¬ IsTie D` is only the DISJUNCTION "no pair
weakly dominates, OR some pair dominates strictly", which is strictly weaker than
the hinge -- the hinge needs the right disjunct alone.  The left disjunct is
refutable outright: `GtzWeighted m 2` says every rank-two design has a weakly
dominating pair, and `Gtz.gtz_rank_two : GtzWeightedAll 2` is a proved theorem of
the tree, hypothesis-free at every size.  The disjunction therefore collapses onto
its right disjunct, which is exactly the hinge's conclusion.

**The dictionary gap.**  The hinge measures non-parallelism by the bracket
(`pairBracket /= 0`); the band lane measures it by the normalized Gram
(`unitPairGram /= 1`).  Lagrange's identity in the plane converts one to the other:

    <u, v>^2 + bracket(u, v)^2 = |u|^2 |v|^2

A nonzero bracket forces the product of leverages to be strictly positive, so the
quotient defining `unitPairGram` is genuine (not the `x / 0 = 0` junk value) and
Cauchy-Schwarz is STRICT, giving `unitPairGram < 1`.

The converse implication is FALSE, and deliberately not claimed: by Lean's
`x / 0 = 0` convention a zero atom has `pairBracket = 0` yet `unitPairGram = 0`,
which is `/= 1`.  So the two non-parallelism measures are NOT equivalent as stated.
The single direction proved below, `pairBracket /= 0 -> unitPairGram /= 1`, is
precisely the one that carries the hinge's hypotheses into the band theorem. -/

/-- **Lagrange's identity in the plane.**  For two rank-two atoms the squared inner
product plus the squared bracket is the product of the leverages.  A polynomial
identity in the four coordinates -- no positivity, no Cauchy-Schwarz input. -/
theorem dotSq_add_pairBracketSq_eq_leverage_mul (D : WeightedDesign m 2)
    (leftLabel rightLabel : Fin m) :
    (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 + pairBracket D leftLabel rightLabel ^ 2
      = leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel) := by
  simp only [pairBracket, leverageOf, dotProduct, Fin.sum_univ_two, Fin.isValue]
  ring

/-- **The non-parallelism dictionary, in the direction the hinge needs.**  A nonzero
bracket forces the normalized Gram off `1`.  Note the leverage product is positive
*because* the bracket is nonzero -- that is what rules out the degenerate
zero-denominator branch, where `unitPairGram` would be the junk value `0`. -/
theorem unitPairGram_ne_one_of_pairBracket_ne_zero (D : WeightedDesign m 2)
    (leftLabel rightLabel : Fin m)
    (hbracket : pairBracket D leftLabel rightLabel ≠ 0) :
    unitPairGram D leftLabel rightLabel ≠ 1 := by
  have hlagrange := dotSq_add_pairBracketSq_eq_leverage_mul D leftLabel rightLabel
  have hbracketSqPos : 0 < pairBracket D leftLabel rightLabel ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hbracket))
  have hdotSqNonneg : (0 : ℝ) ≤ (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2 := sq_nonneg _
  have hdenomPos : 0 < leverageOf (D.atom leftLabel) * leverageOf (D.atom rightLabel) := by
    linarith
  intro hgramOne
  rw [unitPairGram, div_eq_iff (ne_of_gt hdenomPos)] at hgramOne
  linarith

/-- **The disjunction closure.**  `¬ IsTie` collapses to its strict-domination
disjunct, because the weak-domination disjunct is discharged outright by the tree
theorem `Gtz.gtz_rank_two`.  This is where the rank-two case of weighted GTZ --
already a theorem at every size -- does its work. -/
theorem exists_strictlyDominatingPair_of_not_isTie (D : WeightedDesign m 2)
    (hnotTie : ¬ IsTie D) :
    ∃ dominatingPair : Finset (Fin m), dominatingPair.card = 2
      ∧ (subsetSum D dominatingPair - 1).PosDef := by
  by_contra hnoStrictPair
  exact hnotTie ⟨gtz_rank_two m D, fun candidate hcard hposDef =>
    hnoStrictPair ⟨candidate, hcard, hposDef⟩⟩

/-- **THE RANK-TWO FOUR-DIRECTION HINGE, UNCONDITIONAL.**  Four pairwise
non-parallel atoms of a rank-two design force a STRICTLY dominating pair, at every
size, with no hypotheses.  This is the exact `Prop` that
`twoPoleStratumSelection_of_hinge_of_handoff` consumes as its first argument, so
branch (iii) of the `(6,3)` stress trichotomy now rests on the handoff alone. -/
theorem rankTwoFourDirectionHinge_holds : RankTwoFourDirectionHinge := by
  intro size D firstLabel secondLabel thirdLabel fourthLabel
    hone htwo hthree hfour hfive hsix
    hbracketOne hbracketTwo hbracketThree hbracketFour hbracketFive hbracketSix
  exact exists_strictlyDominatingPair_of_not_isTie D
    (not_isTie_of_fourNonParallel D firstLabel secondLabel thirdLabel fourthLabel
      hone htwo hthree hfour hfive hsix
      (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hbracketOne)
      (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hbracketTwo)
      (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hbracketThree)
      (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hbracketFour)
      (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hbracketFive)
      (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hbracketSix))

/-! ## The dictionary is genuinely one-directional

The bridge above proves `pairBracket /= 0 -> unitPairGram /= 1` and pointedly does
NOT claim the converse.  That restraint is necessary, not defensive: the converse is
FALSE, and false on an honest weighted design rather than on a paper edge case.

The witness carries a ZERO atom.  A dead atom is compatible with Parseval provided
the live atoms are scaled up enough to absorb its weight: atoms `(2,0)`, `(0,2)`,
`(0,0)` with weights `1/4, 1/4, 1/2` satisfy

    (1/4)(2e1)(2e1)^T + (1/4)(2e2)(2e2)^T + (1/2) * 0  =  e1 e1^T + e2 e2^T  =  I

with all weights strictly positive and summing to `1`.  At the dead atom the bracket
vanishes while the normalized Gram takes Lean's `x / 0 = 0` junk value `0`, which is
not `1`.  So the two non-parallelism measures disagree on a genuine design, and only
the direction proved above is available to the hinge. -/

/-- A rank-two weighted design carrying a zero atom. -/
noncomputable def zeroAtomDesign : WeightedDesign 3 2 where
  atom := ![![2, 0], ![0, 2], ![0, 0]]
  weight := ![1/4, 1/4, 1/2]
  weight_pos := by
    intro atomLabel
    fin_cases atomLabel <;> norm_num
  weight_sum_one := by
    simp [Fin.sum_univ_three]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [atomMatrix, Matrix.vecMulVec, Fin.sum_univ_three] <;>
      norm_num

/-- The dead atom reads as parallel to atom `0` in the bracket measure. -/
theorem zeroAtomDesign_pairBracket_eq_zero : pairBracket zeroAtomDesign 0 2 = 0 := by
  simp [pairBracket, zeroAtomDesign]

/-- The same pair reads as the junk value `0` in the normalized-Gram measure. -/
theorem zeroAtomDesign_unitPairGram_eq_zero : unitPairGram zeroAtomDesign 0 2 = 0 := by
  simp [unitPairGram, zeroAtomDesign, leverageOf, dotProduct, Fin.sum_univ_two]

/-- **The converse of the non-parallelism dictionary is FALSE**, witnessed by an
actual weighted design.  Hence `pairBracket /= 0` and `unitPairGram /= 1` are NOT
interchangeable hypotheses, and the hinge could only ever have been fed by the
direction proved above. -/
theorem not_forall_pairBracket_ne_zero_of_unitPairGram_ne_one :
    ¬ (∀ (size : ℕ) (D : WeightedDesign size 2) (leftLabel rightLabel : Fin size),
        unitPairGram D leftLabel rightLabel ≠ 1 →
        pairBracket D leftLabel rightLabel ≠ 0) := by
  intro hconverse
  exact hconverse 3 zeroAtomDesign 0 2
    (by rw [zeroAtomDesign_unitPairGram_eq_zero]; norm_num)
    zeroAtomDesign_pairBracket_eq_zero


/-! ## Downstream: branch (iii) rests on the handoff alone -/

/-- The handoff's first argument is discharged by the proved hinge, so branch (iii)
of the `(6,3)` stress trichotomy rests on `StrictCompanionPairClosesTwoPoleSixThree`
alone. -/
theorem twoPoleStratumSelection_of_strictCompanionHandoff
    (hhandoff : StrictCompanionPairClosesTwoPoleSixThree) :
    TwoPoleStratumSelection 6 :=
  twoPoleStratumSelection_of_hinge_of_handoff rankTwoFourDirectionHinge_holds hhandoff

end Gtz
