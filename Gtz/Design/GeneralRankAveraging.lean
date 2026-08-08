import Gtz.Design.RhoNormalForm
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Quantitative.ChartHadamard
import Gtz.Ties.RankTwoMassCircuit
import Gtz.Design.StressCertificate
import Gtz.Reduction.BranchTransferConstants
import Gtz.Quantitative.TieRowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-- The **gap excess** of an atom at ANY rank: the diagonal of `Gram - I`. -/
def gapExcessOf (D : WeightedDesign m k) (atomLabel : Fin m) : ℝ :=
  leverageOf (D.atom atomLabel) - 1

/-- The **gap pairing** of two atoms at ANY rank: the off-diagonal of `Gram - I`. -/
def gapPairingOf (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) : ℝ :=
  D.atom leftLabel ⬝ᵥ D.atom rightLabel

/-- The **pair gap excess**: the two by two leading minor of `Gram - I` at a pair. -/
def pairGapExcessOf (D : WeightedDesign m k) (firstLabel secondLabel : Fin m) : ℝ :=
  gapExcessOf D firstLabel * gapExcessOf D secondLabel
    - gapPairingOf D firstLabel secondLabel ^ 2

/-- The **triple gap form** of a pivot against a pair: minus the three by three
determinant of `Gram - I` on the triple. -/
def tripleGapForm (D : WeightedDesign m k)
    (pivotLabel firstLabel secondLabel : Fin m) : ℝ :=
  gapExcessOf D secondLabel * gapPairingOf D pivotLabel firstLabel ^ 2
    - 2 * gapPairingOf D firstLabel secondLabel * gapPairingOf D pivotLabel firstLabel
        * gapPairingOf D pivotLabel secondLabel
    + gapExcessOf D firstLabel * gapPairingOf D pivotLabel secondLabel ^ 2
    - pairGapExcessOf D firstLabel secondLabel * gapExcessOf D pivotLabel

theorem gapExcessOf_eq_heavyExcess (D : WeightedDesign m 3) (atomLabel : Fin m) :
    gapExcessOf D atomLabel = heavyExcess D atomLabel := rfl

theorem gapPairingOf_eq_atomPairing (D : WeightedDesign m 3)
    (leftLabel rightLabel : Fin m) :
    gapPairingOf D leftLabel rightLabel = atomPairing D leftLabel rightLabel := rfl

/-- At rank three the triple gap form is exactly minus the tree's `discriminantTie`. -/
theorem tripleGapForm_eq_neg_discriminantTie (D : WeightedDesign m 3)
    (pivotLabel firstLabel secondLabel : Fin m) :
    tripleGapForm D pivotLabel firstLabel secondLabel
      = - discriminantTie D pivotLabel firstLabel secondLabel := by
  simp only [tripleGapForm, pairGapExcessOf, gapExcessOf, gapPairingOf, discriminantTie,
    heavyExcess, atomPairing]
  ring

/-! ## The three Parseval consequences, at any rank -/

theorem sum_weight_mul_gapExcessOf (D : WeightedDesign m k) :
    ∑ pivotLabel, D.weight pivotLabel * gapExcessOf D pivotLabel = (k : ℝ) - 1 :=
  sum_weight_mul_leverage_sub_one D

theorem sum_weight_mul_gapPairingOf_sq (D : WeightedDesign m k) (atomLabel : Fin m) :
    ∑ pivotLabel, D.weight pivotLabel * gapPairingOf D pivotLabel atomLabel ^ 2
      = leverageOf (D.atom atomLabel) := by
  have hshipped := dotProduct_self_eq_sum_weight_mul_sq D (D.atom atomLabel)
  rw [← leverageOf_eq_dotProduct] at hshipped
  simpa [gapPairingOf] using hshipped.symm

theorem sum_weight_mul_gapPairingOf_cross (D : WeightedDesign m k)
    (firstLabel secondLabel : Fin m) :
    ∑ pivotLabel, D.weight pivotLabel
        * (gapPairingOf D pivotLabel firstLabel * gapPairingOf D pivotLabel secondLabel)
      = gapPairingOf D firstLabel secondLabel := by
  have hshipped := dotProduct_eq_sum_weight_mul_pair D (D.atom firstLabel)
    (D.atom secondLabel)
  simpa [gapPairingOf] using hshipped.symm

/-! ## The averaging identity, at any rank -/

/-- **THE GENERAL-RANK AVERAGING IDENTITY.**  The weighted average of the triple
gap form over ALL pivots is a function of the pair alone.  Three Parseval
consequences carry it; the rank enters only through the excess budget. -/
theorem sum_weight_mul_tripleGapForm (D : WeightedDesign m k)
    (firstLabel secondLabel : Fin m) :
    ∑ pivotLabel, D.weight pivotLabel * tripleGapForm D pivotLabel firstLabel secondLabel
      = (3 - (k : ℝ)) * pairGapExcessOf D firstLabel secondLabel
        + gapExcessOf D firstLabel + gapExcessOf D secondLabel := by
  have hexpand : ∀ pivotLabel : Fin m,
      D.weight pivotLabel * tripleGapForm D pivotLabel firstLabel secondLabel
        = gapExcessOf D secondLabel
            * (D.weight pivotLabel * gapPairingOf D pivotLabel firstLabel ^ 2)
          - 2 * gapPairingOf D firstLabel secondLabel
              * (D.weight pivotLabel
                  * (gapPairingOf D pivotLabel firstLabel
                      * gapPairingOf D pivotLabel secondLabel))
          + gapExcessOf D firstLabel
              * (D.weight pivotLabel * gapPairingOf D pivotLabel secondLabel ^ 2)
          - pairGapExcessOf D firstLabel secondLabel
              * (D.weight pivotLabel * gapExcessOf D pivotLabel) := by
    intro pivotLabel
    rw [tripleGapForm]
    ring
  rw [Finset.sum_congr rfl fun pivotLabel _ => hexpand pivotLabel]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_weight_mul_gapPairingOf_sq, sum_weight_mul_gapPairingOf_cross,
    sum_weight_mul_gapPairingOf_sq, sum_weight_mul_gapExcessOf]
  simp only [pairGapExcessOf, gapExcessOf, gapPairingOf]
  ring

/-! ## The two diagonal values, rank-independent -/

theorem gapPairingOf_self (D : WeightedDesign m k) (atomLabel : Fin m) :
    gapPairingOf D atomLabel atomLabel = gapExcessOf D atomLabel + 1 := by
  simp only [gapPairingOf, gapExcessOf, ← leverageOf_eq_dotProduct]
  ring

theorem gapPairingOf_comm (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    gapPairingOf D leftLabel rightLabel = gapPairingOf D rightLabel leftLabel :=
  dotProduct_comm _ _

/-- The pivot at the pair's FIRST member. Rank-independent. -/
theorem tripleGapForm_pivot_eq_first (D : WeightedDesign m k)
    (firstLabel secondLabel : Fin m) :
    tripleGapForm D firstLabel firstLabel secondLabel
      = 2 * pairGapExcessOf D firstLabel secondLabel + gapExcessOf D secondLabel := by
  rw [tripleGapForm, gapPairingOf_self, pairGapExcessOf]
  ring

/-- The pivot at the pair's SECOND member. Rank-independent. -/
theorem tripleGapForm_pivot_eq_second (D : WeightedDesign m k)
    (firstLabel secondLabel : Fin m) :
    tripleGapForm D secondLabel firstLabel secondLabel
      = 2 * pairGapExcessOf D firstLabel secondLabel + gapExcessOf D firstLabel := by
  rw [tripleGapForm, gapPairingOf_self, pairGapExcessOf,
    gapPairingOf_comm D secondLabel firstLabel]
  ring

/-! ## The off-pair identity, at any rank -/

/-- **THE GENERAL-RANK OFF-PAIR IDENTITY.**  Peeling the pair's own two pivots off
the averaging identity leaves an exact expression in the pair's data alone.  At
rank three the pair-excess coefficient is `-2 (w_i + w_j)`, which is what makes
the rank-three engine fire; at rank `k` it is `3 - k - 2 (w_i + w_j)`. -/
theorem sum_offPair_weight_mul_tripleGapForm (D : WeightedDesign m k)
    {firstLabel secondLabel : Fin m} (hdistinct : firstLabel ≠ secondLabel) :
    ∑ pivotLabel ∈ (Finset.univ.erase firstLabel).erase secondLabel,
        D.weight pivotLabel * tripleGapForm D pivotLabel firstLabel secondLabel
      = (3 - (k : ℝ) - 2 * D.weight firstLabel - 2 * D.weight secondLabel)
            * pairGapExcessOf D firstLabel secondLabel
          + (1 - D.weight secondLabel) * gapExcessOf D firstLabel
          + (1 - D.weight firstLabel) * gapExcessOf D secondLabel := by
  classical
  have hsecondMem : secondLabel ∈ Finset.univ.erase firstLabel :=
    Finset.mem_erase.mpr ⟨Ne.symm hdistinct, Finset.mem_univ secondLabel⟩
  have hpeelFirst := Finset.add_sum_erase (Finset.univ : Finset (Fin m))
    (fun pivotLabel => D.weight pivotLabel * tripleGapForm D pivotLabel firstLabel secondLabel)
    (Finset.mem_univ firstLabel)
  have hpeelSecond := Finset.add_sum_erase (Finset.univ.erase firstLabel)
    (fun pivotLabel => D.weight pivotLabel * tripleGapForm D pivotLabel firstLabel secondLabel)
    hsecondMem
  have htotal := sum_weight_mul_tripleGapForm D firstLabel secondLabel
  rw [tripleGapForm_pivot_eq_first] at hpeelFirst
  rw [tripleGapForm_pivot_eq_second] at hpeelSecond
  rw [← hpeelSecond] at hpeelFirst
  linear_combination hpeelFirst + htotal

/-! ## Cross-check against the landed rank-three surplus form

`Gtz.sum_offPair_weight_mul_discriminantTie` (Gtz/Quantitative/TieRowLaw.lean) is the
rank-three off-pair law in SURPLUS form.  The general-rank form proved above is the
same statement: at rank three the coefficient `3 - rank` vanishes and the two right
hand sides are equal as polynomials.  This is the agreement theorem, so the
general-rank law is a genuine lift and not a second, unrelated identity. -/

theorem tripleGapForm_offPair_agrees_with_surplusForm (D : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    -((3 - ((3 : ℕ) : ℝ) - 2 * D.weight firstLabel - 2 * D.weight secondLabel)
          * pairGapExcessOf D firstLabel secondLabel
        + (1 - D.weight secondLabel) * gapExcessOf D firstLabel
        + (1 - D.weight firstLabel) * gapExcessOf D secondLabel)
      = heavyExcess D secondLabel * shareSurplus D firstLabel
        + heavyExcess D firstLabel * shareSurplus D secondLabel
        - 2 * atomPairing D firstLabel secondLabel ^ 2
            * (D.weight firstLabel + D.weight secondLabel) := by
  simp only [pairGapExcessOf, gapExcessOf, gapPairingOf, heavyExcess, atomPairing,
    shareSurplus, atomShare]
  push_cast
  ring

/-! ## Why the rank-two machine does not lift: two independent obstructions

The rank-two closure (`Gtz.rankTwoEqualityStratum_holds`) rests on the pivot bound
`mass * (1 + heaviness) <= 1` summed over an admissible support, which forces
`rank + (rank - 1) <= support.card`, against the Caratheodory ceiling
`support.card <= dim Sym(rank) = rank * (rank + 1) / 2`.  The two coincide only at
rank one and rank two, so at rank three the circuit bound is slack by one and goes
vacuous.  Independently, the pair cap the bound consumes is FALSE at rank three. -/

/-- **THE ARITHMETIC OBSTRUCTION.**  `2 * rank - 1 = rank * (rank + 1) / 2` -- the
coincidence that makes the rank-two circuit bound exactly tight -- holds at rank one
and rank two and at no other rank.  Stated multiplied out, so no natural subtraction
or division appears. -/
theorem rankTwoCaratheodoryCoincidence_iff (rank : ℕ) :
    4 * rank = rank * rank + rank + 2 ↔ (rank = 1 ∨ rank = 2) := by
  constructor
  · intro hcoincide
    match rank with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => exact Or.inr rfl
    | (remaining + 3) => exfalso; nlinarith [hcoincide, Nat.zero_le remaining]
  · rintro (rfl | rfl) <;> norm_num

theorem tetraDesign_atomHeaviness (atomLabel : Fin 4) :
    atomHeaviness tetraDesign atomLabel = 2 / 3 := by
  have hleverage := tetraDesign_leverage atomLabel
  rw [atomHeaviness, if_neg (by rw [hleverage]; norm_num), hleverage]
  norm_num

theorem tetraDesign_unitPairGram_zeroOne :
    unitPairGram tetraDesign 0 1 = 1 / 9 := by
  rw [unitPairGram, tetraDesign_leverage, tetraDesign_leverage]
  norm_num [tetraDesign, tetraAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **THE PAIR-CAP OBSTRUCTION.**  The rank-two tie law caps the product of two
heavinesses by the unit pair Gram.  At rank three the regular tetrahedron -- which
IS a tie -- violates that cap outright, `4/9` against `1/9`.  So the rank-two cap is
not merely unavailable at rank three, it is false there, and no route through it can
be repaired. -/
theorem tetraDesign_violates_rankTwoPairCap :
    IsTie tetraDesign
      ∧ unitPairGram tetraDesign 0 1
          < atomHeaviness tetraDesign 0 * atomHeaviness tetraDesign 1 := by
  refine ⟨tetraDesign_isTie, ?_⟩
  rw [tetraDesign_unitPairGram_zeroOne, tetraDesign_atomHeaviness, tetraDesign_atomHeaviness]
  norm_num

/-! ## The surplus budget at general rank, and its collision with the wall

`Gtz.shareSurplus` and `Gtz.sum_shareSurplus` are landed at rank three only
(`Gtz.sum_shareSurplus : sum = 5 - m`).  `Gtz.atomShare` and
`Gtz.sum_atomShare_eq_rank` are already rank-generic, so the budget lifts for free
-- and what it lifts to is the SAME polynomial that governs the rank-two wall. -/

/-- The **share surplus** at ANY rank: `2 * share - weight - 1`. -/
noncomputable def shareSurplusOf (D : WeightedDesign m k) (atomLabel : Fin m) : ℝ :=
  2 * atomShare D atomLabel - D.weight atomLabel - 1

theorem shareSurplusOf_eq_shareSurplus (D : WeightedDesign m 3) (atomLabel : Fin m) :
    shareSurplusOf D atomLabel = shareSurplus D atomLabel := rfl

/-- **THE SURPLUS BUDGET AT GENERAL RANK.**  The rank-three `Gtz.sum_shareSurplus`
(`= 5 - m`) is the case `rank = 3` of `2 * rank - 1 - size`. -/
theorem sum_shareSurplusOf (D : WeightedDesign m k) :
    ∑ atomLabel, shareSurplusOf D atomLabel = 2 * (k : ℝ) - 1 - (m : ℝ) := by
  simp only [shareSurplusOf]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_atomShare_eq_rank D, D.weight_sum_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **THE BUDGET AT THE THRESHOLD CELL IS MINUS THE WALL POLYNOMIAL.**  At the
threshold cell `size = rank * (rank + 1) / 2` the whole surplus budget is
`-(rank - 1)(rank - 2) / 2`.  Stated doubled so no division appears.

This is the SAME polynomial as `rankTwoCaratheodoryCoincidence_iff`
(`4 * rank = rank * rank + rank + 2` is `(rank - 1)(rank - 2) = 0`): the arithmetic
obstruction to lifting the rank-two Caratheodory argument and the vanishing of the
surplus budget are ONE obstruction.  It vanishes exactly at rank one and rank two,
and grows quadratically negative from rank three on. -/
theorem two_mul_sum_shareSurplusOf_thresholdCell (D : WeightedDesign m k)
    (hthreshold : 2 * m = k * (k + 1)) :
    2 * ∑ atomLabel, shareSurplusOf D atomLabel
      = -(((k : ℝ) - 1) * ((k : ℝ) - 2)) := by
  have hcast : 2 * (m : ℝ) = (k : ℝ) * ((k : ℝ) + 1) := by
    have := congrArg (fun natValue : ℕ => (natValue : ℝ)) hthreshold
    push_cast at this
    linarith [this]
  rw [sum_shareSurplusOf]
  linarith [hcast, sq_nonneg ((k : ℝ))]

/-- **The budget vanishes at exactly the ranks where the rank-two machine works.**
Zero surplus budget at the threshold cell is the rank-two coincidence. -/
theorem sum_shareSurplusOf_thresholdCell_eq_zero_iff (D : WeightedDesign m k)
    (hthreshold : 2 * m = k * (k + 1)) :
    (∑ atomLabel, shareSurplusOf D atomLabel) = 0 ↔ (k = 1 ∨ k = 2) := by
  have hdoubled := two_mul_sum_shareSurplusOf_thresholdCell D hthreshold
  constructor
  · intro hzero
    rw [hzero, mul_zero] at hdoubled
    have hproduct : ((k : ℝ) - 1) * ((k : ℝ) - 2) = 0 := by linarith
    rcases mul_eq_zero.mp hproduct with hone | htwo
    · exact Or.inl (by exact_mod_cast (by linarith : (k : ℝ) = 1))
    · exact Or.inr (by exact_mod_cast (by linarith : (k : ℝ) = 2))
  · intro hrankSmall
    have hproduct : ((k : ℝ) - 1) * ((k : ℝ) - 2) = 0 := by
      rcases hrankSmall with rfl | rfl <;> norm_num
    rw [hproduct] at hdoubled
    linarith

end Gtz
