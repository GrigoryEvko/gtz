/-
# Calibrating the connectedness route: its topological input has real content

`Gtz/Reduction/ConnectednessRoute.lean` derives `Gtz.GtzWeighted 6 3` from
`Gtz.HingeHoldsAtSize 6 3` together with one named topological hypothesis,
`Gtz.ParallelFreeReachesAnchor`.  An interface is only worth what its hypotheses
are worth, so this module measures both of them against cells where the truth is
known.

## THE REACH IS NOT A TAUTOLOGY

`Gtz.not_parallelFreeReachesAnchor_rankTwo`: the hypothesis is FALSE at RANK TWO,
at every size and for every parallel-free anchor.  In the plane a vanishing pair
determinant IS a parallel pair (`Gtz.hasParallelPair_of_pairDet_eq_zero`), so
along a path that stays parallel-free the determinant of a fixed pair is
continuous and never zero, hence of constant sign; negating one atom preserves
Parseval and preserves parallel-freeness (`Gtz.not_hasParallelPair_negateAtom`)
while flipping that sign, so the negated design is unreachable.

This is the codimension count made visible.  Two vectors of `ℝ^rank` are parallel
on a set of codimension `rank − 1`: a SEPARATING hypersurface at rank two, and
not separating from rank three on.  The route is therefore not a rank-two
argument in disguise, and its topological input is a genuine rank-sensitive fact
that has to be paid for rather than assumed.

## THE HINGE IS NOT SLACK

`Gtz.not_forall_parallelFree_strictlyDominates_fiveThree`: at `(5,3)` the route's
own CONCLUSION is false, witnessed by `Gtz.diamondDesign`, which is parallel-free
and an exact tie — it dominates, but never strictly.  The hinge is false there
too (`Gtz.not_hingeHoldsAtSize_five_three`), so the route declines rather than
proving something false.

## The small-cell table

* `(2,2)`  hinge TRUE (`Gtz.hingeHoldsAtSize_twoTwo`, vacuously — there are no
  `(2,2)` ties), anchor strictly dominating (`Gtz.posDef_gap_twoTwo`), parallel
  branch vacuous (`Gtz.not_hasParallelPair_twoTwo`), REACH FALSE
  (`Gtz.not_parallelFreeReachesAnchor_twoTwo`), and the conclusion
  `Gtz.GtzWeighted 2 2` TRUE anyway.  The route declines on the reach.
* `(5,3)`  reach plausible, HINGE FALSE, conclusion FALSE.  The route declines on
  the hinge.
* `(6,3)`  both premises open.

No small cell makes the route prove anything false, and each premise fails
somewhere, so neither is redundant.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.DiamondPrimitive
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.ConnectednessRoute

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Negating one atom stays inside the design space and inside the parallel-free locus -/

theorem atomMatrix_neg (vecArg : Fin k → ℝ) : atomMatrix (-vecArg) = atomMatrix vecArg := by
  ext rowIndex colIndex
  simp [atomMatrix, Matrix.vecMulVec_apply]

/-- The design with one designated atom negated: same weights, same Parseval
identity, because `atomMatrix` is sign-blind. -/
def negateAtom (D : WeightedDesign m k) (flipLabel : Fin m) : WeightedDesign m k where
  atom := Function.update D.atom flipLabel (-(D.atom flipLabel))
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := by
    refine Eq.trans (Finset.sum_congr rfl ?_) D.isParseval
    intro atomLabel _
    by_cases hhit : atomLabel = flipLabel
    · subst hhit; simp [atomMatrix_neg]
    · simp [Function.update_of_ne hhit]

theorem negateAtom_atom_self (D : WeightedDesign m k) (flipLabel : Fin m) :
    (negateAtom D flipLabel).atom flipLabel = -(D.atom flipLabel) := by
  simp [negateAtom]

theorem negateAtom_atom_other (D : WeightedDesign m k) {flipLabel otherLabel : Fin m}
    (hdistinct : otherLabel ≠ flipLabel) :
    (negateAtom D flipLabel).atom otherLabel = D.atom otherLabel := by
  simp [negateAtom, Function.update_of_ne hdistinct]

/-- Parallelism is sign-blind, so negating an atom cannot create a parallel pair. -/
theorem not_hasParallelPair_negateAtom {D : WeightedDesign m k} (flipLabel : Fin m)
    (hfree : ¬ HasParallelPair D) : ¬ HasParallelPair (negateAtom D flipLabel) := by
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  apply hfree
  by_cases hkept : keptLabel = flipLabel
  · subst hkept
    have hdropNe : dropLabel ≠ keptLabel := fun hcontra => hdistinct hcontra.symm
    rw [negateAtom_atom_self, negateAtom_atom_other D hdropNe] at hparallel
    exact ⟨keptLabel, dropLabel, -ratio, hdistinct, by rw [hparallel]; module⟩
  · by_cases hdrop : dropLabel = flipLabel
    · subst hdrop
      rw [negateAtom_atom_self, negateAtom_atom_other D hkept] at hparallel
      refine ⟨keptLabel, dropLabel, -ratio, hdistinct, ?_⟩
      have hflipped : -(D.atom dropLabel) = ratio • D.atom keptLabel := hparallel
      have hneg : D.atom dropLabel = -(ratio • D.atom keptLabel) := by
        rw [← hflipped]; module
      rw [hneg]; module
    · rw [negateAtom_atom_other D hdrop, negateAtom_atom_other D hkept] at hparallel
      exact ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩

/-! ## Rank two: the parallel-free locus carries a locally constant sign -/

/-- The `2 × 2` determinant of two atoms of a rank-two atom family. -/
def pairDet (atoms : Fin m → Fin 2 → ℝ) (leftLabel rightLabel : Fin m) : ℝ :=
  atoms leftLabel 0 * atoms rightLabel 1 - atoms leftLabel 1 * atoms rightLabel 0

/-- **In the plane, a vanishing pair determinant IS a parallel pair.**  This is the
lemma with no analogue at rank three: three coplanar vectors of `ℝ³` need not
contain a parallel pair, which is exactly why the obstruction below does not
transfer to the cell the route is aimed at. -/
theorem hasParallelPair_of_pairDet_eq_zero (D : WeightedDesign m 2)
    {leftLabel rightLabel : Fin m} (hdistinct : leftLabel ≠ rightLabel)
    (hvanishes : pairDet D.atom leftLabel rightLabel = 0) : HasParallelPair D := by
  simp only [pairDet] at hvanishes
  by_cases hzeroCoord : D.atom leftLabel 0 = 0
  · by_cases honeCoord : D.atom leftLabel 1 = 0
    · refine ⟨rightLabel, leftLabel, 0, hdistinct.symm, ?_⟩
      have hzero : D.atom leftLabel 0 = (0 : ℝ) * D.atom rightLabel 0 := by
        rw [hzeroCoord]; ring
      have hone : D.atom leftLabel 1 = (0 : ℝ) * D.atom rightLabel 1 := by
        rw [honeCoord]; ring
      funext coord
      fin_cases coord
      · simpa using hzero
      · simpa using hone
    · refine ⟨leftLabel, rightLabel, D.atom rightLabel 1 / D.atom leftLabel 1, hdistinct, ?_⟩
      have hrightZero : D.atom rightLabel 0 = 0 := by
        have hproduct : D.atom leftLabel 1 * D.atom rightLabel 0 = 0 := by
          rw [hzeroCoord] at hvanishes; linarith
        rcases mul_eq_zero.mp hproduct with hcontra | hgood
        · exact absurd hcontra honeCoord
        · exact hgood
      have hzero : D.atom rightLabel 0
          = D.atom rightLabel 1 / D.atom leftLabel 1 * D.atom leftLabel 0 := by
        rw [hrightZero, hzeroCoord]; ring
      have hone : D.atom rightLabel 1
          = D.atom rightLabel 1 / D.atom leftLabel 1 * D.atom leftLabel 1 := by
        field_simp
      funext coord
      fin_cases coord
      · simpa using hzero
      · simpa using hone
  · refine ⟨leftLabel, rightLabel, D.atom rightLabel 0 / D.atom leftLabel 0, hdistinct, ?_⟩
    have hzero : D.atom rightLabel 0
        = D.atom rightLabel 0 / D.atom leftLabel 0 * D.atom leftLabel 0 := by
      field_simp
    have hone : D.atom rightLabel 1
        = D.atom rightLabel 0 / D.atom leftLabel 0 * D.atom leftLabel 1 := by
      field_simp
      linarith
    funext coord
    fin_cases coord
    · simpa using hzero
    · simpa using hone

theorem pairDet_ne_zero_of_parallelFree {D : WeightedDesign m 2}
    (hfree : ¬ HasParallelPair D) {leftLabel rightLabel : Fin m}
    (hdistinct : leftLabel ≠ rightLabel) : pairDet D.atom leftLabel rightLabel ≠ 0 :=
  fun hvanishes => hfree (hasParallelPair_of_pairDet_eq_zero D hdistinct hvanishes)

theorem pairDet_negateAtom (D : WeightedDesign m 2) {leftLabel rightLabel : Fin m}
    (hdistinct : leftLabel ≠ rightLabel) :
    pairDet (negateAtom D leftLabel).atom leftLabel rightLabel
      = - pairDet D.atom leftLabel rightLabel := by
  simp only [pairDet, negateAtom_atom_self, negateAtom_atom_other D hdistinct.symm,
    Pi.neg_apply]
  ring

/-! ## THE REFUTATION AT RANK TWO -/

/-- **THE ROUTE'S TOPOLOGICAL INPUT IS FALSE AT RANK TWO**, at every size with at
least two atoms and for every parallel-free anchor.

Along any path that stays parallel-free the determinant of a fixed pair of atoms
is continuous and never zero, hence of constant sign.  Negating one atom flips
that sign while preserving both the Parseval identity and parallel-freeness, so
the negated design is unreachable.  The hypothesis is therefore neither vacuous
nor a tautology. -/
theorem not_parallelFreeReachesAnchor_rankTwo {size : ℕ}
    (anchor : WeightedDesign (size + 2) 2) (hanchorFree : ¬ HasParallelPair anchor) :
    ¬ ParallelFreeReachesAnchor (size + 2) 2 anchor := by
  intro hreach
  have hdistinct : (0 : Fin (size + 2)) ≠ 1 := by
    simp
  obtain ⟨pathAtoms, hcontinuous, hstart, hend, hstays⟩ :=
    hreach (negateAtom anchor 0) (not_hasParallelPair_negateAtom 0 hanchorFree)
  have hcoord : ∀ atomLabel : Fin (size + 2), ∀ coord : Fin 2,
      Continuous fun timeArg : ℝ => pathAtoms timeArg atomLabel coord :=
    fun atomLabel coord =>
      (continuous_apply coord).comp ((continuous_apply atomLabel).comp hcontinuous)
  have hcontDet : Continuous fun timeArg : ℝ => pairDet (pathAtoms timeArg) 0 1 := by
    simp only [pairDet]
    exact ((hcoord 0 0).mul (hcoord 1 1)).sub ((hcoord 0 1).mul (hcoord 1 0))
  have hcontOn : ContinuousOn (fun timeArg : ℝ => pairDet (pathAtoms timeArg) 0 1)
      (Set.Icc (0 : ℝ) 1) := hcontDet.continuousOn
  have hstartValue : pairDet (pathAtoms 0) 0 1 = pairDet anchor.atom 0 1 := by rw [hstart]
  have hendValue : pairDet (pathAtoms 1) 0 1 = - pairDet anchor.atom 0 1 := by
    rw [hend]; exact pairDet_negateAtom anchor hdistinct
  have hnever : ∀ timeArg ∈ Set.Icc (0 : ℝ) 1, pairDet (pathAtoms timeArg) 0 1 ≠ 0 := by
    intro timeArg hmem
    obtain ⟨designHere, hatoms, hfreeHere⟩ := hstays timeArg hmem
    rw [← hatoms]
    exact pairDet_ne_zero_of_parallelFree hfreeHere hdistinct
  have hanchorNe : pairDet anchor.atom 0 1 ≠ 0 :=
    pairDet_ne_zero_of_parallelFree hanchorFree hdistinct
  rcases lt_or_gt_of_ne hanchorNe with hnegative | hpositive
  · have hmem : (0 : ℝ) ∈ Set.Icc (pairDet (pathAtoms 0) 0 1) (pairDet (pathAtoms 1) 0 1) := by
      rw [hstartValue, hendValue]; constructor <;> linarith
    obtain ⟨witnessTime, hwitnessMem, hwitnessValue⟩ :=
      intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcontOn hmem
    exact hnever witnessTime hwitnessMem hwitnessValue
  · have hmem : (0 : ℝ) ∈ Set.Icc (pairDet (pathAtoms 1) 0 1) (pairDet (pathAtoms 0) 0 1) := by
      rw [hstartValue, hendValue]; constructor <;> linarith
    obtain ⟨witnessTime, hwitnessMem, hwitnessValue⟩ :=
      intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcontOn hmem
    exact hnever witnessTime hwitnessMem hwitnessValue

/-! ## The `(2,2)` cell: every other premise of the route holds, and only the reach fails -/

theorem parsevalEntry (D : WeightedDesign 2 2) (rowIndex colIndex : Fin 2) :
    D.weight 0 * (D.atom 0 rowIndex * D.atom 0 colIndex)
      + D.weight 1 * (D.atom 1 rowIndex * D.atom 1 colIndex)
      = if rowIndex = colIndex then 1 else 0 := by
  have hpars := congrFun (congrFun D.isParseval rowIndex) colIndex
  simpa [Fin.sum_univ_two, atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply]
    using hpars

/-- **The Parseval determinant identity.**  Lagrange's identity applied to the three
entries of `Σ w_c a_c a_cᵀ = 1` pins the squared determinant to `1/(w₀ w₁)`. -/
theorem weight_mul_pairDet_sq (D : WeightedDesign 2 2) :
    D.weight 0 * D.weight 1 * pairDet D.atom 0 1 ^ 2 = 1 := by
  have hzeroZero := parsevalEntry D 0 0
  have hzeroOne := parsevalEntry D 0 1
  have honeOne := parsevalEntry D 1 1
  norm_num at hzeroZero hzeroOne honeOne
  simp only [pairDet]
  linear_combination
    (D.weight 0 * (D.atom 0 1 * D.atom 0 1) + D.weight 1 * (D.atom 1 1 * D.atom 1 1)) * hzeroZero
      + honeOne
      - (D.weight 0 * (D.atom 0 0 * D.atom 0 1) + D.weight 1 * (D.atom 1 0 * D.atom 1 1))
          * hzeroOne

theorem pairDet_ne_zero_twoTwo (D : WeightedDesign 2 2) : pairDet D.atom 0 1 ≠ 0 := by
  intro hzero
  have hidentity := weight_mul_pairDet_sq D
  rw [hzero] at hidentity
  norm_num at hidentity

/-- **No `(2,2)` design has a parallel pair.**  Its two atoms span the plane. -/
theorem not_hasParallelPair_twoTwo (D : WeightedDesign 2 2) : ¬ HasParallelPair D := by
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  apply pairDet_ne_zero_twoTwo D
  have hkd : (keptLabel = 0 ∧ dropLabel = 1) ∨ (keptLabel = 1 ∧ dropLabel = 0) := by
    revert hdistinct
    fin_cases keptLabel <;> fin_cases dropLabel <;> simp
  simp only [pairDet]
  rcases hkd with ⟨hkept, hdrop⟩ | ⟨hkept, hdrop⟩ <;> rw [hkept, hdrop] at hparallel <;>
    · have hcoordZero := congrFun hparallel 0
      have hcoordOne := congrFun hparallel 1
      simp only [Pi.smul_apply, smul_eq_mul] at hcoordZero hcoordOne
      rw [hcoordZero, hcoordOne]
      ring

/-- **THE REACH IS FALSE AT `(2,2)` FOR EVERY ANCHOR** — a corollary of the
rank-two refutation, since at this cell parallel-freeness is automatic. -/
theorem not_parallelFreeReachesAnchor_twoTwo (anchor : WeightedDesign 2 2) :
    ¬ ParallelFreeReachesAnchor 2 2 anchor :=
  not_parallelFreeReachesAnchor_rankTwo (size := 0) anchor (not_hasParallelPair_twoTwo anchor)

theorem gapForm_twoTwo (D : WeightedDesign 2 2) (vecArg : Fin 2 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ vecArg)
      = (D.atom 0 0 * vecArg 0 + D.atom 0 1 * vecArg 1) ^ 2
        + (D.atom 1 0 * vecArg 0 + D.atom 1 1 * vecArg 1) ^ 2
        - (vecArg 0 ^ 2 + vecArg 1 ^ 2) := by
  simp [subsetSum, atomMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.sub_apply]
  ring

theorem parsevalForm_twoTwo (D : WeightedDesign 2 2) (vecArg : Fin 2 → ℝ) :
    D.weight 0 * (D.atom 0 0 * vecArg 0 + D.atom 0 1 * vecArg 1) ^ 2
      + D.weight 1 * (D.atom 1 0 * vecArg 0 + D.atom 1 1 * vecArg 1) ^ 2
      = vecArg 0 ^ 2 + vecArg 1 ^ 2 := by
  have hzeroZero := parsevalEntry D 0 0
  have hzeroOne := parsevalEntry D 0 1
  have honeOne := parsevalEntry D 1 1
  norm_num at hzeroZero hzeroOne honeOne
  linear_combination (vecArg 0 ^ 2) * hzeroZero + (2 * vecArg 0 * vecArg 1) * hzeroOne
    + (vecArg 1 ^ 2) * honeOne

/-- **Every `(2,2)` design dominates STRICTLY**, so no `(2,2)` design is a tie. -/
theorem posDef_gap_twoTwo (D : WeightedDesign 2 2) :
    (subsetSum D Finset.univ - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact ((Matrix.posSemidef_sum _ fun c _ => posSemidef_atomMatrix (D.atom c)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, gapForm_twoTwo D vecArg]
    have hparseval := parsevalForm_twoTwo D vecArg
    have hweightSum := D.weight_sum_one
    rw [Fin.sum_univ_two] at hweightSum
    have hweightZero := D.weight_pos 0
    have hweightOne := D.weight_pos 1
    have hnotBoth : ¬ ((D.atom 0 0 * vecArg 0 + D.atom 0 1 * vecArg 1) = 0
        ∧ (D.atom 1 0 * vecArg 0 + D.atom 1 1 * vecArg 1) = 0) := by
      rintro ⟨halpha, hbeta⟩
      apply pairDet_ne_zero_twoTwo D
      obtain ⟨badIndex, hbad⟩ := Function.ne_iff.mp hne
      fin_cases badIndex
      · have hproduct : vecArg 0 * pairDet D.atom 0 1 = 0 := by
          simp only [pairDet]
          linear_combination (D.atom 1 1) * halpha - (D.atom 0 1) * hbeta
        rcases mul_eq_zero.mp hproduct with hcontra | hgood
        · exact absurd hcontra (by simpa using hbad)
        · exact hgood
      · have hproduct : vecArg 1 * pairDet D.atom 0 1 = 0 := by
          simp only [pairDet]
          linear_combination (D.atom 0 0) * hbeta - (D.atom 1 0) * halpha
        rcases mul_eq_zero.mp hproduct with hcontra | hgood
        · exact absurd hcontra (by simpa using hbad)
        · exact hgood
    rcases not_and_or.mp hnotBoth with halphaNe | hbetaNe
    · have hsquarePos : 0 < (D.atom 0 0 * vecArg 0 + D.atom 0 1 * vecArg 1) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 halphaNe))
      nlinarith [hparseval, hweightSum, mul_pos hweightOne hsquarePos,
        mul_nonneg (le_of_lt hweightZero)
          (sq_nonneg (D.atom 1 0 * vecArg 0 + D.atom 1 1 * vecArg 1))]
    · have hsquarePos : 0 < (D.atom 1 0 * vecArg 0 + D.atom 1 1 * vecArg 1) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hbetaNe))
      nlinarith [hparseval, hweightSum, mul_pos hweightZero hsquarePos,
        mul_nonneg (le_of_lt hweightOne)
          (sq_nonneg (D.atom 0 0 * vecArg 0 + D.atom 0 1 * vecArg 1))]

/-- **The hinge HOLDS at `(2,2)`** — vacuously, because there are no ties. -/
theorem hingeHoldsAtSize_twoTwo : HingeHoldsAtSize 2 2 := by
  intro D htie
  exact absurd (posDef_gap_twoTwo D) (htie.2 Finset.univ (by simp))

/-- The conclusion the route would deliver at `(2,2)` is TRUE anyway, so the route
declining there costs nothing. -/
theorem gtzWeighted_twoTwo : GtzWeighted 2 2 :=
  gtzWeighted_of_le_five 2 2 (by norm_num) (by norm_num)

/-! ## The `(5,3)` calibration: the hinge hypothesis is NOT slack -/

/-- **AT `(5,3)` THE ROUTE'S CONCLUSION IS FALSE.**  `Gtz.diamondDesign` is
parallel-free and an exact tie, so it dominates but never strictly.  The hinge is
false there as well (`Gtz.not_hingeHoldsAtSize_five_three`), so the route declines
rather than proving something false — and the hinge is therefore carrying real
weight rather than being a slack hypothesis. -/
theorem not_forall_parallelFree_strictlyDominates_fiveThree :
    ¬ ∀ D : WeightedDesign 5 3, ¬ HasParallelPair D →
        ∃ C : Finset (Fin 5), C.card = 3 ∧ (subsetSum D C - 1).PosDef := by
  intro hall
  obtain ⟨chosen, hcard, hposDef⟩ := hall diamondDesign not_hasParallelPair_diamondDesign
  exact diamondDesign_isTie.2 chosen hcard hposDef

end Gtz
