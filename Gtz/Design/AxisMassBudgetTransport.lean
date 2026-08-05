/-
# Branch (i), phase 0 and phase 3b: the exchange gate tolerates axis mass

Phase-0 finding, mechanized.  The landed transport
`Gtz.posDef_exchangeTriple_of_tightAxisGate` is an INEQUALITY gate, so the exact
on-plane drop demanded by `TightDropOnPlaneSixThree` is strictly stronger than
what the exchange needs: a drop atom with SMALL axis mass fires the same gate,
"small" being measured against the remaining pair's plane margin.  Everything
here is unconditional.

* `posDef_exchangeTriple_of_axisMassBudget` — the quantitative gate.  If the
  remaining subset dominates the tight plane with ratio margin `marginRatio`
  and the exchange satisfies the scalar budget

      |g_drop . axis| * (leverage drop + leverage insert)
        < (|g_insert . axis| - |g_drop . axis|) * marginRatio,

  then the exchanged subset dominates STRICTLY.  At `g_drop . axis = 0` the
  budget reads `0 < |g_insert . axis| * marginRatio` and the on-plane transport
  is recovered; Cauchy-Schwarz and the two-squares bound price the tilt.

* `exists_ratioMargin_of_planeStrict_subset` — pointwise plane-strictness
  already carries a RATIO margin.  The two-squares identity

      (k11 + k22) * (k11 x^2 + 2 k12 x y + k22 y^2)
        - (k11 k22 - k12^2) * (x^2 + y^2)
        = (k11 x + k12 y)^2 + (k12 x + k22 y)^2

  converts positive definiteness of the plane restriction into the explicit
  margin `det / trace`: no compactness, no eigenvalues, no square roots.

* `TightDropWithinBudgetSixThree` — the WEAKENED branch-(i) residual: some
  tight triple of every stress-free `(6,3)` tie admits an exchange within the
  budget.  `tightDropWithinBudget_of_tightDropOnPlane` shows the tight-axis
  lane's on-plane residual implies it, and
  `stressFreeHingeHoldsSixThree_of_tightDropWithinBudget` closes branch (i)
  from it.  The residual is thereby an OPEN condition — an equality target
  replaced by a neighbourhood, which is the shape the branch-(iii) lesson
  demands.

Calibration (exact rationals, lane report under `/tmp/gtz-p17/tightdrop/`): on
the symmetric budget-equality family at `(6,3)` the exchange that kills the
configuration fires at drop axis mass about `0.62` against a plane margin about
`0.30` — far outside this budget.  So the budget names the on-plane
NEIGHBOURHOOD honestly and is not claimed to capture every firing exchange.

Self-containment note: Part 3 restates the orthonormal-frame kit textually
(base: the tight-axis pair lane); if this file is landed next to
`FourOnPlaneStress.lean` the shared kit belongs in one module.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Design.TwoPoleStratum
import Gtz.Design.StressFreeNormalizer
import Gtz.Reduction.TrichotomyLedger
import Gtz.Design.TightAxisPairBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: scalar kit -/

/-- Cauchy-Schwarz for the real dot product, in the campaign's vocabulary. -/
theorem dotProduct_sq_le_dotProduct_self_mul {dim : ℕ} (leftVec rightVec : Fin dim → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2 ≤ (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ leftVec rightVec
  have hleft : ∑ coord, leftVec coord ^ 2 = leftVec ⬝ᵥ leftVec := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun coord _ => pow_two (leftVec coord)
  have hright : ∑ coord, rightVec coord ^ 2 = rightVec ⬝ᵥ rightVec := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun coord _ => pow_two (rightVec coord)
  rw [hleft, hright] at hcs
  exact hcs

/-- **THE TWO-SQUARES MARGIN.**  A positive definite binary form dominates the
squared norm with ratio `det / trace`, certified by an exact sum of two
squares — the scalar core of the margin extraction. -/
theorem margin_le_quadForm_of_posDef_binary
    {kOneOne kOneTwo kTwoTwo seedCoord probeCoord : ℝ} (hOnePos : 0 < kOneOne)
    (hDetPos : 0 < kOneOne * kTwoTwo - kOneTwo ^ 2) :
    ((kOneOne * kTwoTwo - kOneTwo ^ 2) / (kOneOne + kTwoTwo))
        * (seedCoord ^ 2 + probeCoord ^ 2)
      ≤ kOneOne * seedCoord ^ 2 + 2 * kOneTwo * (seedCoord * probeCoord)
        + kTwoTwo * probeCoord ^ 2 := by
  have hTwoPos : 0 < kTwoTwo := by nlinarith [hDetPos, hOnePos, sq_nonneg kOneTwo]
  have htracePos : 0 < kOneOne + kTwoTwo := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ htracePos]
  nlinarith [sq_nonneg (kOneOne * seedCoord + kOneTwo * probeCoord),
    sq_nonneg (kOneTwo * seedCoord + kTwoTwo * probeCoord)]

/-- The squared pairings of a planar combination expand into the three plane
moments of the subset. -/
theorem sum_sq_pairing_of_planarCombination (design : WeightedDesign size rank)
    (support : Finset (Fin size)) (frameOne frameTwo : Fin rank → ℝ)
    (coeffOne coeffTwo : ℝ) :
    ∑ atomIndex ∈ support,
        (design.atom atomIndex ⬝ᵥ (coeffOne • frameOne + coeffTwo • frameTwo)) ^ 2
      = coeffOne ^ 2 * ∑ atomIndex ∈ support, (design.atom atomIndex ⬝ᵥ frameOne) ^ 2
        + 2 * coeffOne * coeffTwo
            * ∑ atomIndex ∈ support,
                (design.atom atomIndex ⬝ᵥ frameOne) * (design.atom atomIndex ⬝ᵥ frameTwo)
        + coeffTwo ^ 2
            * ∑ atomIndex ∈ support, (design.atom atomIndex ⬝ᵥ frameTwo) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-! ## Part 2: the quantitative exchange gate -/

/-- **THE GATE TOLERATES AXIS MASS.**  Exchange a drop atom of a tight subset
for an outside insert.  If the REMAINING subset dominates the tight plane with
ratio margin `marginRatio` and the scalar budget

    `|a_drop| * (leverage drop + leverage insert) < (|a_insert| - |a_drop|) * marginRatio`

holds for the axis components `a`, then the exchanged subset dominates
strictly.  The on-plane transport is the boundary case `a_drop = 0`. -/
theorem posDef_exchangeTriple_of_axisMassBudget (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel addLabel : Fin size} (hdrop : dropLabel ∈ selected)
    (haddNot : addLabel ∉ selected)
    {marginRatio : ℝ} (hmarginPos : 0 < marginRatio)
    (hpairMargin : ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 →
      (1 + marginRatio) * (planar ⬝ᵥ planar)
        ≤ ∑ atomIndex ∈ selected.erase dropLabel, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
    (hbudget : |design.atom dropLabel ⬝ᵥ axis|
          * (leverageOf (design.atom dropLabel) + leverageOf (design.atom addLabel))
        < (|design.atom addLabel ⬝ᵥ axis| - |design.atom dropLabel ⬝ᵥ axis|)
            * marginRatio) :
    (subsetSum design (insert addLabel (selected.erase dropLabel)) - 1).PosDef := by
  classical
  set dropAxis := design.atom dropLabel ⬝ᵥ axis with hdropAxisDef
  set addAxis := design.atom addLabel ⬝ᵥ axis with haddAxisDef
  set dropLev := leverageOf (design.atom dropLabel) with hdropLevDef
  set addLev := leverageOf (design.atom addLabel) with haddLevDef
  have hdropLevNonneg : 0 ≤ dropLev := leverageOf_nonneg _
  have haddLevNonneg : 0 ≤ addLev := leverageOf_nonneg _
  have hlhsNonneg : 0 ≤ |dropAxis| * (dropLev + addLev) :=
    mul_nonneg (abs_nonneg dropAxis) (by linarith)
  have hdiffPos : 0 < |addAxis| - |dropAxis| := by
    by_contra hnot
    push Not at hnot
    have hrhsNonpos := mul_nonpos_of_nonpos_of_nonneg hnot hmarginPos.le
    linarith [hbudget, hlhsNonneg]
  have hsumAbsPos : 0 < |dropAxis| + |addAxis| := by
    have habsNonneg := abs_nonneg dropAxis
    linarith
  have hdiffProduct : (|addAxis| - |dropAxis|) * (|dropAxis| + |addAxis|)
      = addAxis ^ 2 - dropAxis ^ 2 := by
    rw [← sq_abs addAxis, ← sq_abs dropAxis]
    ring
  have hexcess : dropAxis ^ 2 < addAxis ^ 2 := by
    have hprod := mul_pos hdiffPos hsumAbsPos
    linarith [hdiffProduct, hprod]
  refine posDef_exchangeTriple_of_tightAxisGate design hdominates hunit htight hdrop
    haddNot hexcess ?_
  intro planar hplanarOrth hplanarNe
  set dropPairing := design.atom dropLabel ⬝ᵥ planar with hdropPairingDef
  set addPairing := design.atom addLabel ⬝ᵥ planar with haddPairingDef
  set planarNorm := planar ⬝ᵥ planar with hplanarNormDef
  have hplanarNormPos : 0 < planarNorm := dotProduct_self_pos hplanarNe
  have hdropSq : dropPairing ^ 2 ≤ dropLev * planarNorm := by
    have hcs := dotProduct_sq_le_dotProduct_self_mul (design.atom dropLabel) planar
    rw [hdropLevDef, leverageOf_eq_dotProduct_self]
    exact hcs
  have haddSq : addPairing ^ 2 ≤ addLev * planarNorm := by
    have hcs := dotProduct_sq_le_dotProduct_self_mul (design.atom addLabel) planar
    rw [haddLevDef, leverageOf_eq_dotProduct_self]
    exact hcs
  have hmarginAt := hpairMargin planar hplanarOrth
  have hmarginGap : marginRatio * planarNorm
      ≤ (∑ atomIndex ∈ selected.erase dropLabel,
          (design.atom atomIndex ⬝ᵥ planar) ^ 2) - planarNorm := by
    linarith [hmarginAt]
  have hsumSplit : ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2
      = (∑ atomIndex ∈ selected.erase dropLabel,
          (design.atom atomIndex ⬝ᵥ planar) ^ 2) + dropPairing ^ 2 := by
    rw [Finset.sum_erase_eq_sub hdrop]
    ring
  -- the cross term, at absolute-value rates
  have hdropPairingAbsSq : |dropPairing| ^ 2 = dropPairing ^ 2 := sq_abs _
  have haddPairingAbsSq : |addPairing| ^ 2 = addPairing ^ 2 := sq_abs _
  have hamgm : 2 * (|dropPairing| * |addPairing|) ≤ dropPairing ^ 2 + addPairing ^ 2 := by
    nlinarith [sq_nonneg (|dropPairing| - |addPairing|), hdropPairingAbsSq,
      haddPairingAbsSq]
  have habsProdNonneg : 0 ≤ |addAxis| * |dropAxis| :=
    mul_nonneg (abs_nonneg addAxis) (abs_nonneg dropAxis)
  have hcrossAbs : -(2 * (addAxis * dropAxis * (dropPairing * addPairing)))
      ≤ 2 * (|addAxis| * |dropAxis| * (|dropPairing| * |addPairing|)) := by
    have hneg := neg_le_abs (addAxis * dropAxis * (dropPairing * addPairing))
    have habsEq : |addAxis * dropAxis * (dropPairing * addPairing)|
        = |addAxis| * |dropAxis| * (|dropPairing| * |addPairing|) := by
      rw [abs_mul, abs_mul, abs_mul]
    linarith [hneg, habsEq.le, habsEq.ge]
  have hcross : -(2 * (addAxis * dropAxis * (dropPairing * addPairing)))
      ≤ (|addAxis| * |dropAxis|) * (dropPairing ^ 2 + addPairing ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hamgm habsProdNonneg
    linarith [hcrossAbs, hscaled]
  have hdropAxisAbsSqScaled : |dropAxis| ^ 2 * (dropPairing ^ 2 + addPairing ^ 2)
      = dropAxis ^ 2 * (dropPairing ^ 2 + addPairing ^ 2) := by
    rw [sq_abs]
  have hstepOne : dropAxis ^ 2 * (dropPairing ^ 2 + addPairing ^ 2)
        - 2 * (addAxis * dropAxis * (dropPairing * addPairing))
      ≤ |dropAxis| * (|dropAxis| + |addAxis|) * (dropPairing ^ 2 + addPairing ^ 2) := by
    linarith [hcross, hdropAxisAbsSqScaled]
  have hpairingSum : dropPairing ^ 2 + addPairing ^ 2
      ≤ (dropLev + addLev) * planarNorm := by
    linarith [hdropSq, haddSq]
  have hcoeffNonneg : 0 ≤ |dropAxis| * (|dropAxis| + |addAxis|) :=
    mul_nonneg (abs_nonneg dropAxis) hsumAbsPos.le
  have hstepTwo := mul_le_mul_of_nonneg_left hpairingSum hcoeffNonneg
  have hstepThree := mul_lt_mul_of_pos_right hbudget (mul_pos hsumAbsPos hplanarNormPos)
  have hdiffScaled : (|addAxis| - |dropAxis|) * marginRatio
        * ((|dropAxis| + |addAxis|) * planarNorm)
      = (addAxis ^ 2 - dropAxis ^ 2) * (marginRatio * planarNorm) := by
    linear_combination marginRatio * planarNorm * hdiffProduct
  have hstepFive := mul_le_mul_of_nonneg_left hmarginGap (by linarith [hexcess] :
    (0 : ℝ) ≤ addAxis ^ 2 - dropAxis ^ 2)
  have hkeyIdentity : (addAxis * dropPairing - dropAxis * addPairing) ^ 2
      = (addAxis ^ 2 - dropAxis ^ 2) * dropPairing ^ 2
        + (dropAxis ^ 2 * (dropPairing ^ 2 + addPairing ^ 2)
          - 2 * (addAxis * dropAxis * (dropPairing * addPairing))) := by
    ring
  rw [hsumSplit]
  linarith [hkeyIdentity, hstepOne, hstepTwo, hstepThree, hdiffScaled, hstepFive]

/-- **A design with an in-budget exchange is not a tie.** -/
theorem not_isTie_of_axisMassBudget (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0)
    {dropLabel addLabel : Fin size} (hdrop : dropLabel ∈ selected)
    (haddNot : addLabel ∉ selected)
    {marginRatio : ℝ} (hmarginPos : 0 < marginRatio)
    (hpairMargin : ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 →
      (1 + marginRatio) * (planar ⬝ᵥ planar)
        ≤ ∑ atomIndex ∈ selected.erase dropLabel, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
    (hbudget : |design.atom dropLabel ⬝ᵥ axis|
          * (leverageOf (design.atom dropLabel) + leverageOf (design.atom addLabel))
        < (|design.atom addLabel ⬝ᵥ axis| - |design.atom dropLabel ⬝ᵥ axis|)
            * marginRatio) :
    ¬ IsTie design := by
  classical
  intro htie
  refine htie.2 (insert addLabel (selected.erase dropLabel)) ?_
    (posDef_exchangeTriple_of_axisMassBudget design hdominates hunit htight hdrop haddNot
      hmarginPos hpairMargin hbudget)
  rw [card_exchangeSubset selected hdrop haddNot, hcard]

/-! ## Part 3: frame kit (textual base: the tight-axis pair lane) -/

/-! ## Part 4: pointwise plane-strictness carries a ratio margin -/

/-- **THE MARGIN IS FREE.**  A subset whose atoms dominate the plane of a unit
axis pointwise-strictly dominates it with an explicit RATIO margin `det/trace`
of the plane restriction — extracted by the two-squares identity, with no
compactness and no spectral theorem. -/
theorem exists_ratioMargin_of_planeStrict_subset
    (design : WeightedDesign size 3) {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (support : Finset (Fin size))
    (hplaneStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar < ∑ atomIndex ∈ support, (design.atom atomIndex ⬝ᵥ planar) ^ 2) :
    ∃ marginRatio : ℝ, 0 < marginRatio
      ∧ ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 →
          (1 + marginRatio) * (planar ⬝ᵥ planar)
            ≤ ∑ atomIndex ∈ support, (design.atom atomIndex ⬝ᵥ planar) ^ 2 := by
  classical
  obtain ⟨pOne, pTwo, hOneOne, hTwoTwo, hOneTwo, hOneAxis, hTwoAxis⟩ :=
    exists_orthonormal_planarFrame hunit
  have hTwoOne : pTwo ⬝ᵥ pOne = 0 := by rw [dotProduct_comm]; exact hOneTwo
  have hOneNe : pOne ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hOneOne
    exact zero_ne_one hOneOne
  have hTwoNe : pTwo ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hTwoTwo
    exact zero_ne_one hTwoTwo
  obtain ⟨seedSq, hseedSqDef⟩ :
      ∃ value : ℝ, value = ∑ atomIndex ∈ support, (design.atom atomIndex ⬝ᵥ pOne) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨probeSq, hprobeSqDef⟩ :
      ∃ value : ℝ, value = ∑ atomIndex ∈ support, (design.atom atomIndex ⬝ᵥ pTwo) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨crossSum, hcrossSumDef⟩ :
      ∃ value : ℝ, value = ∑ atomIndex ∈ support,
        (design.atom atomIndex ⬝ᵥ pOne) * (design.atom atomIndex ⬝ᵥ pTwo) := ⟨_, rfl⟩
  have hseedPos : 0 < seedSq - 1 := by
    have hvalue := hplaneStrict pOne hOneAxis hOneNe
    rw [hOneOne, ← hseedSqDef] at hvalue
    linarith
  have hprobePos : 0 < probeSq - 1 := by
    have hvalue := hplaneStrict pTwo hTwoAxis hTwoNe
    rw [hTwoTwo, ← hprobeSqDef] at hvalue
    linarith
  -- the Schur direction certifies the determinant
  have hdetPos : 0 < (seedSq - 1) * (probeSq - 1) - crossSum ^ 2 := by
    have hschurPerp : ((-crossSum) • pOne + (seedSq - 1) • pTwo) ⬝ᵥ axis = 0 := by
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hOneAxis, hTwoAxis,
        smul_eq_mul, smul_eq_mul]
      ring
    have hschurPairing : ((-crossSum) • pOne + (seedSq - 1) • pTwo) ⬝ᵥ pTwo
        = seedSq - 1 := by
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hOneTwo, hTwoTwo,
        smul_eq_mul, smul_eq_mul]
      ring
    have hschurNe : (-crossSum) • pOne + (seedSq - 1) • pTwo ≠ 0 := by
      intro hzero
      rw [hzero, zero_dotProduct] at hschurPairing
      exact hseedPos.ne (by rw [hschurPairing])
    have hschurValue := hplaneStrict _ hschurPerp hschurNe
    have hschurNorm : ((-crossSum) • pOne + (seedSq - 1) • pTwo)
          ⬝ᵥ ((-crossSum) • pOne + (seedSq - 1) • pTwo)
        = crossSum ^ 2 + (seedSq - 1) ^ 2 := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, hOneOne, hTwoTwo, hOneTwo, hTwoOne]
      ring
    have hschurSum := sum_sq_pairing_of_planarCombination design support pOne pTwo
      (-crossSum) (seedSq - 1)
    rw [← hseedSqDef, ← hprobeSqDef, ← hcrossSumDef] at hschurSum
    rw [hschurNorm, hschurSum] at hschurValue
    nlinarith [hschurValue, hseedPos]
  refine ⟨((seedSq - 1) * (probeSq - 1) - crossSum ^ 2) / ((seedSq - 1) + (probeSq - 1)),
    div_pos hdetPos (by linarith), ?_⟩
  intro planar hplanarPerp
  obtain ⟨seedCoord, hseedCoordDef⟩ : ∃ value : ℝ, value = planar ⬝ᵥ pOne := ⟨_, rfl⟩
  obtain ⟨probeCoord, hprobeCoordDef⟩ : ∃ value : ℝ, value = planar ⬝ᵥ pTwo := ⟨_, rfl⟩
  have hexpand := orthonormalFrame_expansion hOneOne hTwoTwo hunit hOneTwo
    hOneAxis hTwoAxis planar
  rw [hplanarPerp, zero_smul, add_zero, ← hseedCoordDef, ← hprobeCoordDef] at hexpand
  have hplanarNorm : planar ⬝ᵥ planar = seedCoord ^ 2 + probeCoord ^ 2 := by
    conv_lhs => rw [hexpand]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hOneOne, hTwoTwo, hOneTwo, hTwoOne]
    ring
  have hplanarSum := sum_sq_pairing_of_planarCombination design support pOne pTwo
    seedCoord probeCoord
  rw [← hexpand, ← hseedSqDef, ← hprobeSqDef, ← hcrossSumDef] at hplanarSum
  have hscalar := margin_le_quadForm_of_posDef_binary (kOneOne := seedSq - 1)
    (kOneTwo := crossSum) (kTwoTwo := probeSq - 1) (seedCoord := seedCoord)
    (probeCoord := probeCoord) hseedPos hdetPos
  rw [hplanarNorm, hplanarSum]
  nlinarith [hscalar]

/-! ## Part 5: the weakened branch-(i) residual and its wirings -/

/-- **THE WEAKENED RESIDUAL: a drop within the axis-mass budget.**  Identical to
`TightDropOnPlaneSixThree` except that the drop atom need not sit on the tight
plane: it must merely fit the exchange budget against some outside insert, with
the plane margin quantified.  The on-plane residual is the boundary case
`drop axis mass = 0`, so this `Prop` asks for strictly less. -/
def TightDropWithinBudgetSixThree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∀ stress : Fin 6 → ℝ,
      (∑ atomIndex, stress atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stress = 0) →
    IsTie design →
    ∃ (selected : Finset (Fin 6)) (axis : Fin 3 → ℝ) (dropLabel addLabel : Fin 6)
      (marginRatio : ℝ),
      selected.card = 3 ∧ Dominates design selected ∧ axis ⬝ᵥ axis = 1
        ∧ axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0
        ∧ dropLabel ∈ selected ∧ addLabel ∉ selected ∧ 0 < marginRatio
        ∧ (∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 →
            (1 + marginRatio) * (planar ⬝ᵥ planar)
              ≤ ∑ atomIndex ∈ selected.erase dropLabel,
                  (design.atom atomIndex ⬝ᵥ planar) ^ 2)
        ∧ |design.atom dropLabel ⬝ᵥ axis|
              * (leverageOf (design.atom dropLabel)
                + leverageOf (design.atom addLabel))
            < (|design.atom addLabel ⬝ᵥ axis| - |design.atom dropLabel ⬝ᵥ axis|)
                * marginRatio

/-- **The on-plane residual implies the budget residual.**  The margin is paid
by `exists_ratioMargin_of_planeStrict_subset`, the insert by the axis Parseval
identity, and the budget by `drop axis mass = 0`. -/
theorem tightDropWithinBudget_of_tightDropOnPlane
    (hresidual : TightDropOnPlaneSixThree) : TightDropWithinBudgetSixThree := by
  intro design hstressFree htie
  obtain ⟨selected, axis, dropLabel, hcard, hdominates, hunit, htight, hdropMem,
    hdropOnPlane, hpairStrict⟩ := hresidual design hstressFree htie
  obtain ⟨marginRatio, hmarginPos, hpairMargin⟩ :=
    exists_ratioMargin_of_planeStrict_subset design hunit (selected.erase dropLabel)
      hpairStrict
  have hproper : selectedᶜ.Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  obtain ⟨addLabel, haddMem, haddBig⟩ := exists_outside_axisMass_ge design hproper htight
  have haddNot : addLabel ∉ selected := Finset.mem_compl.mp haddMem
  have haddAbsGe : 1 ≤ |design.atom addLabel ⬝ᵥ axis| := by
    rw [hunit] at haddBig
    nlinarith [sq_abs (design.atom addLabel ⬝ᵥ axis),
      abs_nonneg (design.atom addLabel ⬝ᵥ axis)]
  refine ⟨selected, axis, dropLabel, addLabel, marginRatio, hcard, hdominates, hunit,
    htight, hdropMem, haddNot, hmarginPos, hpairMargin, ?_⟩
  rw [hdropOnPlane, abs_zero, zero_mul, sub_zero]
  exact mul_pos (by linarith) hmarginPos

/-- **The budget residual closes branch (i).** -/
theorem stressFreeHingeHoldsSixThree_of_tightDropWithinBudget
    (hresidual : TightDropWithinBudgetSixThree) : StressFreeHingeHoldsSixThree := by
  intro design hstressFree htie
  exfalso
  obtain ⟨selected, axis, dropLabel, addLabel, marginRatio, hcard, hdominates, hunit,
    htight, hdropMem, haddNot, hmarginPos, hpairMargin, hbudget⟩ :=
    hresidual design hstressFree htie
  exact not_isTie_of_axisMassBudget design hcard hdominates hunit htight hdropMem
    haddNot hmarginPos hpairMargin hbudget htie

/-- The tight-axis lane's conditional, recovered THROUGH the weaker residual. -/
theorem stressFreeHingeHoldsSixThree_of_tightDropOnPlane_viaBudget
    (hresidual : TightDropOnPlaneSixThree) : StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_tightDropWithinBudget
    (tightDropWithinBudget_of_tightDropOnPlane hresidual)

end Gtz
