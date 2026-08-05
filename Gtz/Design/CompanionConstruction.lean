/-
# The companion construction: branch (iii) closed

The scale-one companion turns the rank-two hinge's strict pair into a strictly
dominating triple of the original `(6,3)` design.  The crossing-locus wall is
dissolved, not narrowed: the budget is needed only NON-STRICTLY (strictness is
paid by the pair being PosDef), both pole defects factor exactly through one
signed quantity, and `le_total` on it always supplies a payable steep carrier.
Concludes `twoPoleStratumSelection_six_unconditional : TwoPoleStratumSelection 6`.
-/
import Mathlib
import Gtz.Design.RankTwoTieCriterion
import Gtz.Ties.RankTwoHingeBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Companion Part A: the two obstructions the strict pair still has to clear

Two things stand between a strictly dominating companion pair and a strictly
dominating triple of the original `(6,3)` design, and neither is an inequality
about the planar family.

* NON-PARALLELISM.  The hinge fires only on four pairwise non-parallel labels,
  so the companion's four planar shadows must be pairwise non-parallel.  In the
  `(seed, cross)` frame their bracket is the probe's triple product with the two
  original atoms, and that vanishes exactly when those atoms are parallel —
  which primitivity forbids.  `probeTriple_ne_zero_of_planarNonParallel` is the
  whole of it, and it is pure `ℝ^3` geometry: the Gram determinant of
  `(probe, left, right)` collapses to `(probe . probe) |left x right|^2` on the
  probe's plane, and a vanishing Lagrange gap exhibits the ratio outright.

* THE CARRIER BUDGET.  A pole shadow paired with a planar atom hands back
  `alongCoord^2 < (poleShadow - 1 - kappa) (acrossCoord^2 - seedNormSq)`, and
  the landed scalar gate wants `axisBlock alongCoord^2 < pairGap (acrossCoord^2
  - seedNormSq)`.  Bridging them needs `axisBlock (poleShadow - 1 - kappa) <=
  pairGap`, NON-STRICTLY — the strictness is already paid for by the pair being
  positive definite rather than merely dominating.  That non-strict form is a
  THEOREM, at one of the two poles, for every configuration: after the tilt is
  cleared by `q^2 v^2` and the carrier's `kappa` by its steepness, the defect is
  the exact product

      seedNormSq * weight * (1 - weight) * crossingDefect

  with `crossingDefect = (1 - t_Q) massP - (1 - t_P) massQ` the crossing locus of
  the two steepness masses, and the two poles read that defect with OPPOSITE
  signs.  `le_total` therefore always supplies a payable carrier, and the pole it
  supplies is automatically the steep one. -/

/-- **The Gram determinant of a triple is its squared triple product.**  Pure
polynomial identity in the nine coordinates; no hypothesis on any of the three
vectors. -/
theorem probeTriple_sq_eq_gramDeterminant (probe leftAtom rightAtom : Fin 3 → ℝ) :
    (probe ⬝ᵥ crossProduct leftAtom rightAtom) ^ 2
      = (probe ⬝ᵥ probe)
          * ((leftAtom ⬝ᵥ leftAtom) * (rightAtom ⬝ᵥ rightAtom)
            - (leftAtom ⬝ᵥ rightAtom) ^ 2)
        - (probe ⬝ᵥ leftAtom) ^ 2 * (rightAtom ⬝ᵥ rightAtom)
        + 2 * (probe ⬝ᵥ leftAtom) * (probe ⬝ᵥ rightAtom) * (leftAtom ⬝ᵥ rightAtom)
        - (probe ⬝ᵥ rightAtom) ^ 2 * (leftAtom ⬝ᵥ leftAtom) := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **Two non-parallel atoms of the probe's plane have a nonzero triple product
with the probe.**  On the plane the Gram determinant reduces to the Lagrange gap
`|left|^2 |right|^2 - <left, right>^2`; a vanishing triple product kills that
gap, and then the orthogonal residual of `right` against `left` has zero norm,
exhibiting the parallel ratio explicitly. -/
theorem probeTriple_ne_zero_of_planarNonParallel
    (probe leftAtom rightAtom : Fin 3 → ℝ)
    (hunit : probe ⬝ᵥ probe = 1)
    (hleftPlanar : leftAtom ⬝ᵥ probe = 0)
    (hrightPlanar : rightAtom ⬝ᵥ probe = 0)
    (hleftNonzero : leftAtom ≠ 0)
    (hnotParallel : ∀ ratio : ℝ, rightAtom ≠ ratio • leftAtom) :
    probe ⬝ᵥ crossProduct leftAtom rightAtom ≠ 0 := by
  intro htripleZero
  have hleftDot : probe ⬝ᵥ leftAtom = 0 := by
    rw [dotProduct_comm]; exact hleftPlanar
  have hrightDot : probe ⬝ᵥ rightAtom = 0 := by
    rw [dotProduct_comm]; exact hrightPlanar
  have hgram := probeTriple_sq_eq_gramDeterminant probe leftAtom rightAtom
  rw [htripleZero, hunit, hleftDot, hrightDot] at hgram
  have hlagrange : (leftAtom ⬝ᵥ leftAtom) * (rightAtom ⬝ᵥ rightAtom)
      = (leftAtom ⬝ᵥ rightAtom) ^ 2 := by nlinarith [hgram]
  have hleftNormPos : 0 < leftAtom ⬝ᵥ leftAtom := dotProduct_self_pos hleftNonzero
  set ratio := (leftAtom ⬝ᵥ rightAtom) / (leftAtom ⬝ᵥ leftAtom) with hratioDef
  have hresidualNorm : (rightAtom - ratio • leftAtom)
      ⬝ᵥ (rightAtom - ratio • leftAtom)
      = (rightAtom ⬝ᵥ rightAtom) - 2 * ratio * (leftAtom ⬝ᵥ rightAtom)
        + ratio ^ 2 * (leftAtom ⬝ᵥ leftAtom) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    rw [dotProduct_comm rightAtom leftAtom]
    ring
  have hresidualZero : (rightAtom - ratio • leftAtom)
      ⬝ᵥ (rightAtom - ratio • leftAtom) = 0 := by
    rw [hresidualNorm, hratioDef]
    field_simp
    linear_combination hlagrange
  exact hnotParallel ratio (sub_eq_zero.mp (dotProduct_self_eq_zero.mp hresidualZero))

/-- **The in-plane mass, cleared of the tilt.**  Parseval at `(probe, seed)`
pins `weightP axisP + weightQ axisQ tiltRatio = 0`, and squaring it turns the
tilt out of the in-plane mass: the mass times `weightQ axisQ^2` is exactly
`seedNormSq weightP`. -/
theorem inPlaneMass_mul_poleSecondAxis
    {weightP weightQ axisP axisQ seedNormSq tiltRatio : ℝ}
    (hparsevalAxis : weightP * axisP ^ 2 + weightQ * axisQ ^ 2 = 1)
    (hparsevalMixed : weightP * axisP + weightQ * axisQ * tiltRatio = 0) :
    seedNormSq * (weightP + weightQ * tiltRatio ^ 2) * (weightQ * axisQ ^ 2)
      = seedNormSq * weightP := by
  linear_combination (seedNormSq * weightP) * hparsevalAxis
    + (seedNormSq * (weightQ * axisQ * tiltRatio - weightP * axisP)) * hparsevalMixed

/-- **The pair gap, cleared of the tilt.**  Multiplying by `weightQ^2 axisQ^2`
turns every occurrence of the tilt into the mixed Parseval relation, leaving a
polynomial in the weights, the two axis components and the seed norm alone. -/
theorem pairGap_mul_poleSecondAxisSq
    {weightP weightQ axisP axisQ seedNormSq tiltRatio : ℝ}
    (hparsevalMixed : weightP * axisP + weightQ * axisQ * tiltRatio = 0) :
    ((axisP ^ 2 + axisQ ^ 2 - 1) * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
        - seedNormSq * (axisP + tiltRatio * axisQ) ^ 2)
        * (weightQ ^ 2 * axisQ ^ 2)
      = (axisP ^ 2 + axisQ ^ 2 - 1)
          * (seedNormSq * weightQ ^ 2 * axisQ ^ 2
            + seedNormSq * weightP ^ 2 * axisP ^ 2 - weightQ ^ 2 * axisQ ^ 2)
        - seedNormSq * axisP ^ 2 * axisQ ^ 2 * (weightQ - weightP) ^ 2 := by
  linear_combination
    (seedNormSq * (weightQ * axisQ * tiltRatio - weightP * axisP
        - 2 * weightQ * axisQ ^ 2 * axisP - weightQ * axisQ ^ 3 * tiltRatio
        + weightP * axisP * axisQ ^ 2)
      - seedNormSq * (weightP * axisP - weightQ * tiltRatio * axisQ)
        * (axisP ^ 2 + axisQ ^ 2 - 2)) * hparsevalMixed

/-- **The steepness masses of the two poles sum to the planar mass.**  Parseval
on the probe axis reads `t_P a_P^2 + t_Q a_Q^2 = 1`; subtracting the two weights
leaves what the planar family carries. -/
theorem steepnessMass_sum_eq_planarMass
    {weightP weightQ axisP axisQ : ℝ}
    (hparsevalAxis : weightP * axisP ^ 2 + weightQ * axisQ ^ 2 = 1) :
    weightP * (axisP ^ 2 - 1) + weightQ * (axisQ ^ 2 - 1)
      = 1 - weightP - weightQ := by
  linarith [hparsevalAxis]

/-- **The favourable half of the crossing comparison makes the FIRST pole
steep.**  The two steepness masses sum to the planar mass, which is positive, so
they cannot both be nonpositive; the comparison then pins which one is not. -/
theorem one_lt_axisFirstSq_of_crossing
    {weightP weightQ axisP axisQ : ℝ}
    (hweightPPos : 0 < weightP) (hweightQPos : 0 < weightQ)
    (hplanarMassPos : 0 < 1 - weightP - weightQ)
    (hparsevalAxis : weightP * axisP ^ 2 + weightQ * axisQ ^ 2 = 1)
    (hcrossing : (1 - weightP) * (weightQ * (axisQ ^ 2 - 1))
      ≤ (1 - weightQ) * (weightP * (axisP ^ 2 - 1))) :
    1 < axisP ^ 2 := by
  have hmassSum := steepnessMass_sum_eq_planarMass hparsevalAxis
  by_contra hflat
  push Not at hflat
  have hmassPNonpos : weightP * (axisP ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hweightPPos.le (by linarith)
  have hmassQPos : 0 < weightQ * (axisQ ^ 2 - 1) := by linarith
  nlinarith [hcrossing, hmassPNonpos, hmassQPos, hweightPPos, hweightQPos,
    hplanarMassPos]

/-- **The unfavourable half makes the SECOND pole steep.**  Mirror image of
`one_lt_axisFirstSq_of_crossing`. -/
theorem one_lt_axisSecondSq_of_crossing
    {weightP weightQ axisP axisQ : ℝ}
    (hweightPPos : 0 < weightP) (hweightQPos : 0 < weightQ)
    (hplanarMassPos : 0 < 1 - weightP - weightQ)
    (hparsevalAxis : weightP * axisP ^ 2 + weightQ * axisQ ^ 2 = 1)
    (hcrossing : (1 - weightQ) * (weightP * (axisP ^ 2 - 1))
      ≤ (1 - weightP) * (weightQ * (axisQ ^ 2 - 1))) :
    1 < axisQ ^ 2 := by
  have hmassSum := steepnessMass_sum_eq_planarMass hparsevalAxis
  by_contra hflat
  push Not at hflat
  have hmassQNonpos : weightQ * (axisQ ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hweightQPos.le (by linarith)
  have hmassPPos : 0 < weightP * (axisP ^ 2 - 1) := by linarith
  nlinarith [hcrossing, hmassQNonpos, hmassPPos, hweightPPos, hweightQPos,
    hplanarMassPos]

/-- **The carrier budget at the first pole.**  Under the favourable half of the
crossing comparison the pole is steep and its budget defect is the exact product
`seedNormSq * weightP * (1 - weightP) * crossingDefect`, hence nonnegative. -/
theorem carrierBudget_of_crossing_poleFirst
    {weightP weightQ axisP axisQ seedNormSq tiltRatio kappa : ℝ}
    (hweightPPos : 0 < weightP) (hweightQPos : 0 < weightQ)
    (hplanarMassPos : 0 < 1 - weightP - weightQ)
    (hseedPos : 0 < seedNormSq)
    (haxisQNe : axisQ ≠ 0)
    (hparsevalAxis : weightP * axisP ^ 2 + weightQ * axisQ ^ 2 = 1)
    (hparsevalMixed : weightP * axisP + weightQ * axisQ * tiltRatio = 0)
    (hcrossing : (1 - weightP) * (weightQ * (axisQ ^ 2 - 1))
      ≤ (1 - weightQ) * (weightP * (axisP ^ 2 - 1)))
    (hkappa : kappa * (axisP ^ 2 - 1) = seedNormSq) :
    1 < axisP ^ 2
      ∧ (axisP ^ 2 + axisQ ^ 2 - 1)
          * (seedNormSq * (weightP + weightQ * tiltRatio ^ 2) + kappa
            - (weightP + weightQ) * (1 + kappa))
        ≤ ((axisP ^ 2 + axisQ ^ 2 - 1) * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
            - seedNormSq * (axisP + tiltRatio * axisQ) ^ 2) * (weightP + weightQ) := by
  have hsteepP : 1 < axisP ^ 2 :=
    one_lt_axisFirstSq_of_crossing hweightPPos hweightQPos hplanarMassPos
      hparsevalAxis hcrossing
  refine ⟨hsteepP, ?_⟩
  set steepP := axisP ^ 2 - 1 with hsteepPDef
  have hsteepPPos : 0 < steepP := by rw [hsteepPDef]; linarith
  set crossingDefect := (1 - weightQ) * (weightP * steepP)
    - (1 - weightP) * (weightQ * (axisQ ^ 2 - 1)) with hcrossingDefectDef
  have hcrossingNonneg : 0 ≤ crossingDefect := by
    rw [hcrossingDefectDef, hsteepPDef]; linarith [hcrossing]
  have haxisQSqPos : 0 < axisQ ^ 2 := by positivity
  set scaleFactor := weightP * steepP * (weightQ ^ 2 * axisQ ^ 2) with hscaleDef
  have hscalePos : 0 < scaleFactor := by
    rw [hscaleDef]
    exact mul_pos (mul_pos hweightPPos hsteepPPos)
      (mul_pos (by positivity) haxisQSqPos)
  set axisBlock := axisP ^ 2 + axisQ ^ 2 - 1 with haxisBlockDef
  set inPlaneMass := seedNormSq * (weightP + weightQ * tiltRatio ^ 2)
    with hinPlaneMassDef
  set pairGap := axisBlock * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
    - seedNormSq * (axisP + tiltRatio * axisQ) ^ 2 with hpairGapDef
  have hmassCleared : inPlaneMass * (weightQ * axisQ ^ 2) = seedNormSq * weightP :=
    inPlaneMass_mul_poleSecondAxis hparsevalAxis hparsevalMixed
  have hgapCleared : pairGap * (weightQ ^ 2 * axisQ ^ 2)
      = axisBlock * (seedNormSq * weightQ ^ 2 * axisQ ^ 2
            + seedNormSq * weightP ^ 2 * axisP ^ 2 - weightQ ^ 2 * axisQ ^ 2)
        - seedNormSq * axisP ^ 2 * axisQ ^ 2 * (weightQ - weightP) ^ 2 :=
    pairGap_mul_poleSecondAxisSq hparsevalMixed
  have hkeyIdentity :
      (pairGap * (weightP + weightQ)
          - axisBlock * (inPlaneMass + kappa - (weightP + weightQ) * (1 + kappa)))
        * scaleFactor
      = seedNormSq * weightP * (1 - weightP) * crossingDefect := by
    have hcofactor : axisBlock
          * (seedNormSq * weightQ ^ 2 * axisQ ^ 2
              + seedNormSq * weightP ^ 2 * axisP ^ 2 - weightQ ^ 2 * axisQ ^ 2)
            * steepP * (weightP + weightQ)
        - seedNormSq * axisP ^ 2 * axisQ ^ 2 * (weightQ - weightP) ^ 2
            * steepP * (weightP + weightQ)
        - axisBlock
          * (steepP * seedNormSq * weightP * weightQ
            + seedNormSq * weightQ ^ 2 * axisQ ^ 2 * (1 - weightP - weightQ)
            - (weightP + weightQ) * steepP * (weightQ ^ 2 * axisQ ^ 2))
        - seedNormSq * (1 - weightP) * crossingDefect = 0 := by
      rw [hcrossingDefectDef, haxisBlockDef, hsteepPDef]
      linear_combination
        (seedNormSq * (weightP ^ 2 * axisP ^ 4 - 2 * weightP ^ 2 * axisP ^ 2
            + weightP ^ 2 + weightP * weightQ * axisP ^ 4
            + weightP * weightQ * axisP ^ 2 * axisQ ^ 2
            - 2 * weightP * weightQ * axisP ^ 2 + weightP * axisP ^ 2 - weightP
            + weightQ ^ 2 * axisP ^ 2 * axisQ ^ 2 - weightQ * axisQ ^ 2
            + weightQ)) * hparsevalAxis
    rw [hscaleDef]
    have hexpand : (pairGap * (weightP + weightQ)
          - axisBlock * (inPlaneMass + kappa - (weightP + weightQ) * (1 + kappa)))
          * (weightP * steepP * (weightQ ^ 2 * axisQ ^ 2))
        = weightP * ((pairGap * (weightQ ^ 2 * axisQ ^ 2)) * steepP
              * (weightP + weightQ)
            - axisBlock * (steepP * (inPlaneMass * (weightQ * axisQ ^ 2)) * weightQ
                + (kappa * steepP) * (weightQ ^ 2 * axisQ ^ 2)
                  * (1 - weightP - weightQ)
                - (weightP + weightQ) * steepP * (weightQ ^ 2 * axisQ ^ 2))) := by
      ring
    rw [hexpand, hgapCleared, hmassCleared, hkappa]
    linear_combination weightP * hcofactor
  have hdefectNonneg : 0 ≤ (pairGap * (weightP + weightQ)
      - axisBlock * (inPlaneMass + kappa - (weightP + weightQ) * (1 + kappa)))
      * scaleFactor := by
    rw [hkeyIdentity]
    have hweightPLt : weightP < 1 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hseedPos.le hweightPPos.le)
      (by linarith)) hcrossingNonneg
  nlinarith [hdefectNonneg, hscalePos]

/-- **The carrier budget at the second pole.**  Mirror of the first: the
unfavourable half of the crossing comparison makes the SECOND pole steep and its
defect the product with the opposite sign of `crossingDefect`. -/
theorem carrierBudget_of_crossing_poleSecond
    {weightP weightQ axisP axisQ seedNormSq tiltRatio kappa : ℝ}
    (hweightPPos : 0 < weightP) (hweightQPos : 0 < weightQ)
    (hplanarMassPos : 0 < 1 - weightP - weightQ)
    (hseedPos : 0 < seedNormSq)
    (haxisQNe : axisQ ≠ 0)
    (hparsevalAxis : weightP * axisP ^ 2 + weightQ * axisQ ^ 2 = 1)
    (hparsevalMixed : weightP * axisP + weightQ * axisQ * tiltRatio = 0)
    (hcrossing : (1 - weightQ) * (weightP * (axisP ^ 2 - 1))
      ≤ (1 - weightP) * (weightQ * (axisQ ^ 2 - 1)))
    (hkappa : kappa * (axisQ ^ 2 - 1) = tiltRatio ^ 2 * seedNormSq) :
    1 < axisQ ^ 2
      ∧ (axisP ^ 2 + axisQ ^ 2 - 1)
          * (seedNormSq * (weightP + weightQ * tiltRatio ^ 2) + kappa
            - (weightP + weightQ) * (1 + kappa))
        ≤ ((axisP ^ 2 + axisQ ^ 2 - 1) * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
            - seedNormSq * (axisP + tiltRatio * axisQ) ^ 2) * (weightP + weightQ) := by
  have hsteepQ : 1 < axisQ ^ 2 :=
    one_lt_axisSecondSq_of_crossing hweightPPos hweightQPos hplanarMassPos
      hparsevalAxis hcrossing
  refine ⟨hsteepQ, ?_⟩
  set steepQ := axisQ ^ 2 - 1 with hsteepQDef
  have hsteepQPos : 0 < steepQ := by rw [hsteepQDef]; linarith
  set crossingDefect := (1 - weightQ) * (weightP * (axisP ^ 2 - 1))
    - (1 - weightP) * (weightQ * steepQ) with hcrossingDefectDef
  have hcrossingNonpos : crossingDefect ≤ 0 := by
    rw [hcrossingDefectDef, hsteepQDef]; linarith [hcrossing]
  have haxisQSqPos : 0 < axisQ ^ 2 := by positivity
  set scaleFactor := weightQ * steepQ * (weightQ * axisQ ^ 2) with hscaleDef
  have hscalePos : 0 < scaleFactor := by
    rw [hscaleDef]
    exact mul_pos (mul_pos hweightQPos hsteepQPos) (mul_pos hweightQPos haxisQSqPos)
  set axisBlock := axisP ^ 2 + axisQ ^ 2 - 1 with haxisBlockDef
  set inPlaneMass := seedNormSq * (weightP + weightQ * tiltRatio ^ 2)
    with hinPlaneMassDef
  set pairGap := axisBlock * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
    - seedNormSq * (axisP + tiltRatio * axisQ) ^ 2 with hpairGapDef
  have hmassCleared : inPlaneMass * (weightQ * axisQ ^ 2) = seedNormSq * weightP :=
    inPlaneMass_mul_poleSecondAxis hparsevalAxis hparsevalMixed
  have hgapCleared : pairGap * (weightQ ^ 2 * axisQ ^ 2)
      = axisBlock * (seedNormSq * weightQ ^ 2 * axisQ ^ 2
            + seedNormSq * weightP ^ 2 * axisP ^ 2 - weightQ ^ 2 * axisQ ^ 2)
        - seedNormSq * axisP ^ 2 * axisQ ^ 2 * (weightQ - weightP) ^ 2 :=
    pairGap_mul_poleSecondAxisSq hparsevalMixed
  have htiltCleared : tiltRatio ^ 2 * (weightQ ^ 2 * axisQ ^ 2)
      = weightP ^ 2 * axisP ^ 2 := by
    linear_combination (weightQ * axisQ * tiltRatio - weightP * axisP) * hparsevalMixed
  have hkeyIdentity :
      (pairGap * (weightP + weightQ)
          - axisBlock * (inPlaneMass + kappa - (weightP + weightQ) * (1 + kappa)))
        * scaleFactor
      = seedNormSq * (1 - weightQ) * (-crossingDefect) := by
    have hcofactor : axisBlock
          * (seedNormSq * weightQ ^ 2 * axisQ ^ 2
              + seedNormSq * weightP ^ 2 * axisP ^ 2 - weightQ ^ 2 * axisQ ^ 2)
            * steepQ * (weightP + weightQ)
        - seedNormSq * axisP ^ 2 * axisQ ^ 2 * (weightQ - weightP) ^ 2
            * steepQ * (weightP + weightQ)
        - axisBlock
          * (steepQ * seedNormSq * weightP * weightQ
            + seedNormSq * weightP ^ 2 * axisP ^ 2 * (1 - weightP - weightQ)
            - (weightP + weightQ) * steepQ * (weightQ ^ 2 * axisQ ^ 2))
        - seedNormSq * (1 - weightQ) * (-crossingDefect) = 0 := by
      rw [hcrossingDefectDef, haxisBlockDef, hsteepQDef]
      linear_combination
        (seedNormSq * (weightP ^ 2 * axisP ^ 2 * axisQ ^ 2
            + weightP * weightQ * axisP ^ 2 * axisQ ^ 2
            + weightP * weightQ * axisQ ^ 4 - 2 * weightP * weightQ * axisQ ^ 2
            - weightP * axisP ^ 2 + weightP + weightQ ^ 2 * axisQ ^ 4
            - 2 * weightQ ^ 2 * axisQ ^ 2 + weightQ ^ 2 + weightQ * axisQ ^ 2
            - weightQ)) * hparsevalAxis
    rw [hscaleDef]
    have hexpand : (pairGap * (weightP + weightQ)
          - axisBlock * (inPlaneMass + kappa - (weightP + weightQ) * (1 + kappa)))
          * (weightQ * steepQ * (weightQ * axisQ ^ 2))
        = (pairGap * (weightQ ^ 2 * axisQ ^ 2)) * steepQ * (weightP + weightQ)
            - axisBlock * (steepQ * (inPlaneMass * (weightQ * axisQ ^ 2)) * weightQ
                + (kappa * steepQ) * (weightQ ^ 2 * axisQ ^ 2)
                  * (1 - weightP - weightQ)
                - (weightP + weightQ) * steepQ * (weightQ ^ 2 * axisQ ^ 2)) := by
      ring
    rw [hexpand, hgapCleared, hmassCleared, hkappa]
    have hshadow : tiltRatio ^ 2 * seedNormSq * (weightQ ^ 2 * axisQ ^ 2)
        * (1 - weightP - weightQ)
        = seedNormSq * weightP ^ 2 * axisP ^ 2 * (1 - weightP - weightQ) := by
      linear_combination (seedNormSq * (1 - weightP - weightQ)) * htiltCleared
    linear_combination hcofactor - axisBlock * hshadow
  have hdefectNonneg : 0 ≤ (pairGap * (weightP + weightQ)
      - axisBlock * (inPlaneMass + kappa - (weightP + weightQ) * (1 + kappa)))
      * scaleFactor := by
    rw [hkeyIdentity]
    have hweightQLt : weightQ < 1 := by linarith
    exact mul_nonneg (mul_nonneg hseedPos.le (by linarith)) (by linarith)
  nlinarith [hdefectNonneg, hscalePos]

/-! ## Companion Part B: the companion, and the pair the hinge hands back

The companion is the template's reweighted rank-two design AT COMPANION SCALE
ONE.  That single choice is what deletes the transport gate: the scale only ever
existed to buy a strict conclusion out of a weakly dominating pair, and a pair
that is positive definite pays for itself.  At scale one the weight budget

    2 poleWeight + planarMass = poleMass + planarMass = 1

is an identity rather than a condition, and the shadow entry it forces,
`poleShadow = (nu + kappa) / poleMass`, is the SMALLEST any admissible scale
reaches — which is exactly what the mixed branch wants, since its obligation
grows with the shadow. -/

/-- **The planar family is uncorrelated in the `(seed, cross)` frame.**  Parseval
at the pair `(seed, cross)`: the seed and its cross product are orthogonal and
both poles are blind to the cross direction, so the pole terms drop and the
planar sum reads zero on the nose. -/
theorem planarMixedMoment_eq_zero {size : ℕ} (design : WeightedDesign size 3)
    (poleP poleQ : Fin size) (probe : Fin 3 → ℝ) (tiltRatio : ℝ)
    (hunit : probe ⬝ᵥ probe = 1) (hpoleNe : poleP ≠ poleQ)
    (hantiparallel : design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe
      = tiltRatio • (design.atom poleP
        - (design.atom poleP ⬝ᵥ probe) • probe)) :
    ∑ c ∈ (Finset.univ.erase poleP).erase poleQ,
        design.weight c
          * ((design.atom c ⬝ᵥ (design.atom poleP
                - (design.atom poleP ⬝ᵥ probe) • probe))
            * (design.atom c ⬝ᵥ crossProduct probe (design.atom poleP
                - (design.atom poleP ⬝ᵥ probe) • probe))) = 0 := by
  classical
  set poleAxisP := design.atom poleP ⬝ᵥ probe with hpoleAxisPDef
  set seedVec := design.atom poleP - poleAxisP • probe with hseedDef
  set crossVec := crossProduct probe seedVec with hcrossDef
  have hseedPlanar : probe ⬝ᵥ seedVec = 0 := by
    rw [hseedDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit,
      dotProduct_comm probe (design.atom poleP)]
    ring
  have hpolePDecomp : design.atom poleP = seedVec + poleAxisP • probe := by
    rw [hseedDef]; abel
  have hpoleQDecomp : design.atom poleQ
      = tiltRatio • seedVec + (design.atom poleQ ⬝ᵥ probe) • probe :=
    sub_eq_iff_eq_add.mp hantiparallel
  have hpoleCrossP : design.atom poleP ⬝ᵥ crossVec = 0 := by
    rw [hpolePDecomp, add_dotProduct, smul_dotProduct, smul_eq_mul, hcrossDef,
      planarCross_seed_dot, planarCross_probe_dot]
    ring
  have hpoleCrossQ : design.atom poleQ ⬝ᵥ crossVec = 0 := by
    rw [hpoleQDecomp, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, hcrossDef, planarCross_seed_dot,
      planarCross_probe_dot]
    ring
  have hseedCross : seedVec ⬝ᵥ crossVec = 0 := by
    rw [hcrossDef, planarCross_seed_dot]
  have hqMemErase : poleQ ∈ Finset.univ.erase poleP :=
    Finset.mem_erase.mpr ⟨fun hEq => hpoleNe hEq.symm, Finset.mem_univ poleQ⟩
  have hsplit : ∀ scoreFn : Fin size → ℝ,
      ∑ c, scoreFn c
        = scoreFn poleP + (scoreFn poleQ
            + ∑ c ∈ (Finset.univ.erase poleP).erase poleQ, scoreFn c) := by
    intro scoreFn
    rw [← Finset.add_sum_erase _ scoreFn (Finset.mem_univ poleP),
      ← Finset.add_sum_erase _ scoreFn hqMemErase]
  have htotal := sum_weighted_atomPairing design seedVec crossVec
  rw [hsplit (fun c => design.weight c
      * ((design.atom c ⬝ᵥ seedVec) * (design.atom c ⬝ᵥ crossVec)))] at htotal
  rw [hpoleCrossP, hpoleCrossQ, hseedCross] at htotal
  linear_combination htotal

/-- The companion atom at scale one: both pole labels carry the bundled shadow on
the seed axis, every other label carries its rescaled planar coordinates. -/
noncomputable def strictCompanionAtom (alongCoord acrossCoord : Fin 6 → ℝ)
    (poleP poleQ : Fin 6) (poleEntry : ℝ) (label : Fin 6) : Fin 2 → ℝ :=
  if label = poleP then ![poleEntry, 0]
  else if label = poleQ then ![poleEntry, 0]
  else ![alongCoord label, acrossCoord label]

/-- The companion weight at scale one: the shared pole share on each pole label,
the design's own weight elsewhere. -/
noncomputable def strictCompanionWeight (planarWeight : Fin 6 → ℝ)
    (poleP poleQ : Fin 6) (poleWeight : ℝ) (label : Fin 6) : ℝ :=
  if label = poleP then poleWeight
  else if label = poleQ then poleWeight
  else planarWeight label

set_option maxHeartbeats 2000000 in
/-- **The hinge on the companion.**  Under the three planar moment identities and
the weight budget the companion data is a genuine weighted `(6, 2)` design; its
four planar labels are pairwise non-parallel exactly when their raw brackets are
nonzero, so the handoff's antecedent applies and returns a POSITIVE DEFINITE
pair.  What comes out is the strict master inequality both scalar branches read,
at every nonzero test vector. -/
theorem exists_strictCompanionPair_of_moments
    (hstrictPair : ∀ (companion : WeightedDesign 6 2)
      (firstLabel secondLabel thirdLabel fourthLabel : Fin 6),
      firstLabel ≠ secondLabel → firstLabel ≠ thirdLabel → firstLabel ≠ fourthLabel →
      secondLabel ≠ thirdLabel → secondLabel ≠ fourthLabel → thirdLabel ≠ fourthLabel →
      pairBracket companion firstLabel secondLabel ≠ 0 →
      pairBracket companion firstLabel thirdLabel ≠ 0 →
      pairBracket companion firstLabel fourthLabel ≠ 0 →
      pairBracket companion secondLabel thirdLabel ≠ 0 →
      pairBracket companion secondLabel fourthLabel ≠ 0 →
      pairBracket companion thirdLabel fourthLabel ≠ 0 →
      ∃ dominatingPair : Finset (Fin 6), dominatingPair.card = 2
        ∧ (subsetSum companion dominatingPair - 1).PosDef)
    (alongCoord acrossCoord planarWeight : Fin 6 → ℝ)
    (poleP poleQ : Fin 6) (poleEntry poleWeight : ℝ)
    (hpoleNe : poleP ≠ poleQ)
    (hpoleWeightPos : 0 < poleWeight)
    (hplanarWeightPos : ∀ c, c ≠ poleP → c ≠ poleQ → 0 < planarWeight c)
    (hweightBudget : 2 * poleWeight
      + ∑ c ∈ (Finset.univ.erase poleP).erase poleQ, planarWeight c = 1)
    (halongMoment : 2 * (poleWeight * poleEntry ^ 2)
      + ∑ c ∈ (Finset.univ.erase poleP).erase poleQ,
          planarWeight c * alongCoord c ^ 2 = 1)
    (hacrossMoment : ∑ c ∈ (Finset.univ.erase poleP).erase poleQ,
        planarWeight c * acrossCoord c ^ 2 = 1)
    (hmixedMoment : ∑ c ∈ (Finset.univ.erase poleP).erase poleQ,
        planarWeight c * (alongCoord c * acrossCoord c) = 0)
    (hplanarBracket : ∀ leftLabel rightLabel : Fin 6,
      leftLabel ≠ poleP → leftLabel ≠ poleQ →
      rightLabel ≠ poleP → rightLabel ≠ poleQ → leftLabel ≠ rightLabel →
      alongCoord leftLabel * acrossCoord rightLabel
        - alongCoord rightLabel * acrossCoord leftLabel ≠ 0) :
    ∃ firstLabel secondLabel : Fin 6, firstLabel ≠ secondLabel
      ∧ ∀ testVec : Fin 2 → ℝ, testVec ≠ 0 →
          testVec ⬝ᵥ testVec
            < (strictCompanionAtom alongCoord acrossCoord poleP poleQ poleEntry
                  firstLabel ⬝ᵥ testVec) ^ 2
              + (strictCompanionAtom alongCoord acrossCoord poleP poleQ poleEntry
                  secondLabel ⬝ᵥ testVec) ^ 2 := by
  classical
  set atomFn := strictCompanionAtom alongCoord acrossCoord poleP poleQ poleEntry
    with hatomFnDef
  set weightFn := strictCompanionWeight planarWeight poleP poleQ poleWeight
    with hweightFnDef
  set othersSet := (Finset.univ.erase poleP).erase poleQ with hothersDef
  have hqMemErase : poleQ ∈ Finset.univ.erase poleP :=
    Finset.mem_erase.mpr ⟨fun hEq => hpoleNe hEq.symm, Finset.mem_univ poleQ⟩
  have hsplit : ∀ scoreFn : Fin 6 → ℝ,
      ∑ c, scoreFn c
        = scoreFn poleP + (scoreFn poleQ + ∑ c ∈ othersSet, scoreFn c) := by
    intro scoreFn
    rw [← Finset.add_sum_erase _ scoreFn (Finset.mem_univ poleP),
      ← Finset.add_sum_erase _ scoreFn hqMemErase, hothersDef]
  have hothersNotP : ∀ c ∈ othersSet, c ≠ poleP := fun c hmem =>
    (Finset.mem_erase.mp ((Finset.mem_erase.mp hmem).2)).1
  have hothersNotQ : ∀ c ∈ othersSet, c ≠ poleQ := fun c hmem =>
    (Finset.mem_erase.mp hmem).1
  have hmemOthers : ∀ c : Fin 6, c ≠ poleP → c ≠ poleQ → c ∈ othersSet := by
    intro c hcP hcQ
    rw [hothersDef]
    exact Finset.mem_erase.mpr ⟨hcQ, Finset.mem_erase.mpr ⟨hcP, Finset.mem_univ c⟩⟩
  have hweightP : weightFn poleP = poleWeight := by
    simp [hweightFnDef, strictCompanionWeight]
  have hweightQ : weightFn poleQ = poleWeight := by
    simp [hweightFnDef, strictCompanionWeight, Ne.symm hpoleNe]
  have hweightOther : ∀ c ∈ othersSet, weightFn c = planarWeight c := by
    intro c hmem
    simp [hweightFnDef, strictCompanionWeight, hothersNotP c hmem, hothersNotQ c hmem]
  have hatomP : atomFn poleP = ![poleEntry, 0] := by
    simp [hatomFnDef, strictCompanionAtom]
  have hatomQ : atomFn poleQ = ![poleEntry, 0] := by
    simp [hatomFnDef, strictCompanionAtom, Ne.symm hpoleNe]
  have hatomOther : ∀ c : Fin 6, c ≠ poleP → c ≠ poleQ →
      atomFn c = ![alongCoord c, acrossCoord c] := by
    intro c hcP hcQ
    simp [hatomFnDef, strictCompanionAtom, hcP, hcQ]
  have hweightPos : ∀ c, 0 < weightFn c := by
    intro c
    by_cases hcP : c = poleP
    · rw [hcP, hweightP]; exact hpoleWeightPos
    · by_cases hcQ : c = poleQ
      · rw [hcQ, hweightQ]; exact hpoleWeightPos
      · rw [hweightOther c (hmemOthers c hcP hcQ)]
        exact hplanarWeightPos c hcP hcQ
  have hweightSumOne : ∑ c, weightFn c = 1 := by
    rw [hsplit weightFn, hweightP, hweightQ, Finset.sum_congr rfl hweightOther]
    linarith [hweightBudget]
  have hpoint : ∀ (c : Fin 6) (rowIndex colIndex : Fin 2),
      (weightFn c • atomMatrix (atomFn c)) rowIndex colIndex
        = weightFn c * (atomFn c rowIndex * atomFn c colIndex) := by
    intro c rowIndex colIndex
    simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  have hentrySum : ∀ rowIndex colIndex : Fin 2,
      (∑ c, weightFn c • atomMatrix (atomFn c)) rowIndex colIndex
        = poleWeight * ((![poleEntry, 0] : Fin 2 → ℝ) rowIndex
              * (![poleEntry, 0] : Fin 2 → ℝ) colIndex)
          + (poleWeight * ((![poleEntry, 0] : Fin 2 → ℝ) rowIndex
                * (![poleEntry, 0] : Fin 2 → ℝ) colIndex)
            + ∑ c ∈ othersSet, planarWeight c
                * ((![alongCoord c, acrossCoord c] : Fin 2 → ℝ) rowIndex
                  * (![alongCoord c, acrossCoord c] : Fin 2 → ℝ) colIndex)) := by
    intro rowIndex colIndex
    have hcongr : ∀ c ∈ othersSet,
        weightFn c * (atomFn c rowIndex * atomFn c colIndex)
          = planarWeight c
            * ((![alongCoord c, acrossCoord c] : Fin 2 → ℝ) rowIndex
              * (![alongCoord c, acrossCoord c] : Fin 2 → ℝ) colIndex) := by
      intro c hmem
      rw [hweightOther c hmem, hatomOther c (hothersNotP c hmem) (hothersNotQ c hmem)]
    rw [Matrix.sum_apply,
      Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => hpoint c rowIndex colIndex),
      hsplit (fun c => weightFn c * (atomFn c rowIndex * atomFn c colIndex)),
      hweightP, hweightQ, hatomP, hatomQ, Finset.sum_congr rfl hcongr]
  have hparseval : ∑ c, weightFn c • atomMatrix (atomFn c)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    refine Matrix.ext ?_
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩ <;>
      rw [hentrySum, Matrix.one_apply] <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, mul_zero,
        zero_mul, reduceIte]
    · have hsq : ∀ c ∈ othersSet,
          planarWeight c * (alongCoord c * alongCoord c)
            = planarWeight c * alongCoord c ^ 2 := fun c _ => by ring
      rw [Finset.sum_congr rfl hsq]
      linarith [halongMoment]
    · rw [if_neg (by decide : ¬ ((0 : Fin 2) = 1))]
      linarith [hmixedMoment]
    · rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0)),
        Finset.sum_congr rfl (fun c (_ : c ∈ othersSet) =>
        (by ring : planarWeight c * (acrossCoord c * alongCoord c)
          = planarWeight c * (alongCoord c * acrossCoord c)))]
      linarith [hmixedMoment]
    · have hsq : ∀ c ∈ othersSet,
          planarWeight c * (acrossCoord c * acrossCoord c)
            = planarWeight c * acrossCoord c ^ 2 := fun c _ => by ring
      rw [Finset.sum_congr rfl hsq]
      linarith [hacrossMoment]
  set companion : WeightedDesign 6 2 :=
    ⟨atomFn, weightFn, hweightPos, hweightSumOne, hparseval⟩ with hcompanionDef
  -- the four planar labels, and their brackets
  have hcardOthers : othersSet.card = 4 := by
    rw [hothersDef, Finset.card_erase_of_mem hqMemErase,
      Finset.card_erase_of_mem (Finset.mem_univ poleP), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨planarOne, hplanarOneMem⟩ :=
    Finset.card_pos.mp (by rw [hcardOthers]; norm_num : 0 < othersSet.card)
  have hrestCard : (othersSet.erase planarOne).card = 3 := by
    rw [Finset.card_erase_of_mem hplanarOneMem, hcardOthers]
  obtain ⟨planarTwo, planarThree, planarFour, htwoThree, htwoFour, hthreeFour,
    hrestEq⟩ := Finset.card_eq_three.mp hrestCard
  have hrestMem : ∀ c : Fin 6, c = planarTwo ∨ c = planarThree ∨ c = planarFour →
      c ∈ othersSet.erase planarOne := by
    intro c hmem
    rw [hrestEq]
    rcases hmem with rfl | rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))
  have honeNe : ∀ c : Fin 6, c = planarTwo ∨ c = planarThree ∨ c = planarFour →
      planarOne ≠ c := fun c hmem hEq =>
    (Finset.mem_erase.mp (hrestMem c hmem)).1 hEq.symm
  have hplanarMem : ∀ c : Fin 6,
      c = planarOne ∨ c = planarTwo ∨ c = planarThree ∨ c = planarFour →
      c ∈ othersSet := by
    intro c hmem
    rcases hmem with rfl | hmem
    · exact hplanarOneMem
    · exact (Finset.mem_erase.mp (hrestMem c hmem)).2
  have hbracketAt : ∀ leftLabel rightLabel : Fin 6,
      (leftLabel = planarOne ∨ leftLabel = planarTwo ∨ leftLabel = planarThree
        ∨ leftLabel = planarFour) →
      (rightLabel = planarOne ∨ rightLabel = planarTwo ∨ rightLabel = planarThree
        ∨ rightLabel = planarFour) →
      leftLabel ≠ rightLabel → pairBracket companion leftLabel rightLabel ≠ 0 := by
    intro leftLabel rightLabel hleft hright hne
    have hleftMem := hplanarMem leftLabel hleft
    have hrightMem := hplanarMem rightLabel hright
    have hleftAtom : companion.atom leftLabel = ![alongCoord leftLabel,
        acrossCoord leftLabel] :=
      hatomOther leftLabel (hothersNotP _ hleftMem) (hothersNotQ _ hleftMem)
    have hrightAtom : companion.atom rightLabel = ![alongCoord rightLabel,
        acrossCoord rightLabel] :=
      hatomOther rightLabel (hothersNotP _ hrightMem) (hothersNotQ _ hrightMem)
    have hvalue : pairBracket companion leftLabel rightLabel
        = alongCoord leftLabel * acrossCoord rightLabel
          - alongCoord rightLabel * acrossCoord leftLabel := by
      rw [pairBracket, hleftAtom, hrightAtom]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
      ring
    rw [hvalue]
    exact hplanarBracket leftLabel rightLabel (hothersNotP _ hleftMem)
      (hothersNotQ _ hleftMem) (hothersNotP _ hrightMem) (hothersNotQ _ hrightMem) hne
  obtain ⟨dominatingPair, hcard, hposDef⟩ :=
    hstrictPair companion planarOne planarTwo planarThree planarFour
      (honeNe planarTwo (Or.inl rfl)) (honeNe planarThree (Or.inr (Or.inl rfl)))
      (honeNe planarFour (Or.inr (Or.inr rfl))) htwoThree htwoFour hthreeFour
      (hbracketAt _ _ (Or.inl rfl) (Or.inr (Or.inl rfl))
        (honeNe planarTwo (Or.inl rfl)))
      (hbracketAt _ _ (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
        (honeNe planarThree (Or.inr (Or.inl rfl))))
      (hbracketAt _ _ (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
        (honeNe planarFour (Or.inr (Or.inr rfl))))
      (hbracketAt _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) htwoThree)
      (hbracketAt _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) htwoFour)
      (hbracketAt _ _ (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
        hthreeFour)
  obtain ⟨firstLabel, secondLabel, hlabelNe, hpairEq⟩ := Finset.card_eq_two.mp hcard
  refine ⟨firstLabel, secondLabel, hlabelNe, fun testVec htestNonzero => ?_⟩
  have hquad := quadForm_gt_of_posDef_pair companion dominatingPair hposDef testVec
    htestNonzero
  rw [hpairEq, Finset.sum_pair hlabelNe] at hquad
  exact hquad

/-- **Parseval at `(probe, seed)` pins the tilt to the two axis components.**
The planar atoms are blind to the probe, so only the poles contribute, and their
seed pairings are `seedNormSq` and `tiltRatio * seedNormSq`; dividing out the
positive seed norm leaves the sector's mixed relation. -/
theorem mixedParseval_of_offPlanePair {size : ℕ} (design : WeightedDesign size 3)
    (poleP poleQ : Fin size) (probe : Fin 3 → ℝ) (tiltRatio : ℝ)
    (hunit : probe ⬝ᵥ probe = 1) (hpoleNe : poleP ≠ poleQ)
    (hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0)
    (hantiparallel : design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe
      = tiltRatio • (design.atom poleP
        - (design.atom poleP ⬝ᵥ probe) • probe))
    (hseedNe : design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe ≠ 0) :
    design.weight poleP * (design.atom poleP ⬝ᵥ probe)
      + design.weight poleQ * (design.atom poleQ ⬝ᵥ probe) * tiltRatio = 0 := by
  classical
  set poleAxisP := design.atom poleP ⬝ᵥ probe with hpoleAxisPDef
  set seedVec := design.atom poleP - poleAxisP • probe with hseedDef
  have hseedPos : 0 < seedVec ⬝ᵥ seedVec := dotProduct_self_pos hseedNe
  have hseedPlanar : probe ⬝ᵥ seedVec = 0 := by
    rw [hseedDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit,
      dotProduct_comm probe (design.atom poleP)]
    ring
  have hpolePDecomp : design.atom poleP = seedVec + poleAxisP • probe := by
    rw [hseedDef]; abel
  have hpoleQDecomp : design.atom poleQ
      = tiltRatio • seedVec + (design.atom poleQ ⬝ᵥ probe) • probe :=
    sub_eq_iff_eq_add.mp hantiparallel
  have hpoleSeedP : design.atom poleP ⬝ᵥ seedVec = seedVec ⬝ᵥ seedVec := by
    rw [hpolePDecomp, add_dotProduct, smul_dotProduct, smul_eq_mul, hseedPlanar]
    ring
  have hpoleSeedQ : design.atom poleQ ⬝ᵥ seedVec
      = tiltRatio * (seedVec ⬝ᵥ seedVec) := by
    rw [hpoleQDecomp, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, hseedPlanar]
    ring
  have hqMemErase : poleQ ∈ Finset.univ.erase poleP :=
    Finset.mem_erase.mpr ⟨fun hEq => hpoleNe hEq.symm, Finset.mem_univ poleQ⟩
  have hsplit : ∀ scoreFn : Fin size → ℝ,
      ∑ c, scoreFn c
        = scoreFn poleP + (scoreFn poleQ
            + ∑ c ∈ (Finset.univ.erase poleP).erase poleQ, scoreFn c) := by
    intro scoreFn
    rw [← Finset.add_sum_erase _ scoreFn (Finset.mem_univ poleP),
      ← Finset.add_sum_erase _ scoreFn hqMemErase]
  have htotal := sum_weighted_atomPairing design probe seedVec
  rw [hsplit (fun c => design.weight c
      * ((design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ seedVec)))] at htotal
  have hplanarZero : ∑ c ∈ (Finset.univ.erase poleP).erase poleQ,
      design.weight c * ((design.atom c ⬝ᵥ probe) * (design.atom c ⬝ᵥ seedVec))
      = 0 :=
    Finset.sum_eq_zero fun c hmem => by
      rw [hplanarOthers c (Finset.mem_erase.mp ((Finset.mem_erase.mp hmem).2)).1
        (Finset.mem_erase.mp hmem).1]
      ring
  rw [hplanarZero, hpoleSeedP, hpoleSeedQ, hseedPlanar] at htotal
  have hfactor : (seedVec ⬝ᵥ seedVec)
      * (design.weight poleP * poleAxisP
        + design.weight poleQ * (design.atom poleQ ⬝ᵥ probe) * tiltRatio) = 0 := by
    linear_combination htotal
  exact (mul_eq_zero.mp hfactor).resolve_left hseedPos.ne'

/-! ## Companion Part C: the transport, and the handoff discharged

At companion scale one the three shapes the returned pair can take are all paid
for, and none of them costs a hypothesis:

* TWO POLE SHADOWS — impossible.  Both shadows sit on the seed axis, so the pair
  is blind to the cross direction and the master inequality at `(0, 1)` reads
  `seedNormSq < 0`.
* A POLE SHADOW WITH A PLANAR ATOM — `mixedPair_alongBound_of_strictMaster`,
  then the carrier budget of Part A carries its strict conclusion across to the
  landed scalar gate, and both poles complete the atom to a triple.
* TWO PLANAR ATOMS — `planarPair_strictTarget_of_strictMaster`, and the steep
  carrier completes them through the landed strict carrier reduction.

The budget is the only thing the mixed branch ever needed, it is needed only
NON-STRICTLY, and Part A proves it. -/

set_option maxHeartbeats 4000000 in
/-- **THE TRANSPORT, with the gate deleted.**  Given the handoff's antecedent —
four pairwise non-parallel labels of a rank-two design carry a POSITIVE DEFINITE
pair — a primitive two-pole coplanar `(6,3)` configuration with a steep carrier
whose budget is payable has a strictly dominating triple.  No weight budget, no
companion scale below one, no slack, no crossing-locus hypothesis. -/
theorem exists_posDef_triple_of_strictCompanion
    (hstrictPair : ∀ (companion : WeightedDesign 6 2)
      (firstLabel secondLabel thirdLabel fourthLabel : Fin 6),
      firstLabel ≠ secondLabel → firstLabel ≠ thirdLabel → firstLabel ≠ fourthLabel →
      secondLabel ≠ thirdLabel → secondLabel ≠ fourthLabel → thirdLabel ≠ fourthLabel →
      pairBracket companion firstLabel secondLabel ≠ 0 →
      pairBracket companion firstLabel thirdLabel ≠ 0 →
      pairBracket companion firstLabel fourthLabel ≠ 0 →
      pairBracket companion secondLabel thirdLabel ≠ 0 →
      pairBracket companion secondLabel fourthLabel ≠ 0 →
      pairBracket companion thirdLabel fourthLabel ≠ 0 →
      ∃ dominatingPair : Finset (Fin 6), dominatingPair.card = 2
        ∧ (subsetSum companion dominatingPair - 1).PosDef)
    (design : WeightedDesign 6 3)
    (poleP poleQ thirdLabel carrierLabel : Fin 6)
    (probe : Fin 3 → ℝ)
    (tiltRatio carrierTilt kappa seedNormSq axisBlock pairGap poleMass
      inPlaneMass : ℝ)
    (hunit : probe ⬝ᵥ probe = 1)
    (hpoleNe : poleP ≠ poleQ)
    (hthirdP : thirdLabel ≠ poleP) (hthirdQ : thirdLabel ≠ poleQ)
    (hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0)
    (hprimitive : IsPrimitiveDesign design)
    (hantiparallel : design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe
      = tiltRatio • (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
    (hseedNe : design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe ≠ 0)
    (hseedNormDef : seedNormSq
      = (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
        ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
    (haxisBlockDef : axisBlock
      = (design.atom poleP ⬝ᵥ probe) ^ 2 + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
    (hpairGapDef : pairGap
      = axisBlock * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
        - seedNormSq * ((design.atom poleP ⬝ᵥ probe)
          + tiltRatio * (design.atom poleQ ⬝ᵥ probe)) ^ 2)
    (hpoleMassDef : poleMass = design.weight poleP + design.weight poleQ)
    (hinPlaneMassDef : inPlaneMass
      = seedNormSq * (design.weight poleP + design.weight poleQ * tiltRatio ^ 2))
    (hcarrierPole : carrierLabel = poleP ∨ carrierLabel = poleQ)
    (hcarrierPart : design.atom carrierLabel
        - (design.atom carrierLabel ⬝ᵥ probe) • probe
      = carrierTilt • (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
    (hcarrierSteep : 1 < (design.atom carrierLabel ⬝ᵥ probe) ^ 2)
    (hkappaDef : kappa * ((design.atom carrierLabel ⬝ᵥ probe) ^ 2 - 1)
      = carrierTilt ^ 2 * seedNormSq)
    (hbudget : axisBlock * (inPlaneMass + kappa - poleMass * (1 + kappa))
      ≤ pairGap * poleMass) :
    ∃ dominatingTriple : Finset (Fin 6), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef := by
  classical
  set poleAxisP := design.atom poleP ⬝ᵥ probe with hpoleAxisPDef
  set poleAxisQ := design.atom poleQ ⬝ᵥ probe with hpoleAxisQDef
  set seedVec := design.atom poleP - poleAxisP • probe with hseedDef
  set crossVec := crossProduct probe seedVec with hcrossDef
  set othersSet := (Finset.univ.erase poleP).erase poleQ with hothersDef
  set weightP := design.weight poleP with hweightPDef
  set weightQ := design.weight poleQ with hweightQDef
  -- the frame
  have hseedPos : 0 < seedNormSq := by
    rw [hseedNormDef]; exact dotProduct_self_pos hseedNe
  have hseedNormNe : seedNormSq ≠ 0 := hseedPos.ne'
  have hseedPlanar : probe ⬝ᵥ seedVec = 0 := by
    rw [hseedDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit,
      dotProduct_comm probe (design.atom poleP)]
    ring
  have hseedPerp : seedVec ⬝ᵥ probe = 0 := by
    rw [dotProduct_comm]; exact hseedPlanar
  have hpolePDecomp : design.atom poleP = seedVec + poleAxisP • probe := by
    rw [hseedDef]; abel
  have hpoleQDecomp : design.atom poleQ = tiltRatio • seedVec + poleAxisQ • probe :=
    sub_eq_iff_eq_add.mp hantiparallel
  have hpoleSeedP : design.atom poleP ⬝ᵥ seedVec = seedNormSq := by
    rw [hpolePDecomp, add_dotProduct, smul_dotProduct, smul_eq_mul, hseedPlanar,
      hseedNormDef]
    ring
  have hpoleSeedQ : design.atom poleQ ⬝ᵥ seedVec = tiltRatio * seedNormSq := by
    rw [hpoleQDecomp, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, hseedPlanar, hseedNormDef]
    ring
  have hpoleCrossP : design.atom poleP ⬝ᵥ crossVec = 0 := by
    rw [hpolePDecomp, add_dotProduct, smul_dotProduct, smul_eq_mul, hcrossDef,
      planarCross_seed_dot, planarCross_probe_dot]
    ring
  have hpoleCrossQ : design.atom poleQ ⬝ᵥ crossVec = 0 := by
    rw [hpoleQDecomp, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, hcrossDef, planarCross_seed_dot,
      planarCross_probe_dot]
    ring
  have hcrossNorm : crossVec ⬝ᵥ crossVec = seedNormSq := by
    rw [hcrossDef, planarCross_self_dot, hunit, hseedPlanar, hseedNormDef]
    ring
  have hqMemErase : poleQ ∈ Finset.univ.erase poleP :=
    Finset.mem_erase.mpr ⟨fun hEq => hpoleNe hEq.symm, Finset.mem_univ poleQ⟩
  have hsplit : ∀ scoreFn : Fin 6 → ℝ,
      ∑ c, scoreFn c
        = scoreFn poleP + (scoreFn poleQ + ∑ c ∈ othersSet, scoreFn c) := by
    intro scoreFn
    rw [← Finset.add_sum_erase _ scoreFn (Finset.mem_univ poleP),
      ← Finset.add_sum_erase _ scoreFn hqMemErase, hothersDef]
  have hothersNotP : ∀ c ∈ othersSet, c ≠ poleP := fun c hmem =>
    (Finset.mem_erase.mp ((Finset.mem_erase.mp hmem).2)).1
  have hothersNotQ : ∀ c ∈ othersSet, c ≠ poleQ := fun c hmem =>
    (Finset.mem_erase.mp hmem).1
  -- the three planar moments
  have hseedMoment : ∑ c ∈ othersSet,
        design.weight c * (design.atom c ⬝ᵥ seedVec) ^ 2
      = seedNormSq * (1 - inPlaneMass) := by
    have htotal := sum_weighted_atomPairing design seedVec seedVec
    rw [hsplit (fun c => design.weight c
        * ((design.atom c ⬝ᵥ seedVec) * (design.atom c ⬝ᵥ seedVec)))] at htotal
    rw [hpoleSeedP, hpoleSeedQ, ← hseedNormDef, ← hweightPDef, ← hweightQDef]
      at htotal
    have hsquares : ∑ c ∈ othersSet,
        design.weight c * ((design.atom c ⬝ᵥ seedVec) * (design.atom c ⬝ᵥ seedVec))
        = ∑ c ∈ othersSet, design.weight c * (design.atom c ⬝ᵥ seedVec) ^ 2 :=
      Finset.sum_congr rfl fun c _ => by ring
    rw [hsquares] at htotal
    rw [hinPlaneMassDef]
    linear_combination htotal
  have hcrossMoment : ∑ c ∈ othersSet,
        design.weight c * (design.atom c ⬝ᵥ crossVec) ^ 2 = seedNormSq := by
    have htotal := sum_weighted_atomPairing design crossVec crossVec
    rw [hsplit (fun c => design.weight c
        * ((design.atom c ⬝ᵥ crossVec) * (design.atom c ⬝ᵥ crossVec)))] at htotal
    rw [hpoleCrossP, hpoleCrossQ, hcrossNorm] at htotal
    have hsquares : ∑ c ∈ othersSet,
        design.weight c * ((design.atom c ⬝ᵥ crossVec) * (design.atom c ⬝ᵥ crossVec))
        = ∑ c ∈ othersSet, design.weight c * (design.atom c ⬝ᵥ crossVec) ^ 2 :=
      Finset.sum_congr rfl fun c _ => by ring
    rw [hsquares] at htotal
    linear_combination htotal
  have hmixedMoment : ∑ c ∈ othersSet,
      design.weight c
        * ((design.atom c ⬝ᵥ seedVec) * (design.atom c ⬝ᵥ crossVec)) = 0 :=
    planarMixedMoment_eq_zero design poleP poleQ probe tiltRatio hunit hpoleNe
      hantiparallel
  have hothersMass : ∑ c ∈ othersSet, design.weight c = 1 - weightP - weightQ := by
    have htotal := design.weight_sum_one
    rw [hsplit design.weight, ← hweightPDef, ← hweightQDef] at htotal
    linarith
  -- positivity of the sector data
  have hweightPPos : 0 < weightP := design.weight_pos poleP
  have hweightQPos : 0 < weightQ := design.weight_pos poleQ
  have hpoleMassPos : 0 < poleMass := by rw [hpoleMassDef]; linarith
  have hpoleMassNe : poleMass ≠ 0 := hpoleMassPos.ne'
  have haxisBlockPos : 0 < axisBlock := by
    have hone := one_lt_axisBlock_of_offPlanePair design poleP poleQ thirdLabel
      probe hunit hpoleNe hthirdP hthirdQ hplanarOthers
    rw [haxisBlockDef]
    linarith
  have hcarrierSteepPos : 0 < (design.atom carrierLabel ⬝ᵥ probe) ^ 2 - 1 := by
    linarith
  have hkappaNonneg : 0 ≤ kappa := by
    nlinarith [hkappaDef, hcarrierSteepPos, hseedPos, sq_nonneg carrierTilt]
  have hkappaOnePos : (0 : ℝ) < 1 + kappa := by linarith
  have hkappaOneNe : (1 : ℝ) + kappa ≠ 0 := hkappaOnePos.ne'
  have hinPlaneMassPos : 0 < inPlaneMass := by
    rw [hinPlaneMassDef]
    have hsecond : 0 ≤ weightQ * tiltRatio ^ 2 :=
      mul_nonneg hweightQPos.le (sq_nonneg tiltRatio)
    nlinarith [hseedPos, hweightPPos, hsecond]
  -- the companion at scale one
  set poleWeight := poleMass / 2 with hpoleWeightDef
  have hpoleWeightPos : 0 < poleWeight := by
    rw [hpoleWeightDef]; linarith
  set poleShadow := (inPlaneMass + kappa) / poleMass with hpoleShadowDef
  have hpoleShadowPos : 0 < poleShadow := by
    rw [hpoleShadowDef]
    exact div_pos (by linarith) hpoleMassPos
  set poleEntrySq := poleShadow / (1 + kappa) with hpoleEntrySqDef
  have hpoleEntrySqPos : 0 < poleEntrySq := div_pos hpoleShadowPos hkappaOnePos
  set poleEntry := Real.sqrt poleEntrySq with hpoleEntryDef
  have hpoleEntrySq : poleEntry ^ 2 = poleEntrySq :=
    Real.sq_sqrt hpoleEntrySqPos.le
  set alongScaleSq := (seedNormSq * (1 + kappa))⁻¹ with halongScaleSqDef
  set acrossScaleSq := seedNormSq⁻¹ with hacrossScaleSqDef
  have halongScaleSqPos : 0 < alongScaleSq :=
    inv_pos.mpr (mul_pos hseedPos hkappaOnePos)
  have hacrossScaleSqPos : 0 < acrossScaleSq := inv_pos.mpr hseedPos
  set alongScale := Real.sqrt alongScaleSq with halongScaleDef
  set acrossScale := Real.sqrt acrossScaleSq with hacrossScaleDef
  have halongScalePos : 0 < alongScale := Real.sqrt_pos.mpr halongScaleSqPos
  have hacrossScalePos : 0 < acrossScale := Real.sqrt_pos.mpr hacrossScaleSqPos
  have halongScaleNe : alongScale ≠ 0 := halongScalePos.ne'
  have hacrossScaleNe : acrossScale ≠ 0 := hacrossScalePos.ne'
  have halongScaleSq : alongScale ^ 2 = alongScaleSq :=
    Real.sq_sqrt halongScaleSqPos.le
  have hacrossScaleSq : acrossScale ^ 2 = acrossScaleSq :=
    Real.sq_sqrt hacrossScaleSqPos.le
  set alongCoordFn := fun c : Fin 6 => alongScale * (design.atom c ⬝ᵥ seedVec)
    with halongCoordDef
  set acrossCoordFn := fun c : Fin 6 => acrossScale * (design.atom c ⬝ᵥ crossVec)
    with hacrossCoordDef
  -- the companion's moments
  have halongSum : ∑ c ∈ othersSet, design.weight c * alongCoordFn c ^ 2
      = alongScaleSq * (seedNormSq * (1 - inPlaneMass)) := by
    have hstep : ∀ c ∈ othersSet,
        design.weight c * alongCoordFn c ^ 2
          = alongScaleSq * (design.weight c * (design.atom c ⬝ᵥ seedVec) ^ 2) := by
      intro c _
      simp only [halongCoordDef, mul_pow, halongScaleSq]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hseedMoment]
  have hacrossSum : ∑ c ∈ othersSet, design.weight c * acrossCoordFn c ^ 2
      = acrossScaleSq * seedNormSq := by
    have hstep : ∀ c ∈ othersSet,
        design.weight c * acrossCoordFn c ^ 2
          = acrossScaleSq * (design.weight c * (design.atom c ⬝ᵥ crossVec) ^ 2) := by
      intro c _
      simp only [hacrossCoordDef, mul_pow, hacrossScaleSq]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hcrossMoment]
  have hmixedSum : ∑ c ∈ othersSet,
      design.weight c * (alongCoordFn c * acrossCoordFn c) = 0 := by
    have hstep : ∀ c ∈ othersSet,
        design.weight c * (alongCoordFn c * acrossCoordFn c)
          = (alongScale * acrossScale) * (design.weight c
            * ((design.atom c ⬝ᵥ seedVec) * (design.atom c ⬝ᵥ crossVec))) := by
      intro c _
      simp only [halongCoordDef, hacrossCoordDef]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hmixedMoment, mul_zero]
  have hweightBudget : 2 * poleWeight + ∑ c ∈ othersSet, design.weight c = 1 := by
    rw [hothersMass, hpoleWeightDef, hpoleMassDef]
    ring
  have halongMoment : 2 * (poleWeight * poleEntry ^ 2)
      + ∑ c ∈ othersSet, design.weight c * alongCoordFn c ^ 2 = 1 := by
    rw [halongSum, hpoleEntrySq, hpoleEntrySqDef, hpoleShadowDef, hpoleWeightDef,
      halongScaleSqDef]
    field_simp
    ring
  have hacrossMoment : ∑ c ∈ othersSet, design.weight c * acrossCoordFn c ^ 2 = 1 := by
    rw [hacrossSum, hacrossScaleSqDef]
    field_simp
  -- the planar shadows are pairwise non-parallel
  have hatomNonzero : ∀ c : Fin 6, design.atom c ≠ 0 := by
    intro c hzero
    obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card (by simp) c
    exact hprimitive other c 0 hother (by rw [hzero, zero_smul])
  have hplanarBracket : ∀ leftLabel rightLabel : Fin 6,
      leftLabel ≠ poleP → leftLabel ≠ poleQ →
      rightLabel ≠ poleP → rightLabel ≠ poleQ → leftLabel ≠ rightLabel →
      alongCoordFn leftLabel * acrossCoordFn rightLabel
        - alongCoordFn rightLabel * acrossCoordFn leftLabel ≠ 0 := by
    intro leftLabel rightLabel hleftP hleftQ hrightP hrightQ hne
    have hframe := frameBracket_eq_seedNormSq_mul_probeTriple probe seedVec
      (design.atom leftLabel) (design.atom rightLabel) hseedPerp
    have htriple : probe ⬝ᵥ crossProduct (design.atom leftLabel)
        (design.atom rightLabel) ≠ 0 :=
      probeTriple_ne_zero_of_planarNonParallel probe (design.atom leftLabel)
        (design.atom rightLabel) hunit (hplanarOthers leftLabel hleftP hleftQ)
        (hplanarOthers rightLabel hrightP hrightQ) (hatomNonzero leftLabel)
        (fun ratio => hprimitive leftLabel rightLabel ratio hne)
    have hvalue : alongCoordFn leftLabel * acrossCoordFn rightLabel
        - alongCoordFn rightLabel * acrossCoordFn leftLabel
        = alongScale * acrossScale
          * ((seedVec ⬝ᵥ seedVec)
            * (probe ⬝ᵥ crossProduct (design.atom leftLabel)
              (design.atom rightLabel))) := by
      simp only [halongCoordDef, hacrossCoordDef]
      rw [← hframe, ← hcrossDef]
      ring
    rw [hvalue, ← hseedNormDef]
    exact mul_ne_zero (mul_ne_zero halongScaleNe hacrossScaleNe)
      (mul_ne_zero hseedNormNe htriple)
  -- the hinge on the companion
  obtain ⟨firstLabel, secondLabel, hlabelNe, hpairStrict⟩ :=
    exists_strictCompanionPair_of_moments hstrictPair alongCoordFn acrossCoordFn
      design.weight poleP poleQ poleEntry poleWeight hpoleNe hpoleWeightPos
      (fun c _ _ => design.weight_pos c) hweightBudget halongMoment hacrossMoment
      hmixedSum hplanarBracket
  set companionAtoms :=
    strictCompanionAtom alongCoordFn acrossCoordFn poleP poleQ poleEntry
    with hcompanionAtomsDef
  -- the master inequality at the scale-clearing test vector
  have hdotTwo : ∀ leftFirst leftSecond rightFirst rightSecond : ℝ,
      (![leftFirst, leftSecond] : Fin 2 → ℝ) ⬝ᵥ ![rightFirst, rightSecond]
        = leftFirst * rightFirst + leftSecond * rightSecond := by
    intro leftFirst leftSecond rightFirst rightSecond
    simp [dotProduct, Fin.sum_univ_two]
  have hatomPlanarDot : ∀ c : Fin 6, c ≠ poleP → c ≠ poleQ → ∀ alongInput acrossInput : ℝ,
      companionAtoms c ⬝ᵥ ![alongInput / alongScale, acrossInput / acrossScale]
        = (design.atom c ⬝ᵥ seedVec) * alongInput + (design.atom c ⬝ᵥ crossVec) * acrossInput := by
    intro c hcP hcQ alongInput acrossInput
    have hval : companionAtoms c = ![alongCoordFn c, acrossCoordFn c] := by
      simp only [hcompanionAtomsDef, strictCompanionAtom, if_neg hcP, if_neg hcQ]
    rw [hval, hdotTwo]
    simp only [halongCoordDef, hacrossCoordDef]
    field_simp
  have hatomPoleDot : ∀ c : Fin 6, (c = poleP ∨ c = poleQ) → ∀ alongInput acrossInput : ℝ,
      companionAtoms c ⬝ᵥ ![alongInput / alongScale, acrossInput / acrossScale]
        = poleEntry * (alongInput / alongScale) := by
    intro c hmem alongInput acrossInput
    have hval : companionAtoms c = ![poleEntry, 0] := by
      rcases hmem with hmem | hmem
      · simp [hcompanionAtomsDef, strictCompanionAtom, hmem]
      · simp [hcompanionAtomsDef, strictCompanionAtom, hmem, Ne.symm hpoleNe]
    rw [hval, hdotTwo]
    ring
  have htestNorm : ∀ alongInput acrossInput : ℝ,
      (![alongInput / alongScale, acrossInput / acrossScale] : Fin 2 → ℝ)
          ⬝ᵥ ![alongInput / alongScale, acrossInput / acrossScale]
        = (alongInput ^ 2 * (1 + kappa) + acrossInput ^ 2) * seedNormSq := by
    intro alongInput acrossInput
    rw [hdotTwo]
    have hleft : alongInput / alongScale * (alongInput / alongScale) = alongInput ^ 2 / alongScaleSq := by
      rw [div_mul_div_comm, ← sq, ← sq, halongScaleSq]
    have hright : acrossInput / acrossScale * (acrossInput / acrossScale) = acrossInput ^ 2 / acrossScaleSq := by
      rw [div_mul_div_comm, ← sq, ← sq, hacrossScaleSq]
    rw [hleft, hright, halongScaleSqDef, hacrossScaleSqDef]
    field_simp
  have htestNe : ∀ alongInput acrossInput : ℝ, 0 < alongInput ^ 2 + acrossInput ^ 2 →
      (![alongInput / alongScale, acrossInput / acrossScale] : Fin 2 → ℝ) ≠ 0 := by
    intro alongInput acrossInput hpos hzero
    have hfirst : alongInput / alongScale = 0 := by
      have := congrFun hzero 0
      simpa using this
    have hsecond : acrossInput / acrossScale = 0 := by
      have := congrFun hzero 1
      simpa using this
    have haaZero : alongInput = 0 := (div_eq_zero_iff.mp hfirst).resolve_right halongScaleNe
    have hbbZero : acrossInput = 0 := (div_eq_zero_iff.mp hsecond).resolve_right hacrossScaleNe
    rw [haaZero, hbbZero] at hpos
    norm_num at hpos
  have hmaster : ∀ alongInput acrossInput : ℝ, 0 < alongInput ^ 2 + acrossInput ^ 2 →
      (alongInput ^ 2 * (1 + kappa) + acrossInput ^ 2) * seedNormSq
        < (companionAtoms firstLabel ⬝ᵥ ![alongInput / alongScale, acrossInput / acrossScale]) ^ 2
          + (companionAtoms secondLabel
              ⬝ᵥ ![alongInput / alongScale, acrossInput / acrossScale]) ^ 2 := by
    intro alongInput acrossInput hpos
    have hbound := hpairStrict ![alongInput / alongScale, acrossInput / acrossScale] (htestNe alongInput acrossInput hpos)
    rwa [htestNorm alongInput acrossInput] at hbound
  have hshadowTerm : ∀ alongInput : ℝ,
      (poleEntry * (alongInput / alongScale)) ^ 2 = poleShadow * seedNormSq * alongInput ^ 2 := by
    intro alongInput
    rw [mul_pow, hpoleEntrySq, hpoleEntrySqDef, div_pow, halongScaleSq,
      halongScaleSqDef]
    field_simp
  have haxisBlockPosRaw : 0 < poleAxisP ^ 2 + poleAxisQ ^ 2 - 1 :=
    haxisBlockDef ▸ haxisBlockPos
  -- branch: a pole shadow paired with a planar atom
  have htwoPoleBranch : ∀ planarLabel : Fin 6, planarLabel ≠ poleP →
      planarLabel ≠ poleQ →
      (∀ alongInput acrossInput : ℝ, 0 < alongInput ^ 2 + acrossInput ^ 2 →
        (alongInput ^ 2 * (1 + kappa) + acrossInput ^ 2) * seedNormSq
          < poleShadow * seedNormSq * alongInput ^ 2
            + ((design.atom planarLabel ⬝ᵥ seedVec) * alongInput
              + (design.atom planarLabel ⬝ᵥ crossVec) * acrossInput) ^ 2) →
      ∃ dominatingTriple : Finset (Fin 6), dominatingTriple.card = 3
        ∧ (subsetSum design dominatingTriple - 1).PosDef := by
    intro planarLabel hnotP hnotQ hmixMaster
    obtain ⟨hacrossBig, hshadowGapPos, halongBound⟩ :=
      mixedPair_alongBound_of_strictMaster hseedPos hmixMaster
    have hshadowProduct : poleShadow * poleMass = inPlaneMass + kappa := by
      rw [hpoleShadowDef]
      field_simp
    have hshadowIdentity : (poleShadow - 1 - kappa) * poleMass
        = inPlaneMass + kappa - poleMass * (1 + kappa) := by
      linear_combination hshadowProduct
    have hbudgetScaled : axisBlock * (poleShadow - 1 - kappa) ≤ pairGap := by
      have hscaled : axisBlock * ((poleShadow - 1 - kappa) * poleMass)
          ≤ pairGap * poleMass := by
        rw [hshadowIdentity]; exact hbudget
      nlinarith [hscaled, hpoleMassPos]
    have hexcessPos : 0 < (design.atom planarLabel ⬝ᵥ crossVec) ^ 2 - seedNormSq := by
      linarith
    have hstepOne : axisBlock * (design.atom planarLabel ⬝ᵥ seedVec) ^ 2
        < axisBlock * ((poleShadow - 1 - kappa)
          * ((design.atom planarLabel ⬝ᵥ crossVec) ^ 2 - seedNormSq)) :=
      mul_lt_mul_of_pos_left halongBound haxisBlockPos
    have hstepTwo : axisBlock * (poleShadow - 1 - kappa)
          * ((design.atom planarLabel ⬝ᵥ crossVec) ^ 2 - seedNormSq)
        ≤ pairGap * ((design.atom planarLabel ⬝ᵥ crossVec) ^ 2 - seedNormSq) :=
      mul_le_mul_of_nonneg_right hbudgetScaled hexcessPos.le
    have hgateScalar : axisBlock * (design.atom planarLabel ⬝ᵥ seedVec) ^ 2
        < pairGap * ((design.atom planarLabel ⬝ᵥ crossVec) ^ 2 - seedNormSq) := by
      nlinarith [hstepOne, hstepTwo]
    have hpairGapPos : 0 < pairGap := by
      nlinarith [hgateScalar, haxisBlockPos, hexcessPos,
        sq_nonneg (design.atom planarLabel ⬝ᵥ seedVec)]
    rw [hpairGapDef, haxisBlockDef, hseedNormDef] at hpairGapPos hgateScalar
    refine ⟨insert poleP (insert poleQ {planarLabel}), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨hpoleNe, fun hEq => hnotP hEq.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact fun hEq => hnotQ hEq.symm),
        Finset.card_singleton]
    · exact posDef_polePair_triple_of_scalarGate design poleP poleQ planarLabel
        probe tiltRatio hunit hpoleNe hnotP hnotQ
        (hplanarOthers planarLabel hnotP hnotQ) hantiparallel hseedNe
        haxisBlockPosRaw hpairGapPos hgateScalar
  -- the returned pair, by shape
  by_cases hfirstPole : firstLabel = poleP ∨ firstLabel = poleQ
  · by_cases hsecondPole : secondLabel = poleP ∨ secondLabel = poleQ
    · exfalso
      have hzero := hmaster 0 1 (by norm_num)
      rw [hatomPoleDot firstLabel hfirstPole 0 1,
        hatomPoleDot secondLabel hsecondPole 0 1] at hzero
      have hcollapse : poleEntry * ((0 : ℝ) / alongScale) = 0 := by ring
      rw [hcollapse] at hzero
      norm_num at hzero
      linarith [hzero, hseedPos]
    · push Not at hsecondPole
      refine htwoPoleBranch secondLabel hsecondPole.1 hsecondPole.2 ?_
      intro alongInput acrossInput hpos
      have hraw := hmaster alongInput acrossInput hpos
      rw [hatomPoleDot firstLabel hfirstPole alongInput acrossInput,
        hatomPlanarDot secondLabel hsecondPole.1 hsecondPole.2 alongInput acrossInput] at hraw
      linarith [hraw, hshadowTerm alongInput]
  · push Not at hfirstPole
    by_cases hsecondPole : secondLabel = poleP ∨ secondLabel = poleQ
    · refine htwoPoleBranch firstLabel hfirstPole.1 hfirstPole.2 ?_
      intro alongInput acrossInput hpos
      have hraw := hmaster alongInput acrossInput hpos
      rw [hatomPoleDot secondLabel hsecondPole alongInput acrossInput,
        hatomPlanarDot firstLabel hfirstPole.1 hfirstPole.2 alongInput acrossInput] at hraw
      linarith [hraw, hshadowTerm alongInput]
    · push Not at hsecondPole
      obtain ⟨hfirstNotP, hfirstNotQ⟩ := hfirstPole
      obtain ⟨hsecondNotP, hsecondNotQ⟩ := hsecondPole
      have hcarrierNotMem :
          carrierLabel ∉ ({firstLabel, secondLabel} : Finset (Fin 6)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        rcases hcarrierPole with hmem | hmem
        · exact ⟨fun hEq => hfirstNotP (hmem ▸ hEq.symm),
            fun hEq => hsecondNotP (hmem ▸ hEq.symm)⟩
        · exact ⟨fun hEq => hfirstNotQ (hmem ▸ hEq.symm),
            fun hEq => hsecondNotQ (hmem ▸ hEq.symm)⟩
      refine ⟨insert carrierLabel {firstLabel, secondLabel}, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hcarrierNotMem, Finset.card_pair hlabelNe]
      · refine posDef_insert_carrier_of_planarTargetStrict design
          {firstLabel, secondLabel} carrierLabel probe hunit hcarrierNotMem ?_
          hcarrierSteep ?_
        · intro c hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact hplanarOthers _ hfirstNotP hfirstNotQ
          · exact hplanarOthers _ hsecondNotP hsecondNotQ
        · intro inPlaneVec hperp hnonzero
          set alongTest := (inPlaneVec ⬝ᵥ seedVec) / seedNormSq with halongTestDef
          set acrossTest := (inPlaneVec ⬝ᵥ crossVec) / seedNormSq with hacrossTestDef
          have hexpandOf : ∀ c : Fin 6, design.atom c ⬝ᵥ probe = 0 →
              (design.atom c ⬝ᵥ seedVec) * alongTest
                + (design.atom c ⬝ᵥ crossVec) * acrossTest
              = design.atom c ⬝ᵥ inPlaneVec := by
            intro c hplanar
            have hexp := planarBasis_bilinear_expansion probe seedVec
              (design.atom c) inPlaneVec hunit hseedPlanar
            rw [hplanar, hperp] at hexp
            have hkey : (design.atom c ⬝ᵥ seedVec) * (inPlaneVec ⬝ᵥ seedVec)
                + (design.atom c ⬝ᵥ crossVec) * (inPlaneVec ⬝ᵥ crossVec)
                = seedNormSq * (design.atom c ⬝ᵥ inPlaneVec) := by
              rw [hseedNormDef]
              linear_combination hexp
            rw [halongTestDef, hacrossTestDef]
            field_simp
            linear_combination hkey
          have hnormTest : alongTest ^ 2 + acrossTest ^ 2
              = (inPlaneVec ⬝ᵥ inPlaneVec) / seedNormSq := by
            have hexp := planarBasis_bilinear_expansion probe seedVec
              inPlaneVec inPlaneVec hunit hseedPlanar
            rw [hperp] at hexp
            have hkey : (inPlaneVec ⬝ᵥ seedVec) ^ 2 + (inPlaneVec ⬝ᵥ crossVec) ^ 2
                = seedNormSq * (inPlaneVec ⬝ᵥ inPlaneVec) := by
              rw [hseedNormDef]
              linear_combination hexp
            rw [halongTestDef, hacrossTestDef]
            field_simp
            linear_combination hkey
          have hnormPos : 0 < inPlaneVec ⬝ᵥ inPlaneVec :=
            dotProduct_self_pos hnonzero
          have htestNonzero : 0 < alongTest ^ 2 + acrossTest ^ 2 := by
            rw [hnormTest]
            exact div_pos hnormPos hseedPos
          have hcarrierDot : design.atom carrierLabel ⬝ᵥ inPlaneVec
              = carrierTilt * (alongTest * seedNormSq) := by
            have hdecomp : design.atom carrierLabel
                = carrierTilt • seedVec
                  + (design.atom carrierLabel ⬝ᵥ probe) • probe :=
              sub_eq_iff_eq_add.mp hcarrierPart
            rw [hdecomp, add_dotProduct, smul_dotProduct, smul_dotProduct,
              smul_eq_mul, smul_eq_mul, dotProduct_comm probe inPlaneVec, hperp,
              dotProduct_comm seedVec inPlaneVec, halongTestDef]
            field_simp
            ring
          have hpairMaster :
              (alongTest ^ 2 * (1 + kappa) + acrossTest ^ 2) * seedNormSq
                < ((design.atom firstLabel ⬝ᵥ seedVec) * alongTest
                      + (design.atom firstLabel ⬝ᵥ crossVec) * acrossTest) ^ 2
                  + ((design.atom secondLabel ⬝ᵥ seedVec) * alongTest
                      + (design.atom secondLabel ⬝ᵥ crossVec) * acrossTest) ^ 2 := by
            have hraw := hmaster alongTest acrossTest htestNonzero
            rwa [hatomPlanarDot firstLabel hfirstNotP hfirstNotQ alongTest acrossTest,
              hatomPlanarDot secondLabel hsecondNotP hsecondNotQ alongTest acrossTest]
              at hraw
          have hstrict := planarPair_strictTarget_of_strictMaster
            (seedNormSq := seedNormSq) (kappa := kappa)
            (carrierTiltSq := carrierTilt ^ 2)
            (carrierAxisSq := (design.atom carrierLabel ⬝ᵥ probe) ^ 2)
            (alongCoordFirst := design.atom firstLabel ⬝ᵥ seedVec)
            (alongCoordSecond := design.atom secondLabel ⬝ᵥ seedVec)
            (acrossCoordFirst := design.atom firstLabel ⬝ᵥ crossVec)
            (acrossCoordSecond := design.atom secondLabel ⬝ᵥ crossVec)
            (alongTest := alongTest) (acrossTest := acrossTest)
            hcarrierSteep hkappaDef hpairMaster
          rw [hexpandOf firstLabel (hplanarOthers _ hfirstNotP hfirstNotQ),
            hexpandOf secondLabel (hplanarOthers _ hsecondNotP hsecondNotQ)]
            at hstrict
          have hnormProduct : seedNormSq * (alongTest ^ 2 + acrossTest ^ 2)
              = inPlaneVec ⬝ᵥ inPlaneVec := by
            rw [hnormTest]
            field_simp
          have hcarrierSq : (design.atom carrierLabel ⬝ᵥ inPlaneVec) ^ 2
              = carrierTilt ^ 2 * alongTest ^ 2 * seedNormSq ^ 2 := by
            rw [hcarrierDot]; ring
          rw [Finset.sum_pair hlabelNe, hcarrierSq, ← hnormProduct]
          exact hstrict

/-! ## Companion Part D: the handoff, discharged

Everything above is assembled by one `le_total` on the crossing comparison of the
two steepness masses.  Whichever way it falls, the pole it selects is steep (its
mass carries the whole planar mass on the favourable side) and its carrier budget
is payable, so the transport applies.  No configuration is left over: the
crossing locus itself is covered, because the budget is needed only NON-STRICTLY
and the identity of Part A is an equality exactly there. -/

set_option maxHeartbeats 2000000 in
/-- **THE HANDOFF, DISCHARGED.**  `StrictCompanionPairClosesTwoPoleSixThree` is a
theorem: a rank-two four-direction strict pair closes the whole two-pole
substratum of branch (iii), with no residual region whatsoever.  The gate-average
hypothesis `TwoPoleStratumSelection` carries is not used — the conclusion holds on
the gate-average region too. -/
theorem strictCompanionPairClosesTwoPoleSixThree_holds :
    StrictCompanionPairClosesTwoPoleSixThree := by
  classical
  intro hstrictPair design probe tiltRatio hunit poleP poleQ hpoleNe hplanarOthers
    hoffP hoffQ hprimitive hantiparallel _hgateAverage
  have hprobeNe : probe ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  obtain ⟨thirdLabel, hthirdP, hthirdQ⟩ : ∃ t : Fin 6, t ≠ poleP ∧ t ≠ poleQ := by
    by_contra hnone
    push Not at hnone
    have hcover : (Finset.univ : Finset (Fin 6)) ⊆ {poleP, poleQ} := by
      intro c _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hcP : c = poleP
      · exact Or.inl hcP
      · exact Or.inr (hnone c hcP)
    have hcount := Finset.card_le_card hcover
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hpoleNe] at hcount
    omega
  have hseedNe : design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe ≠ 0 :=
    seed_ne_zero_of_offPlanePair_of_isPrimitive design hprimitive poleP poleQ
      hpoleNe probe hprobeNe hplanarOthers hoffP hoffQ
  have hseedPos : 0 < (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
      ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe) :=
    dotProduct_self_pos hseedNe
  have hparsevalAxis : design.weight poleP * (design.atom poleP ⬝ᵥ probe) ^ 2
      + design.weight poleQ * (design.atom poleQ ⬝ᵥ probe) ^ 2 = 1 := by
    have hnormal := offPlanePair_normalSquare_eq design poleP poleQ hpoleNe
      (normalVec := probe) hplanarOthers
    rwa [hunit] at hnormal
  have hmixedParseval : design.weight poleP * (design.atom poleP ⬝ᵥ probe)
      + design.weight poleQ * (design.atom poleQ ⬝ᵥ probe) * tiltRatio = 0 :=
    mixedParseval_of_offPlanePair design poleP poleQ probe tiltRatio hunit hpoleNe
      hplanarOthers hantiparallel hseedNe
  have hplanarMassPos : 0 < 1 - design.weight poleP - design.weight poleQ := by
    have hmassLt := twoPole_weight_sum_lt_one design poleP poleQ thirdLabel hpoleNe
      hthirdP hthirdQ
    linarith
  rcases le_total ((1 - design.weight poleP)
      * (design.weight poleQ * ((design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)))
      ((1 - design.weight poleQ)
        * (design.weight poleP * ((design.atom poleP ⬝ᵥ probe) ^ 2 - 1)))
    with hcrossing | hcrossing
  · -- the first pole carries the favourable side of the crossing
    have hsteepP : 1 < (design.atom poleP ⬝ᵥ probe) ^ 2 :=
      one_lt_axisFirstSq_of_crossing (design.weight_pos poleP)
        (design.weight_pos poleQ) hplanarMassPos hparsevalAxis hcrossing
    have hsteepPne : (design.atom poleP ⬝ᵥ probe) ^ 2 - 1 ≠ 0 := by
      intro hzero; linarith
    have hkappa : ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
            ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
          / ((design.atom poleP ⬝ᵥ probe) ^ 2 - 1)
          * ((design.atom poleP ⬝ᵥ probe) ^ 2 - 1)
        = (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
          ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe) := by
      field_simp
    obtain ⟨_, hbudget⟩ := carrierBudget_of_crossing_poleFirst
      (design.weight_pos poleP) (design.weight_pos poleQ) hplanarMassPos hseedPos
      hoffQ hparsevalAxis hmixedParseval hcrossing hkappa
    exact exists_posDef_triple_of_strictCompanion hstrictPair design poleP poleQ
      thirdLabel poleP probe tiltRatio 1
      (((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
          ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
        / ((design.atom poleP ⬝ᵥ probe) ^ 2 - 1))
      _ _ _ _ _ hunit hpoleNe hthirdP hthirdQ hplanarOthers hprimitive
      hantiparallel hseedNe rfl rfl rfl rfl rfl (Or.inl rfl) (one_smul ℝ _).symm
      hsteepP (by rw [one_pow, one_mul]; exact hkappa) hbudget
  · -- the second pole carries it instead
    have hsteepQ : 1 < (design.atom poleQ ⬝ᵥ probe) ^ 2 :=
      one_lt_axisSecondSq_of_crossing (design.weight_pos poleP)
        (design.weight_pos poleQ) hplanarMassPos hparsevalAxis hcrossing
    have hsteepQne : (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1 ≠ 0 := by
      intro hzero; linarith
    have hkappa : tiltRatio ^ 2
            * ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
              ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
          / ((design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
          * ((design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
        = tiltRatio ^ 2
          * ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
            ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)) := by
      field_simp
    obtain ⟨_, hbudget⟩ := carrierBudget_of_crossing_poleSecond
      (design.weight_pos poleP) (design.weight_pos poleQ) hplanarMassPos hseedPos
      hoffQ hparsevalAxis hmixedParseval hcrossing hkappa
    exact exists_posDef_triple_of_strictCompanion hstrictPair design poleP poleQ
      thirdLabel poleQ probe tiltRatio tiltRatio
      (tiltRatio ^ 2
          * ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
            ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
        / ((design.atom poleQ ⬝ᵥ probe) ^ 2 - 1))
      _ _ _ _ _ hunit hpoleNe hthirdP hthirdQ hplanarOthers hprimitive
      hantiparallel hseedNe rfl rfl rfl rfl rfl (Or.inr rfl) hantiparallel
      hsteepQ hkappa hbudget

/-- **Branch (iii)'s selection residual follows from the rank-two hinge alone.**
Composing the discharged handoff with the landed
`twoPoleStratumSelection_of_hinge_of_handoff`. -/
theorem twoPoleStratumSelection_six_of_hinge (hhinge : RankTwoFourDirectionHinge) :
    TwoPoleStratumSelection 6 :=
  twoPoleStratumSelection_of_hinge_of_handoff hhinge
    strictCompanionPairClosesTwoPoleSixThree_holds

/-- **BRANCH (iii), from the rank-two hinge alone.**  A `(6,3)` tie carrying a
coplanar-support stress has a parallel pair — the landed capstone
`sixThree_hasParallelPair_of_isTie_of_coplanarStress` with its named selection
residual now supplied. -/
theorem sixThree_hasParallelPair_of_isTie_of_coplanarStress_of_hinge
    (hhinge : RankTwoFourDirectionHinge)
    (design : WeightedDesign 6 3) (htie : IsTie design)
    {stressCoeff : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    (hstressNonzero : stressCoeff ≠ 0) (hprobeNe : probe ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hcoplanar : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) :
    HasParallelPair design :=
  sixThree_hasParallelPair_of_isTie_of_coplanarStress
    (twoPoleStratumSelection_six_of_hinge hhinge) design htie hstressNonzero
    hprobeNe hstress hcoplanar

/-! ## The chain, closed

Both halves are now in one translation unit, so the composition carries no
hypothesis. -/

/-- **`TwoPoleStratumSelection 6` IS A THEOREM.**  The landed capstone's named
selection residual, discharged: the rank-two four-direction hinge is proved
above, and the scale-one companion turns its strict pair into a strictly
dominating triple of the original `(6,3)` design. -/
theorem twoPoleStratumSelection_six_unconditional : TwoPoleStratumSelection 6 :=
  twoPoleStratumSelection_six_of_hinge rankTwoFourDirectionHinge_holds

/-- **BRANCH (iii) OF THE `(6,3)` STRESS TRICHOTOMY, UNCONDITIONALLY.**  A `(6,3)`
tie carrying a coplanar-support stress has a parallel pair. -/
theorem sixThree_hasParallelPair_of_isTie_of_coplanarStress_unconditional
    (design : WeightedDesign 6 3) (htie : IsTie design)
    {stressCoeff : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    (hstressNonzero : stressCoeff ≠ 0) (hprobeNe : probe ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hcoplanar : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) :
    HasParallelPair design :=
  sixThree_hasParallelPair_of_isTie_of_coplanarStress
    twoPoleStratumSelection_six_unconditional design htie hstressNonzero hprobeNe
    hstress hcoplanar


end Gtz
