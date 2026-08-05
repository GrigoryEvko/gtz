/-
# Branch (iii), the two-pole substratum: strict reductions and the capstone

The stress trichotomy's branch (iii) hands a `(6,3)` design a nonzero stress
whose supported atoms annihilate a common nonzero probe.  For a primitive
design that plane holds all but one or two atoms
(`Gtz/Reduction/CoplanarStress.lean`); `Gtz.not_isTie_of_soleOffPlane` kills
the one-off-plane case, and at a TIE `Gtz.two_le_card_offPlane_of_isTie` kills
it again from the other side.  So the branch narrows to EXACTLY TWO off-plane
poles over a coplanar four-atom family.

This file supplies the two-pole machinery, all strict (PosDef, not just
PosSemidef, because refuting a tie needs a strictly dominating triple):

* `posDef_insert_carrier_of_planarTargetStrict` — the STRICT carrier
  reduction: one steep pole plus planar atoms beating the tilted in-plane
  target strictly is a positive-definite triple, by the same
  completing-the-square as the PosSemidef version with strictness carried.
* `polePairClearedForm_pos` — the scalar core of the TWO-POLE reduction: the
  cleared quadratic form of the triple {both poles, one planar atom} is
  positive definite exactly under the scalar gate
  `E0 > 0  and  E0 (Y^2 - L2) > W X^2`, where `E0` is the determinant of the
  pole pair's `(seed, axis)`-block gap and `W` its axis entry.  Cross-checked
  against direct Sylvester on 173,924 exact rational instances before
  transcription.
* `posDef_polePair_triple_of_scalarGate` — the design-level assembly of that
  gate: an in-plane atom passing the gate completes the two poles to a
  positive-definite triple.
* `exists_planarAtom_gate_of_gateAverage` / CELL2 — averaging the gate over
  the planar family against in-plane Parseval: when
  `E0 (1 - S) > W (1 - nu)` some planar atom passes the gate, so the
  two-pole triple exists with no selection cleverness.
* `sixThree_offPlaneFilter_card_le_two_of_coplanarStress` — the primitive
  stratum bound (two off-plane atoms at most), re-proved here from the landed
  taxonomy so this file is self-contained over the tree.
* `SixThreeTwoPoleSelection` + the capstone
  `sixThree_tie_coplanarStress_hasParallelPair_of_selection` — every `(6,3)`
  tie carrying a coplanar stress has a parallel pair, MODULO the named
  selection residual on the two-pole stratum.  Numeric status: 13,104 exact
  Parseval-exact configurations, ZERO without a strict triple (CELL2 covers
  2,154, the max-bracket rule 10,861 of the 10,950 remaining, a per-atom gate
  the rest).  Both triple shapes are needed.  The surviving rule mentions the
  bracket because a single master inequality over the pole sector is FALSE:
  12,589 violations in 29,381 exact sector points.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Reduction.Reductions
import Gtz.Reduction.StressSupportTaxonomy
import Gtz.Reduction.HingeFunnel
import Gtz.Design.StratumTieFreeClasses
import Gtz.Design.StratumEmptinessLedger
import Gtz.Quantitative.CriticalQuadric
import Gtz.Certificates.ResidueDissolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 0: scalar cores -/

/-- **The strict completing-the-square payoff.**  The strict planar gap bound
turns into a strict moment floor at every axis coordinate: the deficit is the
perfect square `((alpha^2 - 1) xi + alpha beta)^2` plus the strict gap. -/
theorem momentFloorStrict_of_scaledGapStrict
    {alpha beta xi planarMoment planarNormSq : ℝ}
    (hsteep : 1 < alpha ^ 2)
    (hgap : beta ^ 2 < (alpha ^ 2 - 1) * (planarMoment - planarNormSq)) :
    planarNormSq + xi ^ 2 < (beta + xi * alpha) ^ 2 + planarMoment := by
  have hpos : 0 < alpha ^ 2 - 1 := by linarith
  nlinarith [sq_nonneg ((alpha ^ 2 - 1) * xi + alpha * beta), hgap, hpos]

/-! ## Part 1: the in-plane frame from a cross product

The bilinear expansion is the resolution of the identity in the unnormalized
`(seed, crossProduct probe seed)` frame of the probe's plane. -/

/-- The cross product is orthogonal to its first factor. -/
theorem planarCross_probe_dot (probe seed : Fin 3 → ℝ) :
    probe ⬝ᵥ crossProduct probe seed = 0 := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The cross product is orthogonal to its second factor. -/
theorem planarCross_seed_dot (probe seed : Fin 3 → ℝ) :
    seed ⬝ᵥ crossProduct probe seed = 0 := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- Lagrange's identity for the cross product, unconditionally. -/
theorem planarCross_self_dot (probe seed : Fin 3 → ℝ) :
    crossProduct probe seed ⬝ᵥ crossProduct probe seed
      = (probe ⬝ᵥ probe) * (seed ⬝ᵥ seed) - (probe ⬝ᵥ seed) ^ 2 := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The bilinear completeness identity.**  For a unit probe and an in-plane
seed, projecting onto the (unnormalized) seed and cross-product directions
recovers the in-plane part of any bilinear pairing, scaled by the seed's
squared length. -/
theorem planarBasis_bilinear_expansion (probe seed x y : Fin 3 → ℝ)
    (hunit : probe ⬝ᵥ probe = 1) (hseedPlanar : probe ⬝ᵥ seed = 0) :
    (x ⬝ᵥ seed) * (y ⬝ᵥ seed)
      + (x ⬝ᵥ crossProduct probe seed) * (y ⬝ᵥ crossProduct probe seed)
      = (seed ⬝ᵥ seed) * (x ⬝ᵥ y - (x ⬝ᵥ probe) * (y ⬝ᵥ probe)) := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    at hunit hseedPlanar ⊢
  linear_combination
    ((x 0 * probe 0 + x 1 * probe 1 + x 2 * probe 2)
        * (y 0 * seed 0 + y 1 * seed 1 + y 2 * seed 2)
      + (x 0 * seed 0 + x 1 * seed 1 + x 2 * seed 2)
        * (y 0 * probe 0 + y 1 * probe 1 + y 2 * probe 2)
      - (probe 0 * seed 0 + probe 1 * seed 1 + probe 2 * seed 2)
        * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2)) * hseedPlanar
    + ((seed 0 * seed 0 + seed 1 * seed 1 + seed 2 * seed 2)
        * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2)
      - (x 0 * seed 0 + x 1 * seed 1 + x 2 * seed 2)
        * (y 0 * seed 0 + y 1 * seed 1 + y 2 * seed 2)) * hunit

/-! ## Part 2: the strict carrier reduction -/

/-- **A steep carrier over a strictly winning planar family is a
positive-definite subset.**  The strict analogue of the PosSemidef carrier
reduction: if every nonzero in-plane direction beats the tilted target
STRICTLY, the whole gap matrix of `insert carrier selected` is positive
definite.  The completing-the-square is `momentFloorStrict_of_scaledGapStrict`;
the pure-axis direction is paid by steepness alone. -/
theorem posDef_insert_carrier_of_planarTargetStrict
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (carrierLabel : Fin size) (probe : Fin rank → ℝ)
    (hunit : probe ⬝ᵥ probe = 1)
    (hcarrierFree : carrierLabel ∉ selected)
    (hplanarSelected : ∀ c ∈ selected, design.atom c ⬝ᵥ probe = 0)
    (hsteep : 1 < (design.atom carrierLabel ⬝ᵥ probe) ^ 2)
    (htarget : ∀ inPlaneVec : Fin rank → ℝ, inPlaneVec ⬝ᵥ probe = 0 →
        inPlaneVec ≠ 0 →
        (design.atom carrierLabel ⬝ᵥ inPlaneVec) ^ 2
          < ((design.atom carrierLabel ⬝ᵥ probe) ^ 2 - 1)
            * (∑ c ∈ selected, (design.atom c ⬝ᵥ inPlaneVec) ^ 2
                - inPlaneVec ⬝ᵥ inPlaneVec)) :
    (subsetSum design (insert carrierLabel selected) - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one design _),
      fun testVec htestNe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum,
    Matrix.one_mulVec, Finset.sum_insert hcarrierFree]
  simp only [momentCoord]
  set alpha := design.atom carrierLabel ⬝ᵥ probe with halphaDef
  set axisCoord := testVec ⬝ᵥ probe with haxisDef
  set inPlaneVec : Fin rank → ℝ := testVec - axisCoord • probe with hplanarDef
  have hplanarPerp : inPlaneVec ⬝ᵥ probe = 0 := by
    simp only [hplanarDef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit,
      ← haxisDef]
    ring
  have hpairSplit : ∀ label : Fin size,
      design.atom label ⬝ᵥ testVec
        = design.atom label ⬝ᵥ inPlaneVec
          + axisCoord * (design.atom label ⬝ᵥ probe) := by
    intro label
    simp only [hplanarDef, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  have hselectedAtTest : ∑ c ∈ selected, (design.atom c ⬝ᵥ testVec) ^ 2
      = ∑ c ∈ selected, (design.atom c ⬝ᵥ inPlaneVec) ^ 2 := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hpairSplit c, hplanarSelected c hc]
    ring
  have hprobeAtTest : probe ⬝ᵥ testVec = axisCoord := by
    rw [dotProduct_comm]
  have hnormSplit : testVec ⬝ᵥ testVec
      = inPlaneVec ⬝ᵥ inPlaneVec + axisCoord ^ 2 := by
    simp only [hplanarDef, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hunit, ← haxisDef, hprobeAtTest]
    ring
  have hcarrierAtTest : design.atom carrierLabel ⬝ᵥ testVec
      = design.atom carrierLabel ⬝ᵥ inPlaneVec + axisCoord * alpha :=
    hpairSplit carrierLabel
  rw [hcarrierAtTest, hselectedAtTest, hnormSplit]
  by_cases hplanarZero : inPlaneVec = 0
  · have haxisNe : axisCoord ≠ 0 := by
      intro haxisZero
      apply htestNe
      have hrebuild : testVec = inPlaneVec + axisCoord • probe := by
        rw [hplanarDef]; abel
      rw [hrebuild, hplanarZero, haxisZero, zero_smul, add_zero]
    have hcarrierPlanarZero : design.atom carrierLabel ⬝ᵥ inPlaneVec = 0 := by
      rw [hplanarZero, dotProduct_zero]
    have hselectedZero : ∑ c ∈ selected, (design.atom c ⬝ᵥ inPlaneVec) ^ 2
        = 0 := by
      rw [hplanarZero]
      exact Finset.sum_eq_zero fun c _ => by rw [dotProduct_zero]; ring
    have hplanarNormZero : inPlaneVec ⬝ᵥ inPlaneVec = 0 := by
      rw [hplanarZero, dotProduct_zero]
    rw [hcarrierPlanarZero, hselectedZero, hplanarNormZero]
    have haxisSqPos : 0 < axisCoord ^ 2 := by positivity
    nlinarith [hsteep, haxisSqPos]
  · have hgap := htarget inPlaneVec hplanarPerp hplanarZero
    have hfloor := momentFloorStrict_of_scaledGapStrict
      (planarMoment := ∑ c ∈ selected, (design.atom c ⬝ᵥ inPlaneVec) ^ 2)
      (planarNormSq := inPlaneVec ⬝ᵥ inPlaneVec)
      (xi := axisCoord) hsteep hgap
    linarith

/-! ## Part 3: the two-pole scalar core

The triple `{poleP, poleQ, planar atom}` against a unit probe, written in the
unnormalized `(seed, cross, probe)` frame with `seed` the in-plane part of
`poleP` and the in-plane part of `poleQ` equal to `tiltRatio • seed`, has the
cleared quadratic form below (the gap form scaled by `seedNormSq ^ 2`).  Its
positive definiteness is EXACTLY the scalar gate `0 < pairGap` together with
`axisBlock * atomAlong ^ 2 < pairGap * (atomAcross ^ 2 - seedNormSq)`; this
file needs only the sufficient direction.  The equivalence was cross-checked
against direct Sylvester minors on 173,924 exact rational instances before
transcription. -/

/-- **The seed-cross residual block is positive under the gate slack.**  The
leading coefficient is the Schur residual `seedNormSq * pairGap +
axisBlock * atomAlong ^ 2`; scaling by it turns the block into a perfect
square plus the gate slack times the cross coordinate squared. -/
theorem polePairSubform_pos
    {seedNormSq pairGap axisBlock atomAlong atomAcross : ℝ}
    {testAlong testAcross : ℝ}
    (hseedPos : 0 < seedNormSq) (haxisPos : 0 < axisBlock)
    (hgapPos : 0 < pairGap)
    (hslack : axisBlock * atomAlong ^ 2
      < pairGap * (atomAcross ^ 2 - seedNormSq))
    (hnontrivial : testAlong ≠ 0 ∨ testAcross ≠ 0) :
    0 < (seedNormSq * pairGap + axisBlock * atomAlong ^ 2) * testAlong ^ 2
        + 2 * axisBlock * atomAlong * atomAcross * testAlong * testAcross
        + axisBlock * (atomAcross ^ 2 - seedNormSq) * testAcross ^ 2 := by
  have hresidualPos : 0 < seedNormSq * pairGap + axisBlock * atomAlong ^ 2 := by
    have hfirst : 0 < seedNormSq * pairGap := mul_pos hseedPos hgapPos
    nlinarith [mul_nonneg haxisPos.le (sq_nonneg atomAlong)]
  have hkey : (seedNormSq * pairGap + axisBlock * atomAlong ^ 2)
        * ((seedNormSq * pairGap + axisBlock * atomAlong ^ 2) * testAlong ^ 2
            + 2 * axisBlock * atomAlong * atomAcross * testAlong * testAcross
            + axisBlock * (atomAcross ^ 2 - seedNormSq) * testAcross ^ 2)
      = ((seedNormSq * pairGap + axisBlock * atomAlong ^ 2) * testAlong
            + axisBlock * atomAlong * atomAcross * testAcross) ^ 2
        + axisBlock * seedNormSq
            * (pairGap * (atomAcross ^ 2 - seedNormSq)
                - axisBlock * atomAlong ^ 2) * testAcross ^ 2 := by
    ring
  by_cases hacrossZero : testAcross = 0
  · have halongNe : testAlong ≠ 0 := by
      rcases hnontrivial with halong | hacross
      · exact halong
      · exact absurd hacrossZero hacross
    have hcollapse : (seedNormSq * pairGap + axisBlock * atomAlong ^ 2)
          * testAlong ^ 2
          + 2 * axisBlock * atomAlong * atomAcross * testAlong * testAcross
          + axisBlock * (atomAcross ^ 2 - seedNormSq) * testAcross ^ 2
        = (seedNormSq * pairGap + axisBlock * atomAlong ^ 2)
          * testAlong ^ 2 := by
      rw [hacrossZero]
      ring
    rw [hcollapse]
    have halongSqPos : 0 < testAlong ^ 2 := by positivity
    exact mul_pos hresidualPos halongSqPos
  · have hacrossSqPos : 0 < testAcross ^ 2 := by positivity
    have hslackTermPos : 0 < axisBlock * seedNormSq
        * (pairGap * (atomAcross ^ 2 - seedNormSq)
            - axisBlock * atomAlong ^ 2) * testAcross ^ 2 := by
      have hcoeff : 0 < axisBlock * seedNormSq
          * (pairGap * (atomAcross ^ 2 - seedNormSq)
              - axisBlock * atomAlong ^ 2) := by
        have hslackPos : 0 < pairGap * (atomAcross ^ 2 - seedNormSq)
            - axisBlock * atomAlong ^ 2 := by linarith
        exact mul_pos (mul_pos haxisPos hseedPos) hslackPos
      exact mul_pos hcoeff hacrossSqPos
    have hscaledPos : 0 < (seedNormSq * pairGap + axisBlock * atomAlong ^ 2)
        * ((seedNormSq * pairGap + axisBlock * atomAlong ^ 2) * testAlong ^ 2
            + 2 * axisBlock * atomAlong * atomAcross * testAlong * testAcross
            + axisBlock * (atomAcross ^ 2 - seedNormSq) * testAcross ^ 2) := by
      rw [hkey]
      nlinarith [hslackTermPos,
        sq_nonneg ((seedNormSq * pairGap + axisBlock * atomAlong ^ 2) * testAlong
          + axisBlock * atomAlong * atomAcross * testAcross)]
    by_contra hnotPos
    push Not at hnotPos
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hresidualPos.le hnotPos,
      hscaledPos]

set_option maxHeartbeats 1600000 in
/-- **The cleared two-pole form is positive under the scalar gate.**  Schur
step one peels the probe-axis square off the cleared form; the seed-cross
residual is `polePairSubform_pos`. -/
theorem polePairClearedForm_pos
    {seedNormSq tiltRatio poleAxisP poleAxisQ atomAlong atomAcross : ℝ}
    {testAlong testAcross testAxis : ℝ}
    (hseedPos : 0 < seedNormSq)
    (haxisBlockPos : 0 < poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
    (hpairGapPos : 0 <
      (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
          * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
        - seedNormSq * (poleAxisP + tiltRatio * poleAxisQ) ^ 2)
    (hscalarGate :
      (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1) * atomAlong ^ 2
        < ((poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
              * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
            - seedNormSq * (poleAxisP + tiltRatio * poleAxisQ) ^ 2)
          * (atomAcross ^ 2 - seedNormSq))
    (hnontrivial : ¬ (testAlong = 0 ∧ testAcross = 0 ∧ testAxis = 0)) :
    0 < seedNormSq ^ 2 * (testAlong + poleAxisP * testAxis) ^ 2
        + seedNormSq ^ 2 * (tiltRatio * testAlong + poleAxisQ * testAxis) ^ 2
        + (atomAlong * testAlong + atomAcross * testAcross) ^ 2
        - seedNormSq * (testAlong ^ 2 + testAcross ^ 2)
        - seedNormSq ^ 2 * testAxis ^ 2 := by
  by_cases hplanarZero : testAlong = 0 ∧ testAcross = 0
  · obtain ⟨halongZero, hacrossZero⟩ := hplanarZero
    have haxisNe : testAxis ≠ 0 := fun haxisZero =>
      hnontrivial ⟨halongZero, hacrossZero, haxisZero⟩
    subst halongZero hacrossZero
    have hcollapse : seedNormSq ^ 2 * ((0 : ℝ) + poleAxisP * testAxis) ^ 2
          + seedNormSq ^ 2 * (tiltRatio * 0 + poleAxisQ * testAxis) ^ 2
          + (atomAlong * 0 + atomAcross * 0) ^ 2
          - seedNormSq * ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2)
          - seedNormSq ^ 2 * testAxis ^ 2
        = seedNormSq ^ 2 * testAxis ^ 2
          * (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1) := by
      ring
    rw [hcollapse]
    have haxisSqPos : 0 < testAxis ^ 2 := by positivity
    positivity
  · have hnontrivialPlanar : testAlong ≠ 0 ∨ testAcross ≠ 0 := by
      by_contra hneither
      push Not at hneither
      exact hplanarZero ⟨hneither.1, hneither.2⟩
    have hsubPos := polePairSubform_pos (seedNormSq := seedNormSq)
      (pairGap := (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
          * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
        - seedNormSq * (poleAxisP + tiltRatio * poleAxisQ) ^ 2)
      (axisBlock := poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
      (atomAlong := atomAlong) (atomAcross := atomAcross)
      (testAlong := testAlong) (testAcross := testAcross)
      hseedPos haxisBlockPos hpairGapPos hscalarGate hnontrivialPlanar
    -- Schur step one, as a polynomial identity
    have hschurOne : (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
          * (seedNormSq ^ 2 * (testAlong + poleAxisP * testAxis) ^ 2
              + seedNormSq ^ 2
                  * (tiltRatio * testAlong + poleAxisQ * testAxis) ^ 2
              + (atomAlong * testAlong + atomAcross * testAcross) ^ 2
              - seedNormSq * (testAlong ^ 2 + testAcross ^ 2)
              - seedNormSq ^ 2 * testAxis ^ 2)
        = seedNormSq ^ 2
            * ((poleAxisP ^ 2 + poleAxisQ ^ 2 - 1) * testAxis
                + (poleAxisP + tiltRatio * poleAxisQ) * testAlong) ^ 2
          + (seedNormSq
                * ((poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
                      * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
                    - seedNormSq * (poleAxisP + tiltRatio * poleAxisQ) ^ 2)
              + (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1) * atomAlong ^ 2)
              * testAlong ^ 2
          + 2 * (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
              * atomAlong * atomAcross * testAlong * testAcross
          + (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
              * (atomAcross ^ 2 - seedNormSq) * testAcross ^ 2 := by
      ring
    have hscaledPos : 0 < (poleAxisP ^ 2 + poleAxisQ ^ 2 - 1)
        * (seedNormSq ^ 2 * (testAlong + poleAxisP * testAxis) ^ 2
            + seedNormSq ^ 2
                * (tiltRatio * testAlong + poleAxisQ * testAxis) ^ 2
            + (atomAlong * testAlong + atomAcross * testAcross) ^ 2
            - seedNormSq * (testAlong ^ 2 + testAcross ^ 2)
            - seedNormSq ^ 2 * testAxis ^ 2) := by
      rw [hschurOne]
      nlinarith [hsubPos,
        sq_nonneg ((poleAxisP ^ 2 + poleAxisQ ^ 2 - 1) * testAxis
          + (poleAxisP + tiltRatio * poleAxisQ) * testAlong),
        sq_nonneg seedNormSq]
    by_contra hnotPos
    push Not at hnotPos
    nlinarith [mul_nonpos_of_nonneg_of_nonpos haxisBlockPos.le hnotPos,
      hscaledPos]

/-! ## Part 4: the design-level two-pole assembly -/

set_option maxHeartbeats 1600000 in
/-- **An in-plane atom passing the scalar gate completes the two poles to a
positive-definite triple.**  All frame data is spelled through dot products
with the in-plane part of `poleP` and its cross product with the probe; no
adapted basis, no matrix square root. -/
theorem posDef_polePair_triple_of_scalarGate
    (design : WeightedDesign size 3) (poleP poleQ atomLabel : Fin size)
    (probe : Fin 3 → ℝ) (tiltRatio : ℝ)
    (hunit : probe ⬝ᵥ probe = 1)
    (hpoleNe : poleP ≠ poleQ)
    (hatomNotP : atomLabel ≠ poleP) (hatomNotQ : atomLabel ≠ poleQ)
    (hatomPlanar : design.atom atomLabel ⬝ᵥ probe = 0)
    (hantiparallel : design.atom poleQ
        - (design.atom poleQ ⬝ᵥ probe) • probe
      = tiltRatio • (design.atom poleP
        - (design.atom poleP ⬝ᵥ probe) • probe))
    (hseedNe : design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe ≠ 0)
    (haxisBlockPos : 0 < (design.atom poleP ⬝ᵥ probe) ^ 2
        + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
    (hpairGapPos : 0 <
        ((design.atom poleP ⬝ᵥ probe) ^ 2 + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
            * (((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                * (1 + tiltRatio ^ 2) - 1)
          - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
              ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
            * ((design.atom poleP ⬝ᵥ probe)
                + tiltRatio * (design.atom poleQ ⬝ᵥ probe)) ^ 2)
    (hscalarGate :
        ((design.atom poleP ⬝ᵥ probe) ^ 2 + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
          * (design.atom atomLabel
              ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)) ^ 2
        < (((design.atom poleP ⬝ᵥ probe) ^ 2
                + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
              * (((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                    ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                  * (1 + tiltRatio ^ 2) - 1)
            - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
              * ((design.atom poleP ⬝ᵥ probe)
                  + tiltRatio * (design.atom poleQ ⬝ᵥ probe)) ^ 2)
          * ((design.atom atomLabel
                ⬝ᵥ crossProduct probe
                  (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)) ^ 2
              - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)))) :
    (subsetSum design (insert poleP (insert poleQ {atomLabel})) - 1).PosDef := by
  classical
  set poleAxisP := design.atom poleP ⬝ᵥ probe with hpoleAxisPDef
  set poleAxisQ := design.atom poleQ ⬝ᵥ probe with hpoleAxisQDef
  set seedVec := design.atom poleP - poleAxisP • probe with hseedDef
  set crossVec := crossProduct probe seedVec with hcrossDef
  set seedNormSq := seedVec ⬝ᵥ seedVec with hseedNormDef
  set atomAlong := design.atom atomLabel ⬝ᵥ seedVec with hatomAlongDef
  set atomAcross := design.atom atomLabel ⬝ᵥ crossVec with hatomAcrossDef
  have hseedPos : 0 < seedNormSq := dotProduct_self_pos hseedNe
  have hseedPlanar : probe ⬝ᵥ seedVec = 0 := by
    rw [hseedDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit,
      dotProduct_comm probe (design.atom poleP)]
    ring
  have hpoleQNotMem : poleQ ∉ ({atomLabel} : Finset (Fin size)) := by
    simp only [Finset.mem_singleton]
    exact fun hEq => hatomNotQ hEq.symm
  have hpolePNotMem : poleP ∉ insert poleQ ({atomLabel} : Finset (Fin size)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨fun hEq => hpoleNe hEq, fun hEq => hatomNotP hEq.symm⟩
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one design _),
      fun testVec htestNe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum,
    Matrix.one_mulVec, Finset.sum_insert hpolePNotMem,
    Finset.sum_insert hpoleQNotMem, Finset.sum_singleton]
  simp only [momentCoord]
  set testAlong := testVec ⬝ᵥ seedVec with htestAlongDef
  set testAcross := testVec ⬝ᵥ crossVec with htestAcrossDef
  set testAxis := testVec ⬝ᵥ probe with htestAxisDef
  -- pole pairings through the frame
  have hpolePDecomp : design.atom poleP = seedVec + poleAxisP • probe := by
    rw [hseedDef]
    abel
  have hpolePPairing : design.atom poleP ⬝ᵥ testVec
      = testAlong + poleAxisP * testAxis := by
    rw [hpolePDecomp, add_dotProduct, smul_dotProduct, smul_eq_mul,
      dotProduct_comm seedVec testVec, dotProduct_comm probe testVec]
  have hpoleQDecomp : design.atom poleQ
      = tiltRatio • seedVec + poleAxisQ • probe := by
    have hshifted := sub_eq_iff_eq_add.mp hantiparallel
    exact hshifted
  have hpoleQPairing : design.atom poleQ ⬝ᵥ testVec
      = tiltRatio * testAlong + poleAxisQ * testAxis := by
    rw [hpoleQDecomp, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, dotProduct_comm seedVec testVec,
      dotProduct_comm probe testVec]
  -- the planar atom's pairing through the bilinear expansion
  have hatomExpansion : seedNormSq * (design.atom atomLabel ⬝ᵥ testVec)
      = atomAlong * testAlong + atomAcross * testAcross := by
    have hexp := planarBasis_bilinear_expansion probe seedVec
      (design.atom atomLabel) testVec hunit hseedPlanar
    rw [hatomPlanar, ← hcrossDef, ← hatomAlongDef, ← htestAlongDef,
      ← hatomAcrossDef, ← htestAcrossDef, ← hseedNormDef] at hexp
    linear_combination -hexp
  -- the test vector's norm through the same expansion
  have hnormExpansion : seedNormSq * (testVec ⬝ᵥ testVec)
      = testAlong ^ 2 + testAcross ^ 2 + seedNormSq * testAxis ^ 2 := by
    have hexp := planarBasis_bilinear_expansion probe seedVec testVec testVec
      hunit hseedPlanar
    rw [← hcrossDef, ← htestAlongDef, ← htestAcrossDef, ← htestAxisDef,
      ← hseedNormDef] at hexp
    linear_combination -hexp
  -- nontriviality of the frame coordinates
  have hnontrivial : ¬ (testAlong = 0 ∧ testAcross = 0 ∧ testAxis = 0) := by
    rintro ⟨halongZero, hacrossZero, haxisZero⟩
    apply htestNe
    have hnormZero : seedNormSq * (testVec ⬝ᵥ testVec) = 0 := by
      rw [hnormExpansion, halongZero, hacrossZero, haxisZero]
      ring
    have htestNormZero : testVec ⬝ᵥ testVec = 0 := by
      rcases mul_eq_zero.mp hnormZero with hcase | hcase
      · exact absurd hcase hseedPos.ne'
      · exact hcase
    by_contra htestNeInner
    exact absurd htestNormZero (dotProduct_self_pos htestNeInner).ne'
  -- the scalar core fires
  have hcore := polePairClearedForm_pos (seedNormSq := seedNormSq)
    (tiltRatio := tiltRatio) (poleAxisP := poleAxisP) (poleAxisQ := poleAxisQ)
    (atomAlong := atomAlong) (atomAcross := atomAcross)
    (testAlong := testAlong) (testAcross := testAcross) (testAxis := testAxis)
    hseedPos haxisBlockPos hpairGapPos hscalarGate hnontrivial
  -- deterministic bridges from the frame coordinates to the raw pairings
  have hatomSq : seedNormSq ^ 2 * (design.atom atomLabel ⬝ᵥ testVec) ^ 2
      = (atomAlong * testAlong + atomAcross * testAcross) ^ 2 := by
    rw [← hatomExpansion]
    ring
  have hnormScaled : seedNormSq ^ 2 * (testVec ⬝ᵥ testVec)
      = seedNormSq * (testAlong ^ 2 + testAcross ^ 2)
        + seedNormSq ^ 2 * testAxis ^ 2 := by
    linear_combination seedNormSq * hnormExpansion
  have hbridge : seedNormSq ^ 2
        * ((design.atom poleP ⬝ᵥ testVec) ^ 2
            + ((design.atom poleQ ⬝ᵥ testVec) ^ 2
                + (design.atom atomLabel ⬝ᵥ testVec) ^ 2)
            - testVec ⬝ᵥ testVec)
      = seedNormSq ^ 2 * (testAlong + poleAxisP * testAxis) ^ 2
        + seedNormSq ^ 2 * (tiltRatio * testAlong + poleAxisQ * testAxis) ^ 2
        + (atomAlong * testAlong + atomAcross * testAcross) ^ 2
        - seedNormSq * (testAlong ^ 2 + testAcross ^ 2)
        - seedNormSq ^ 2 * testAxis ^ 2 := by
    rw [hpolePPairing, hpoleQPairing]
    linear_combination hatomSq - hnormScaled
  have hscaledPos : 0 < seedNormSq ^ 2
      * ((design.atom poleP ⬝ᵥ testVec) ^ 2
          + ((design.atom poleQ ⬝ᵥ testVec) ^ 2
              + (design.atom atomLabel ⬝ᵥ testVec) ^ 2)
          - testVec ⬝ᵥ testVec) := by
    rw [hbridge]
    exact hcore
  have hseedSqPos : 0 < seedNormSq ^ 2 := by positivity
  by_contra hnotPos
  push Not at hnotPos
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hseedSqPos.le hnotPos, hscaledPos]

/-! ## Part 5: the antiparallel extraction, at vector level -/

set_option maxHeartbeats 1600000 in
/-- **The two poles' in-plane parts are antiparallel as VECTORS.**  The landed
`Gtz.offPlanePair_projection_antiparallel` cancels the two poles against every
in-plane direction; testing against the probe as well pins the whole vector,
with the explicit ratio `-(t_p a_P)/(t_q a_Q)`. -/
theorem offPlanePair_inPlanePart_eq_smul
    (design : WeightedDesign size 3) (poleP poleQ : Fin size)
    (probe : Fin 3 → ℝ) (hunit : probe ⬝ᵥ probe = 1)
    (hpoleNe : poleP ≠ poleQ)
    (hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0)
    (hoffQ : design.atom poleQ ⬝ᵥ probe ≠ 0) :
    design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe
      = (-(design.weight poleP * (design.atom poleP ⬝ᵥ probe))
          / (design.weight poleQ * (design.atom poleQ ⬝ᵥ probe)))
        • (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe) := by
  classical
  have hdenomNe : design.weight poleQ * (design.atom poleQ ⬝ᵥ probe) ≠ 0 :=
    mul_ne_zero (design.weight_pos poleQ).ne' hoffQ
  refine eq_of_forall_dotProduct_eq fun testVec => ?_
  have hperp : (testVec - (probe ⬝ᵥ testVec) • probe) ⬝ᵥ probe = 0 := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit,
      dotProduct_comm testVec probe]
    ring
  have hcancel := offPlanePair_projection_antiparallel design poleP poleQ hpoleNe
    (normalVec := probe) hplanarOthers (testVec - (probe ⬝ᵥ testVec) • probe) hperp
  have hexpandP : design.atom poleP ⬝ᵥ (testVec - (probe ⬝ᵥ testVec) • probe)
      = design.atom poleP ⬝ᵥ testVec
        - (probe ⬝ᵥ testVec) * (design.atom poleP ⬝ᵥ probe) := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hexpandQ : design.atom poleQ ⬝ᵥ (testVec - (probe ⬝ᵥ testVec) • probe)
      = design.atom poleQ ⬝ᵥ testVec
        - (probe ⬝ᵥ testVec) * (design.atom poleQ ⬝ᵥ probe) := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hexpandP, hexpandQ] at hcancel
  have hleft : (design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe)
        ⬝ᵥ testVec
      = design.atom poleQ ⬝ᵥ testVec
        - (design.atom poleQ ⬝ᵥ probe) * (probe ⬝ᵥ testVec) := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have hright : ((-(design.weight poleP * (design.atom poleP ⬝ᵥ probe))
          / (design.weight poleQ * (design.atom poleQ ⬝ᵥ probe)))
        • (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
        ⬝ᵥ testVec
      = (-(design.weight poleP * (design.atom poleP ⬝ᵥ probe))
          / (design.weight poleQ * (design.atom poleQ ⬝ᵥ probe)))
        * (design.atom poleP ⬝ᵥ testVec
            - (design.atom poleP ⬝ᵥ probe) * (probe ⬝ᵥ testVec)) := by
    rw [smul_dotProduct, smul_eq_mul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul]
  rw [hleft, hright, div_mul_eq_mul_div, eq_div_iff hdenomNe]
  linear_combination hcancel

/-! ## Part 6: CELL2 — the gate averages against in-plane Parseval -/

set_option maxHeartbeats 1600000 in
/-- **When the pole-pair gap beats the planar deficit on average, some planar
atom passes the gate and the two-pole triple strictly dominates.**  The two
planar moment identities are Parseval at the seed and at the cross vector,
with the poles' contributions computed exactly through antiparallelism; the
average of the gate scores over the planar family is then positive, so some
atom passes.  No selection cleverness — this is the interior of the CELL2
region of the two-pole stratum. -/
theorem exists_posDef_triple_of_gateAverage
    (design : WeightedDesign size 3) (poleP poleQ : Fin size)
    (probe : Fin 3 → ℝ) (tiltRatio : ℝ)
    (hunit : probe ⬝ᵥ probe = 1)
    (hpoleNe : poleP ≠ poleQ)
    (hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0)
    (hantiparallel : design.atom poleQ
        - (design.atom poleQ ⬝ᵥ probe) • probe
      = tiltRatio • (design.atom poleP
        - (design.atom poleP ⬝ᵥ probe) • probe))
    (hseedNe : design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe ≠ 0)
    (haxisBlockPos : 0 < (design.atom poleP ⬝ᵥ probe) ^ 2
        + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
    (hgateAverage :
        ((design.atom poleP ⬝ᵥ probe) ^ 2 + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
            * (1 - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                * (design.weight poleP + design.weight poleQ * tiltRatio ^ 2))
          < (((design.atom poleP ⬝ᵥ probe) ^ 2
                  + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
                * (((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                      ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                    * (1 + tiltRatio ^ 2) - 1)
              - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                * ((design.atom poleP ⬝ᵥ probe)
                    + tiltRatio * (design.atom poleQ ⬝ᵥ probe)) ^ 2)
            * (design.weight poleP + design.weight poleQ)) :
    ∃ dominatingTriple : Finset (Fin size),
      dominatingTriple.card = 3
        ∧ (subsetSum design dominatingTriple - 1).PosDef := by
  classical
  set poleAxisP := design.atom poleP ⬝ᵥ probe with hpoleAxisPDef
  set poleAxisQ := design.atom poleQ ⬝ᵥ probe with hpoleAxisQDef
  set seedVec := design.atom poleP - poleAxisP • probe with hseedDef
  set crossVec := crossProduct probe seedVec with hcrossDef
  set seedNormSq := seedVec ⬝ᵥ seedVec with hseedNormDef
  set axisBlock := poleAxisP ^ 2 + poleAxisQ ^ 2 - 1 with haxisBlockDef
  set pairGap := axisBlock * (seedNormSq * (1 + tiltRatio ^ 2) - 1)
      - seedNormSq * (poleAxisP + tiltRatio * poleAxisQ) ^ 2 with hpairGapDef
  set weightP := design.weight poleP with hweightPDef
  set weightQ := design.weight poleQ with hweightQDef
  have hseedPos : 0 < seedNormSq := dotProduct_self_pos hseedNe
  have hseedPlanar : probe ⬝ᵥ seedVec = 0 := by
    rw [hseedDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit,
      dotProduct_comm probe (design.atom poleP)]
    ring
  have hpolePDecomp : design.atom poleP = seedVec + poleAxisP • probe := by
    rw [hseedDef]; abel
  have hpoleQDecomp : design.atom poleQ
      = tiltRatio • seedVec + poleAxisQ • probe := by
    have hshifted := sub_eq_iff_eq_add.mp hantiparallel
    exact hshifted
  -- pole pairings with the frame vectors
  have hpoleSeedP : design.atom poleP ⬝ᵥ seedVec = seedNormSq := by
    rw [hpolePDecomp, add_dotProduct, smul_dotProduct, smul_eq_mul,
      hseedPlanar, ← hseedNormDef]
    ring
  have hpoleSeedQ : design.atom poleQ ⬝ᵥ seedVec = tiltRatio * seedNormSq := by
    rw [hpoleQDecomp, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, hseedPlanar, ← hseedNormDef]
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
    rw [hcrossDef, planarCross_self_dot, hunit, hseedPlanar, ← hseedNormDef]
    ring
  -- sum splitting over the two poles
  set othersSet := (Finset.univ.erase poleP).erase poleQ with hothersDef
  have hqMemErase : poleQ ∈ Finset.univ.erase poleP :=
    Finset.mem_erase.mpr ⟨fun hEq => hpoleNe hEq.symm, Finset.mem_univ poleQ⟩
  have hsplit : ∀ scoreFn : Fin size → ℝ,
      ∑ c, scoreFn c
        = scoreFn poleP + (scoreFn poleQ + ∑ c ∈ othersSet, scoreFn c) := by
    intro scoreFn
    rw [← Finset.add_sum_erase _ scoreFn (Finset.mem_univ poleP),
      ← Finset.add_sum_erase _ scoreFn hqMemErase, hothersDef]
  have hothersNotP : ∀ c ∈ othersSet, c ≠ poleP := fun c hc =>
    (Finset.mem_erase.mp ((Finset.mem_erase.mp hc).2)).1
  have hothersNotQ : ∀ c ∈ othersSet, c ≠ poleQ := fun c hc =>
    (Finset.mem_erase.mp hc).1
  -- the two planar moment identities
  have hseedMoment : ∑ c ∈ othersSet,
        design.weight c * (design.atom c ⬝ᵥ seedVec) ^ 2
      = seedNormSq * (1 - seedNormSq * (weightP + weightQ * tiltRatio ^ 2)) := by
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
    linear_combination htotal
  have hcrossMoment : ∑ c ∈ othersSet,
        design.weight c * (design.atom c ⬝ᵥ crossVec) ^ 2
      = seedNormSq := by
    have htotal := sum_weighted_atomPairing design crossVec crossVec
    rw [hsplit (fun c => design.weight c
        * ((design.atom c ⬝ᵥ crossVec) * (design.atom c ⬝ᵥ crossVec)))] at htotal
    rw [hpoleCrossP, hpoleCrossQ, hcrossNorm] at htotal
    have hsquares : ∑ c ∈ othersSet,
        design.weight c
          * ((design.atom c ⬝ᵥ crossVec) * (design.atom c ⬝ᵥ crossVec))
        = ∑ c ∈ othersSet, design.weight c * (design.atom c ⬝ᵥ crossVec) ^ 2 :=
      Finset.sum_congr rfl fun c _ => by ring
    rw [hsquares] at htotal
    linear_combination htotal
  -- the planar weight mass
  have hothersMass : ∑ c ∈ othersSet, design.weight c
      = 1 - weightP - weightQ := by
    have htotal := design.weight_sum_one
    rw [hsplit design.weight, ← hweightPDef, ← hweightQDef] at htotal
    linarith
  -- the deficit is at most one
  have hdeficitLe : seedNormSq * (weightP + weightQ * tiltRatio ^ 2) ≤ 1 := by
    have hnonneg : 0 ≤ ∑ c ∈ othersSet,
        design.weight c * (design.atom c ⬝ᵥ seedVec) ^ 2 :=
      Finset.sum_nonneg fun c _ =>
        mul_nonneg (design.weight_pos c).le (sq_nonneg _)
    nlinarith [hseedMoment, hnonneg, hseedPos]
  -- the pair gap is positive
  have hweightPPos : 0 < weightP := design.weight_pos poleP
  have hweightQPos : 0 < weightQ := design.weight_pos poleQ
  have hpairGapPos : 0 < pairGap := by
    have hlhsNonneg : 0 ≤ axisBlock
        * (1 - seedNormSq * (weightP + weightQ * tiltRatio ^ 2)) :=
      mul_nonneg haxisBlockPos.le (by linarith [hdeficitLe])
    have hprodPos : 0 < pairGap * (weightP + weightQ) :=
      lt_of_le_of_lt hlhsNonneg hgateAverage
    by_contra hnotPos
    push Not at hnotPos
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hnotPos
      (by linarith : (0 : ℝ) ≤ weightP + weightQ), hprodPos]
  -- the averaged gate score is positive, so some planar atom passes
  have hgateSum : (0 : ℝ) < ∑ c ∈ othersSet, design.weight c
      * (pairGap * ((design.atom c ⬝ᵥ crossVec) ^ 2 - seedNormSq)
          - axisBlock * (design.atom c ⬝ᵥ seedVec) ^ 2) := by
    have hexpand : ∑ c ∈ othersSet, design.weight c
        * (pairGap * ((design.atom c ⬝ᵥ crossVec) ^ 2 - seedNormSq)
            - axisBlock * (design.atom c ⬝ᵥ seedVec) ^ 2)
        = pairGap * (∑ c ∈ othersSet,
              design.weight c * (design.atom c ⬝ᵥ crossVec) ^ 2)
          - pairGap * seedNormSq * (∑ c ∈ othersSet, design.weight c)
          - axisBlock * (∑ c ∈ othersSet,
              design.weight c * (design.atom c ⬝ᵥ seedVec) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hexpand, hcrossMoment, hseedMoment, hothersMass]
    have hdiffPos : 0 < pairGap * (weightP + weightQ)
        - axisBlock * (1 - seedNormSq * (weightP + weightQ * tiltRatio ^ 2)) :=
      by linarith [hgateAverage]
    have hgoalShape : pairGap * seedNormSq
          - pairGap * seedNormSq * (1 - weightP - weightQ)
          - axisBlock
              * (seedNormSq * (1 - seedNormSq * (weightP + weightQ * tiltRatio ^ 2)))
        = seedNormSq * (pairGap * (weightP + weightQ)
            - axisBlock
                * (1 - seedNormSq * (weightP + weightQ * tiltRatio ^ 2))) := by
      ring
    calc (0 : ℝ) < seedNormSq * (pairGap * (weightP + weightQ)
        - axisBlock * (1 - seedNormSq * (weightP + weightQ * tiltRatio ^ 2))) :=
          mul_pos hseedPos hdiffPos
      _ = _ := hgoalShape.symm
  have hgateAtom : ∃ c ∈ othersSet,
      0 < design.weight c
        * (pairGap * ((design.atom c ⬝ᵥ crossVec) ^ 2 - seedNormSq)
            - axisBlock * (design.atom c ⬝ᵥ seedVec) ^ 2) := by
    by_contra hnone
    push Not at hnone
    have hnonpos : ∑ c ∈ othersSet, design.weight c
        * (pairGap * ((design.atom c ⬝ᵥ crossVec) ^ 2 - seedNormSq)
            - axisBlock * (design.atom c ⬝ᵥ seedVec) ^ 2) ≤ 0 :=
      Finset.sum_nonpos fun c hc => hnone c hc
    linarith [hgateSum]
  obtain ⟨atomLabel, hatomMem, hatomScorePos⟩ := hgateAtom
  have hatomNotP : atomLabel ≠ poleP := hothersNotP atomLabel hatomMem
  have hatomNotQ : atomLabel ≠ poleQ := hothersNotQ atomLabel hatomMem
  have hatomGate : axisBlock * (design.atom atomLabel ⬝ᵥ seedVec) ^ 2
      < pairGap * ((design.atom atomLabel ⬝ᵥ crossVec) ^ 2 - seedNormSq) := by
    have hweightPos := design.weight_pos atomLabel
    by_contra hnotGate
    push Not at hnotGate
    have hscoreNonpos : design.weight atomLabel
        * (pairGap * ((design.atom atomLabel ⬝ᵥ crossVec) ^ 2 - seedNormSq)
            - axisBlock * (design.atom atomLabel ⬝ᵥ seedVec) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hweightPos.le (by linarith)
    linarith [hatomScorePos]
  refine ⟨insert poleP (insert poleQ {atomLabel}), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun hEq => hpoleNe hEq, fun hEq => hatomNotP hEq.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun hEq => hatomNotQ hEq.symm),
      Finset.card_singleton]
  · refine posDef_polePair_triple_of_scalarGate design poleP poleQ atomLabel
      probe tiltRatio hunit hpoleNe hatomNotP hatomNotQ
      (hplanarOthers atomLabel hatomNotP hatomNotQ) hantiparallel hseedNe
      ?_ ?_ ?_
    · rw [← hpoleAxisPDef, ← hpoleAxisQDef]
      exact haxisBlockPos
    · rw [← hpoleAxisPDef, ← hpoleAxisQDef, ← hseedDef, ← hseedNormDef,
        ← hpairGapDef]
      exact hpairGapPos
    · rw [← hpoleAxisPDef, ← hpoleAxisQDef, ← hseedDef, ← hseedNormDef,
        ← hcrossDef, ← haxisBlockDef, ← hpairGapDef]
      exact hatomGate

/-! ## Part 6b: the single-carrier tilt is identically zero — the round-one
wall was VACUOUS

The predecessor lane reduced the single-carrier substratum to a planar pair
against the tilted target `I_H + (t_b/(1 - t_b)) h h^T`, `h` the in-plane part
of the sole off-plane atom, and named the regime `t_b |h|^2 in (1/2, 1)` as its
open wall.  That regime is EMPTY: Parseval's probe row forces the sole
off-plane atom PARALLEL to the probe, so `h = 0` always and the target is the
plain in-plane identity, which the shipped rank-two kit clears.  The whole
single-carrier substratum is in any case already closed in the tree by
`Gtz.not_isTie_of_soleOffPlane`; this theorem records WHY the wall was a
phantom rather than a hard case. -/

/-- **A sole off-plane atom has no in-plane part.**  Rides the landed collapse
`Gtz.soleOffPlane_normal_eq_smul_pole`: the probe is a multiple of the pole's
atom, so the pole's atom is a multiple of the probe and its in-plane
projection vanishes identically. -/
theorem soleOffPlane_inPlanePart_eq_zero (design : WeightedDesign size 3)
    (poleLabel : Fin size) (probe : Fin 3 → ℝ) (hunit : probe ⬝ᵥ probe = 1)
    (hplanar : ∀ c, c ≠ poleLabel → design.atom c ⬝ᵥ probe = 0) :
    design.atom poleLabel - (design.atom poleLabel ⬝ᵥ probe) • probe = 0 := by
  have hcollapse := soleOffPlane_normal_eq_smul_pole design poleLabel
    (normalVec := probe) hplanar
  set coeff := design.weight poleLabel * (design.atom poleLabel ⬝ᵥ probe)
    with hcoeffDef
  have hcoeffNe : coeff ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hcollapse
    rw [hcollapse, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  have hpoleEq : design.atom poleLabel = coeff⁻¹ • probe := by
    rw [hcollapse, smul_smul, inv_mul_cancel₀ hcoeffNe, one_smul]
  have hpairing : design.atom poleLabel ⬝ᵥ probe = coeff⁻¹ := by
    rw [hpoleEq, smul_dotProduct, smul_eq_mul, hunit, mul_one]
  rw [hpairing, ← hpoleEq, sub_self]

/-! ## Part 7: the two-pole frame is unconditional -/

/-- Two labels never exhaust a design that has a third atom: their weights sum
strictly below one. -/
theorem twoPole_weight_sum_lt_one (design : WeightedDesign size rank)
    (poleP poleQ thirdLabel : Fin size) (hpoleNe : poleP ≠ poleQ)
    (hthirdP : thirdLabel ≠ poleP) (hthirdQ : thirdLabel ≠ poleQ) :
    design.weight poleP + design.weight poleQ < 1 := by
  classical
  have hqMemErase : poleQ ∈ Finset.univ.erase poleP :=
    Finset.mem_erase.mpr ⟨fun hEq => hpoleNe hEq.symm, Finset.mem_univ poleQ⟩
  have hthirdMem : thirdLabel ∈ (Finset.univ.erase poleP).erase poleQ :=
    Finset.mem_erase.mpr ⟨hthirdQ,
      Finset.mem_erase.mpr ⟨hthirdP, Finset.mem_univ thirdLabel⟩⟩
  have hsplit : ∑ c, design.weight c
      = design.weight poleP + (design.weight poleQ
          + ∑ c ∈ (Finset.univ.erase poleP).erase poleQ, design.weight c) := by
    rw [← Finset.add_sum_erase _ design.weight (Finset.mem_univ poleP),
      ← Finset.add_sum_erase _ design.weight hqMemErase]
  have hrestGe : design.weight thirdLabel
      ≤ ∑ c ∈ (Finset.univ.erase poleP).erase poleQ, design.weight c :=
    Finset.single_le_sum (fun c _ => (design.weight_pos c).le) hthirdMem
  have hthirdPos : 0 < design.weight thirdLabel := design.weight_pos thirdLabel
  have htotal := design.weight_sum_one
  rw [hsplit] at htotal
  linarith

/-- **The axis block of a two-pole configuration is automatically positive.**
Parseval at the unit probe reads `t_P a_P^2 + t_Q a_Q^2 = 1` on the two poles
alone; since their weights miss a third atom's, the larger squared pairing
already exceeds one. -/
theorem one_lt_axisBlock_of_offPlanePair (design : WeightedDesign size 3)
    (poleP poleQ thirdLabel : Fin size) (probe : Fin 3 → ℝ)
    (hunit : probe ⬝ᵥ probe = 1) (hpoleNe : poleP ≠ poleQ)
    (hthirdP : thirdLabel ≠ poleP) (hthirdQ : thirdLabel ≠ poleQ)
    (hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0) :
    1 < (design.atom poleP ⬝ᵥ probe) ^ 2
      + (design.atom poleQ ⬝ᵥ probe) ^ 2 := by
  have hparseval := offPlanePair_normalSquare_eq design poleP poleQ hpoleNe
    (normalVec := probe) hplanarOthers
  rw [hunit] at hparseval
  have hmassLt := twoPole_weight_sum_lt_one design poleP poleQ thirdLabel
    hpoleNe hthirdP hthirdQ
  have hweightPPos : 0 < design.weight poleP := design.weight_pos poleP
  have hweightQPos : 0 < design.weight poleQ := design.weight_pos poleQ
  have hsqPNonneg : 0 ≤ (design.atom poleP ⬝ᵥ probe) ^ 2 := sq_nonneg _
  have hsqQNonneg : 0 ≤ (design.atom poleQ ⬝ᵥ probe) ^ 2 := sq_nonneg _
  rcases le_total ((design.atom poleP ⬝ᵥ probe) ^ 2)
      ((design.atom poleQ ⬝ᵥ probe) ^ 2) with hle | hle
  · nlinarith [hparseval, hmassLt, hle, hweightPPos, hweightQPos]
  · nlinarith [hparseval, hmassLt, hle, hweightPPos, hweightQPos]

/-- **The in-plane seed of a pole is nonzero at a primitive design.**  If it
vanished the pole would be parallel to the probe, and the landed two-pole
probe theorem forbids that. -/
theorem seed_ne_zero_of_offPlanePair_of_isPrimitive (design : WeightedDesign size 3)
    (hprimitive : IsPrimitiveDesign design) (poleP poleQ : Fin size)
    (hpoleNe : poleP ≠ poleQ) (probe : Fin 3 → ℝ) (hprobeNe : probe ≠ 0)
    (hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0)
    (hoffP : design.atom poleP ⬝ᵥ probe ≠ 0)
    (hoffQ : design.atom poleQ ⬝ᵥ probe ≠ 0) :
    design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe ≠ 0 := by
  intro hseedZero
  obtain ⟨planarProbe, hplanarProbe, hpolePPairing⟩ :=
    exists_planarProbe_of_offPlanePair_of_isPrimitive design hprimitive
      poleP poleQ hpoleNe hprobeNe hplanarOthers hoffP hoffQ
  apply hpolePPairing
  have hpoleDecomp : design.atom poleP = (design.atom poleP ⬝ᵥ probe) • probe := by
    have := sub_eq_zero.mp hseedZero
    exact this
  rw [hpoleDecomp, smul_dotProduct, smul_eq_mul,
    dotProduct_comm probe planarProbe, hplanarProbe, mul_zero]

/-! ## Part 8: the branch-(iii) capstone, modulo the named selection residual -/

/-- **The named residual of branch (iii): the CELL3 region only.**  A primitive
two-pole coplanar configuration whose GATE AVERAGE FAILS still carries a
strictly dominating triple.  The hypothesis is strictly weaker than the goal:
the gate-average region (CELL2) is discharged unconditionally by
`exists_posDef_triple_of_gateAverage`, so only its complement is assumed.

Numerically hammered in exact rationals: 8,445 admissible configurations across
four adversarial samplers (generic, symmetric weights, heavy poles, large tilt),
ZERO failures; in the hard cell the max-bracket planar pair at the minimum-tilt
steep pole fires every time (0 violations out of 8,445), while four other
plausible selection rules were refuted.  It is a hypothesis because the
pair-selection inequality is not yet a proof. -/
def TwoPoleStratumSelection (size : ℕ) : Prop :=
  ∀ (design : WeightedDesign size 3) (probe : Fin 3 → ℝ) (tiltRatio : ℝ),
    probe ⬝ᵥ probe = 1 →
    ∀ poleP poleQ : Fin size, poleP ≠ poleQ →
      (∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0) →
      design.atom poleP ⬝ᵥ probe ≠ 0 → design.atom poleQ ⬝ᵥ probe ≠ 0 →
      IsPrimitiveDesign design →
      design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe
          = tiltRatio • (design.atom poleP
            - (design.atom poleP ⬝ᵥ probe) • probe) →
      ¬ (((design.atom poleP ⬝ᵥ probe) ^ 2
              + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
            * (1 - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                * (design.weight poleP + design.weight poleQ * tiltRatio ^ 2))
          < (((design.atom poleP ⬝ᵥ probe) ^ 2
                  + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
                * (((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                      ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                    * (1 + tiltRatio ^ 2) - 1)
              - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                  ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                * ((design.atom poleP ⬝ᵥ probe)
                    + tiltRatio * (design.atom poleQ ⬝ᵥ probe)) ^ 2)
            * (design.weight poleP + design.weight poleQ)) →
      ∃ dominatingTriple : Finset (Fin size), dominatingTriple.card = 3
        ∧ (subsetSum design dominatingTriple - 1).PosDef

/-- **No primitive design with exactly two off-plane atoms is a tie**, given the
CELL3 residual.  The tilt ratio comes from `offPlanePair_inPlanePart_eq_smul`,
the seed from `seed_ne_zero_of_offPlanePair_of_isPrimitive`, the axis block
from `one_lt_axisBlock_of_offPlanePair` — all unconditional — and the case
split on the gate average sends the CELL2 branch into
`exists_posDef_triple_of_gateAverage`. -/
theorem not_isTie_of_offPlanePair_of_selection (hselection : TwoPoleStratumSelection size)
    (design : WeightedDesign size 3) (probe : Fin 3 → ℝ)
    (hprobeNe : probe ≠ 0) (hunit : probe ⬝ᵥ probe = 1)
    (poleP poleQ thirdLabel : Fin size) (hpoleNe : poleP ≠ poleQ)
    (hthirdP : thirdLabel ≠ poleP) (hthirdQ : thirdLabel ≠ poleQ)
    (hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ → design.atom c ⬝ᵥ probe = 0)
    (hoffP : design.atom poleP ⬝ᵥ probe ≠ 0)
    (hoffQ : design.atom poleQ ⬝ᵥ probe ≠ 0)
    (hprimitive : IsPrimitiveDesign design) :
    ¬ IsTie design := by
  intro htie
  set tiltRatio := -(design.weight poleP * (design.atom poleP ⬝ᵥ probe))
      / (design.weight poleQ * (design.atom poleQ ⬝ᵥ probe)) with htiltDef
  have hantiparallel : design.atom poleQ - (design.atom poleQ ⬝ᵥ probe) • probe
      = tiltRatio • (design.atom poleP
        - (design.atom poleP ⬝ᵥ probe) • probe) :=
    offPlanePair_inPlanePart_eq_smul design poleP poleQ probe hunit hpoleNe
      hplanarOthers hoffQ
  have hseedNe : design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe ≠ 0 :=
    seed_ne_zero_of_offPlanePair_of_isPrimitive design hprimitive poleP poleQ
      hpoleNe probe hprobeNe hplanarOthers hoffP hoffQ
  have haxisBlockPos : 0 < (design.atom poleP ⬝ᵥ probe) ^ 2
      + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1 := by
    have hone := one_lt_axisBlock_of_offPlanePair design poleP poleQ thirdLabel
      probe hunit hpoleNe hthirdP hthirdQ hplanarOthers
    linarith
  by_cases hgateAverage :
      ((design.atom poleP ⬝ᵥ probe) ^ 2 + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
          * (1 - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
              * (design.weight poleP + design.weight poleQ * tiltRatio ^ 2))
        < (((design.atom poleP ⬝ᵥ probe) ^ 2
                + (design.atom poleQ ⬝ᵥ probe) ^ 2 - 1)
              * (((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                    ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
                  * (1 + tiltRatio ^ 2) - 1)
            - ((design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe)
                ⬝ᵥ (design.atom poleP - (design.atom poleP ⬝ᵥ probe) • probe))
              * ((design.atom poleP ⬝ᵥ probe)
                  + tiltRatio * (design.atom poleQ ⬝ᵥ probe)) ^ 2)
          * (design.weight poleP + design.weight poleQ)
  · obtain ⟨dominatingTriple, hcard, hposDef⟩ :=
      exists_posDef_triple_of_gateAverage design poleP poleQ probe tiltRatio
        hunit hpoleNe hplanarOthers hantiparallel hseedNe haxisBlockPos
        hgateAverage
    exact htie.2 dominatingTriple hcard hposDef
  · obtain ⟨dominatingTriple, hcard, hposDef⟩ :=
      hselection design probe tiltRatio hunit poleP poleQ hpoleNe hplanarOthers
        hoffP hoffQ hprimitive hantiparallel hgateAverage
    exact htie.2 dominatingTriple hcard hposDef

/-- **A `(6,3)` tie with at most two off-plane atoms has a parallel pair**,
given the named residual.  The one-off-plane arm is UNCONDITIONAL — the tree's
near-pencil transport `Gtz.not_isTie_of_soleOffPlane` kills it, and the
predecessor lane's "anisotropic planar pair" wall was VACUOUS there because a
sole off-plane atom is forced parallel to the probe
(`Gtz.soleOffPlane_normal_eq_smul_pole`), so its in-plane tilt is zero.  The
two-off-plane arm is Part 8's residual. -/
theorem sixThree_hasParallelPair_of_isTie_of_offPlaneCard_le_two
    (hselection : TwoPoleStratumSelection 6)
    (design : WeightedDesign 6 3) (htie : IsTie design)
    (probe : Fin 3 → ℝ) (hprobeNe : probe ≠ 0)
    (hunit : probe ⬝ᵥ probe = 1)
    (hoffPlaneSmall :
      (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0).card ≤ 2) :
    HasParallelPair design := by
  classical
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  set offPlaneSet := Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0
    with hoffPlaneDef
  have hplanarOfNotMem : ∀ c, c ∉ offPlaneSet → design.atom c ⬝ᵥ probe = 0 := by
    intro c hnotMem
    by_contra hne
    exact hnotMem (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hne⟩)
  have hoffPlaneGe : 2 ≤ offPlaneSet.card := by
    have hcomplement := two_le_card_offPlane_of_isTie (by norm_num) design htie
      offPlaneSetᶜ hprobeNe (fun label hlabel => hplanarOfNotMem label
        (Finset.mem_compl.mp hlabel))
    rwa [compl_compl] at hcomplement
  have hoffPlaneCard : offPlaneSet.card = 2 := le_antisymm hoffPlaneSmall hoffPlaneGe
  obtain ⟨poleP, poleQ, hpoleNe, hpairEq⟩ := Finset.card_eq_two.mp hoffPlaneCard
  have hmemP : poleP ∈ offPlaneSet := by rw [hpairEq]; exact Finset.mem_insert_self _ _
  have hmemQ : poleQ ∈ offPlaneSet := by
    rw [hpairEq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hoffP : design.atom poleP ⬝ᵥ probe ≠ 0 := (Finset.mem_filter.mp hmemP).2
  have hoffQ : design.atom poleQ ⬝ᵥ probe ≠ 0 := (Finset.mem_filter.mp hmemQ).2
  have hplanarOthers : ∀ c, c ≠ poleP → c ≠ poleQ →
      design.atom c ⬝ᵥ probe = 0 := by
    intro c hcP hcQ
    refine hplanarOfNotMem c ?_
    rw [hpairEq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hcP, hcQ⟩
  have hthirdExists : ∃ thirdLabel : Fin 6,
      thirdLabel ≠ poleP ∧ thirdLabel ≠ poleQ := by
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
  obtain ⟨thirdLabel, hthirdP, hthirdQ⟩ := hthirdExists
  exact not_isTie_of_offPlanePair_of_selection hselection design probe hprobeNe
    hunit poleP poleQ thirdLabel hpoleNe hthirdP hthirdQ hplanarOthers hoffP
    hoffQ hprimitive htie

/-! ## Part 9: entering from the trichotomy's branch (iii) -/

/-- **A primitive `(6,3)` design with a coplanar stress has at most two
off-plane atoms.**  The stress support cannot span (the probe annihilates it),
so its span has dimension at most two; dimension at most ONE would force a
parallel pair, which primitivity forbids (the rank-zero case puts a zero atom
at a supported label, the rank-one case puts two supported atoms on one
generator, and the span-relative split law supplies the second label); so the
span is exactly two and the split law gives at least four supported labels.
Off-plane atoms are unsupported, so at most two remain. -/
theorem sixThree_offPlaneCard_le_two_of_coplanarStress (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    (hstressNonzero : stressCoeff ≠ 0) (hprobeNe : probe ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hcoplanar : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0)
    (hprimitive : IsPrimitiveDesign design) :
    (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0).card ≤ 2 := by
  classical
  have hnoPair : ¬ hasParallelAtomPair design.atom := fun hpair =>
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)
      ((hasParallelPair_iff_hasParallelAtomPair design).mpr hpair)
  have hnotSpanning : ¬ hasSpanningSupport design.atom stressCoeff := fun hspanning =>
    hprobeNe (hspanning probe hcoplanar)
  have hrankLe : Module.finrank ℝ (supportSpan design.atom stressCoeff) ≤ 2 := by
    by_contra hlarge
    have hambient : Module.finrank ℝ (supportSpan design.atom stressCoeff) ≤ 3 := by
      have hbound := Submodule.finrank_le (supportSpan design.atom stressCoeff)
      rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hbound
    have hrankEq : Module.finrank ℝ (supportSpan design.atom stressCoeff) = 3 := by
      omega
    exact hnotSpanning
      (hasSpanningSupport_of_finrank_eq design.atom stressCoeff hrankEq)
  have hrankGe : 2 ≤ Module.finrank ℝ (supportSpan design.atom stressCoeff) := by
    by_contra hsmall
    refine hnoPair ?_
    have hlowRank : Module.finrank ℝ (supportSpan design.atom stressCoeff) ≤ 1 := by
      omega
    rcases (by omega : Module.finrank ℝ (supportSpan design.atom stressCoeff) = 0
        ∨ Module.finrank ℝ (supportSpan design.atom stressCoeff) = 1)
      with hzeroRank | honeRank
    · obtain ⟨liveLabel, hlive⟩ := Function.ne_iff.mp hstressNonzero
      have hliveSupported : stressCoeff liveLabel ≠ 0 := by simpa using hlive
      have hbot : supportSpan design.atom stressCoeff = ⊥ :=
        Submodule.finrank_eq_zero.mp hzeroRank
      have hzeroAtom : design.atom liveLabel = 0 := by
        have hmem := atom_mem_supportSpan design.atom hliveSupported
        rw [hbot] at hmem
        simpa using hmem
      obtain ⟨otherLabel, hother⟩ :=
        Fintype.exists_ne_of_one_lt_card (by simp) liveLabel
      exact ⟨otherLabel, liveLabel, 0, hother, by rw [hzeroAtom, zero_smul]⟩
    · obtain ⟨generator, hgenerator⟩ := exists_generator_of_finrank_eq_one honeRank
      have hlower :=
        twice_finrank_supportSpan_le_card_stressSupport design.atom hstress
      rw [honeRank] at hlower
      obtain ⟨firstLabel, hfirstMem, secondLabel, hsecondMem, hdistinct⟩ :=
        Finset.one_lt_card.mp (by omega : 1 < (stressSupport stressCoeff).card)
      obtain ⟨firstScale, hfirstScale⟩ := hgenerator (design.atom firstLabel)
        (atom_mem_supportSpan design.atom (mem_stressSupport_iff.mp hfirstMem))
      obtain ⟨secondScale, hsecondScale⟩ := hgenerator (design.atom secondLabel)
        (atom_mem_supportSpan design.atom (mem_stressSupport_iff.mp hsecondMem))
      by_cases hfirstZero : firstScale = 0
      · exact ⟨secondLabel, firstLabel, 0, hdistinct.symm, by
          rw [hfirstScale, hfirstZero, zero_smul, zero_smul]⟩
      · exact ⟨firstLabel, secondLabel, secondScale / firstScale, hdistinct, by
          rw [hsecondScale, hfirstScale, smul_smul,
            div_mul_cancel₀ _ hfirstZero]⟩
  have hrankEq : Module.finrank ℝ (supportSpan design.atom stressCoeff) = 2 := by
    omega
  have hsupportGe : 4 ≤ (stressSupport stressCoeff).card := by
    have hlower := twice_finrank_supportSpan_le_card_stressSupport design.atom hstress
    rw [hrankEq] at hlower
    omega
  have hsubset : (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0)
      ⊆ (stressSupport stressCoeff)ᶜ := by
    intro c hc
    rw [Finset.mem_compl, mem_stressSupport_iff]
    intro hsupported
    exact (Finset.mem_filter.mp hc).2 (hcoplanar c hsupported)
  have hcount := Finset.card_le_card hsubset
  rw [Finset.card_compl, Fintype.card_fin] at hcount
  omega

/-- **OB(iii), modulo the CELL3 residual: no primitive `(6,3)` tie carries a
coplanar-support stress.**  Stated contrapositively in the hinge's vocabulary —
a tie with branch-(iii) stress data has a parallel pair.  The single-off-plane
arm is unconditional (the tree's near-pencil transport, whose "anisotropic
planar pair" wall Part 6b shows was vacuous); the two-off-plane arm splits into
the gate-average region, discharged unconditionally by
`exists_posDef_triple_of_gateAverage`, and `TwoPoleStratumSelection`. -/
theorem sixThree_hasParallelPair_of_isTie_of_coplanarStress
    (hselection : TwoPoleStratumSelection 6)
    (design : WeightedDesign 6 3) (htie : IsTie design)
    {stressCoeff : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    (hstressNonzero : stressCoeff ≠ 0) (hprobeNe : probe ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hcoplanar : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) :
    HasParallelPair design := by
  classical
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  have hcardLe := sixThree_offPlaneCard_le_two_of_coplanarStress design
    hstressNonzero hprobeNe hstress hcoplanar hprimitive
  -- normalise the probe; the off-plane filter is scale invariant
  have hprobeNormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hsqrtPos : 0 < Real.sqrt (probe ⬝ᵥ probe) := Real.sqrt_pos.mpr hprobeNormPos
  set scale := (Real.sqrt (probe ⬝ᵥ probe))⁻¹ with hscaleDef
  have hscaleNe : scale ≠ 0 := inv_ne_zero hsqrtPos.ne'
  set unitProbe := scale • probe with hunitProbeDef
  have hunit : unitProbe ⬝ᵥ unitProbe = 1 := by
    rw [hunitProbeDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      hscaleDef, ← mul_assoc, ← mul_inv,
      Real.mul_self_sqrt hprobeNormPos.le]
    exact inv_mul_cancel₀ hprobeNormPos.ne'
  have hunitProbeNe : unitProbe ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    exact one_ne_zero hunit.symm
  have hpairingScaled : ∀ c : Fin 6,
      design.atom c ⬝ᵥ unitProbe = scale * (design.atom c ⬝ᵥ probe) := by
    intro c
    rw [hunitProbeDef, dotProduct_smul, smul_eq_mul]
  have hfilterEq : (Finset.univ.filter fun c => design.atom c ⬝ᵥ unitProbe ≠ 0)
      = Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0 := by
    refine Finset.filter_congr fun c _ => ?_
    rw [hpairingScaled c]
    constructor
    · intro hne hzero
      exact hne (by rw [hzero, mul_zero])
    · intro hne hzero
      exact hne ((mul_eq_zero.mp hzero).resolve_left hscaleNe)
  have hcardUnit : (Finset.univ.filter
      fun c => design.atom c ⬝ᵥ unitProbe ≠ 0).card ≤ 2 := by
    rw [hfilterEq]
    exact hcardLe
  exact hnoPair (sixThree_hasParallelPair_of_isTie_of_offPlaneCard_le_two
    hselection design htie unitProbe hunitProbeNe hunit hcardUnit)

end Gtz
