/-
# Branch (i): the insert-plane pair-completion transport

The exact reconnaissance of this lane (`r2_padded_map.py`, `r3_crossover.py`,
all rationals) shows the diamond's `(6,3)` boundary is sealed by TWO
mechanisms: small-axis-mass pads are killed by a tight tree going strict
(first-order law `y^T N_Q y = eps/(1-eps) y^T L y - gamma (v.y)^2`), while
LARGE-mass pads are killed by a PAIR completing the pad atom to a strictly
dominating triple.  The second mechanism lives on the plane orthogonal to the
INSERT atom, not on any tight plane, so the tight-drop residual family
(`TightDropOnPlaneSixThree`, `TightDropWithinBudgetSixThree`) cannot express
it — and the leverage-scalarized budget is asymptotically blind to it (its
left side grows like the insert leverage, its right side like the square
root).  This file lands the missing instrument.

* `posDef_insertCompletion_of_insertPlaneGate` — **THE PAIR-COMPLETION
  TRANSPORT.**  If the insert atom has leverage above one and the coupling
  gate holds on the insert's orthogonal plane,

      ((g_1.g_e)(g_1.planar) + (g_2.g_e)(g_2.planar))^2
        <  (lev_e^2 + (g_1.g_e)^2 + (g_2.g_e)^2 - lev_e)
             * ((g_1.planar)^2 + (g_2.planar)^2 - |planar|^2) ,

  then `{keptOne, keptTwo, insertLabel}` dominates strictly.  This is the
  landed axis-split criterion `Gtz.posDef_gap_of_axisSplit_coupling`
  instantiated at the NORMALIZED INSERT as the axis; the insert's own
  pairing drops out of every planar sum, so the statement is square-root
  free.  Note the gate forces the pair to dominate the insert plane
  strictly, with a margin scaled by the insert's leverage — the sharp form
  of the recon's `tau -> infinity` criterion.

* `exists_insertGateFailure_of_isTie` — the tie-side extraction: at a tie,
  for EVERY pair and every heavy insert the gate fails at some witness
  plane direction.  Together with `exists_gateFailure_of_isTie` (sibling
  file) this mechanizes the full per-axis inequality system a stress-free
  tie must satisfy: nine tight-plane exchange constraints AND the
  insert-plane pair constraints — the two families whose joint infeasibility
  is the sealing phenomenon the reconnaissance measured.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Design.TwoPoleStratum
import Gtz.Design.StressFreeNormalizer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-- Summing a score over an explicit unordered triple of distinct labels. -/
theorem sum_explicitTriple_of_ne {firstLabel secondLabel thirdLabel : Fin size}
    (hFirstSecond : firstLabel ≠ secondLabel) (hFirstThird : firstLabel ≠ thirdLabel)
    (hSecondThird : secondLabel ≠ thirdLabel) (scoreFn : Fin size → ℝ) :
    ∑ atomIndex ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)),
        scoreFn atomIndex
      = scoreFn firstLabel + scoreFn secondLabel + scoreFn thirdLabel := by
  classical
  rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hFirstSecond, hFirstThird⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact hSecondThird),
    Finset.sum_singleton]
  ring

/-- **THE PAIR-COMPLETION TRANSPORT.**  A heavy insert atom plus a pair that
dominates the insert's orthogonal plane with enough coupling margin form a
strictly dominating triple.  The axis-split criterion at the normalized
insert axis, with every hypothesis square-root free. -/
theorem posDef_insertCompletion_of_insertPlaneGate (design : WeightedDesign size rank)
    {keptOne keptTwo insertLabel : Fin size}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    (hinsertHeavy : 1 < design.atom insertLabel ⬝ᵥ design.atom insertLabel)
    (hgate : ∀ planar : Fin rank → ℝ,
      design.atom insertLabel ⬝ᵥ planar = 0 → planar ≠ 0 →
      ((design.atom keptOne ⬝ᵥ design.atom insertLabel)
            * (design.atom keptOne ⬝ᵥ planar)
          + (design.atom keptTwo ⬝ᵥ design.atom insertLabel)
            * (design.atom keptTwo ⬝ᵥ planar)) ^ 2
        < ((design.atom insertLabel ⬝ᵥ design.atom insertLabel) ^ 2
            + (design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
            + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2
            - (design.atom insertLabel ⬝ᵥ design.atom insertLabel))
          * ((design.atom keptOne ⬝ᵥ planar) ^ 2
            + (design.atom keptTwo ⬝ᵥ planar) ^ 2
            - planar ⬝ᵥ planar)) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin size))
        - 1).PosDef := by
  classical
  set insertVec := design.atom insertLabel with hinsertVecDef
  have hlevPos : 0 < insertVec ⬝ᵥ insertVec := by
    rw [hinsertVecDef]
    linarith
  have hsqrtPos : 0 < Real.sqrt (insertVec ⬝ᵥ insertVec) := Real.sqrt_pos.mpr hlevPos
  set axis : Fin rank → ℝ := (Real.sqrt (insertVec ⬝ᵥ insertVec))⁻¹ • insertVec
    with haxisDef
  have hunit : axis ⬝ᵥ axis = 1 := by
    rw [haxisDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hlevPos.le]
    exact inv_mul_cancel₀ hlevPos.ne'
  have hinvSq : ((Real.sqrt (insertVec ⬝ᵥ insertVec))⁻¹) ^ 2
      = (insertVec ⬝ᵥ insertVec)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hlevPos.le]
  have hpairAxis : ∀ atomVec : Fin rank → ℝ, atomVec ⬝ᵥ axis
      = (Real.sqrt (insertVec ⬝ᵥ insertVec))⁻¹ * (atomVec ⬝ᵥ insertVec) := by
    intro atomVec
    rw [haxisDef, dotProduct_smul, smul_eq_mul]
  have hinvPos : 0 < (insertVec ⬝ᵥ insertVec)⁻¹ := inv_pos.mpr hlevPos
  refine posDef_gap_of_axisSplit_coupling design
    ({keptOne, keptTwo, insertLabel} : Finset (Fin size)) hunit ?_ ?_
  · -- the axis-mass excess: the insert alone already carries it
    rw [sum_explicitTriple_of_ne hneKepts hneOneInsert hneTwoInsert
      (fun atomIndex => (design.atom atomIndex ⬝ᵥ axis) ^ 2)]
    have hvalues : (design.atom keptOne ⬝ᵥ axis) ^ 2
          + (design.atom keptTwo ⬝ᵥ axis) ^ 2
          + (design.atom insertLabel ⬝ᵥ axis) ^ 2
        = (insertVec ⬝ᵥ insertVec)⁻¹
            * ((design.atom keptOne ⬝ᵥ insertVec) ^ 2
              + (design.atom keptTwo ⬝ᵥ insertVec) ^ 2
              + (insertVec ⬝ᵥ insertVec) ^ 2) := by
      rw [hpairAxis (design.atom keptOne), hpairAxis (design.atom keptTwo),
        hpairAxis (design.atom insertLabel), ← hinsertVecDef]
      rw [mul_pow, mul_pow, mul_pow, hinvSq]
      ring
    rw [hvalues]
    have hfloor : (insertVec ⬝ᵥ insertVec)⁻¹ * (insertVec ⬝ᵥ insertVec) ^ 2
        = insertVec ⬝ᵥ insertVec := by
      field_simp
    nlinarith [mul_nonneg hinvPos.le
        (add_nonneg (sq_nonneg (design.atom keptOne ⬝ᵥ insertVec))
          (sq_nonneg (design.atom keptTwo ⬝ᵥ insertVec))),
      hinsertHeavy, hfloor, hinvPos]
  · -- the coupling on the insert plane
    intro planar hplanarAxis hplanarNe
    have hplanarInsert : insertVec ⬝ᵥ planar = 0 := by
      have hswap : planar ⬝ᵥ axis
          = (Real.sqrt (insertVec ⬝ᵥ insertVec))⁻¹ * (insertVec ⬝ᵥ planar) := by
        rw [haxisDef, dotProduct_smul, smul_eq_mul, dotProduct_comm planar insertVec]
      rw [hswap] at hplanarAxis
      rcases mul_eq_zero.mp hplanarAxis with hbad | hgood
      · exact absurd hbad (inv_ne_zero hsqrtPos.ne')
      · exact hgood
    have hgateAt := hgate planar hplanarInsert hplanarNe
    rw [sum_explicitTriple_of_ne hneKepts hneOneInsert hneTwoInsert
        (fun atomIndex => (design.atom atomIndex ⬝ᵥ axis)
          * (design.atom atomIndex ⬝ᵥ planar)),
      sum_explicitTriple_of_ne hneKepts hneOneInsert hneTwoInsert
        (fun atomIndex => (design.atom atomIndex ⬝ᵥ axis) ^ 2),
      sum_explicitTriple_of_ne hneKepts hneOneInsert hneTwoInsert
        (fun atomIndex => (design.atom atomIndex ⬝ᵥ planar) ^ 2)]
    have hinsertPlanar : design.atom insertLabel ⬝ᵥ planar = 0 := hplanarInsert
    rw [hpairAxis (design.atom keptOne), hpairAxis (design.atom keptTwo),
      hpairAxis (design.atom insertLabel), hinsertPlanar]
    set scaleInv := (Real.sqrt (insertVec ⬝ᵥ insertVec))⁻¹ with hscaleDef
    set levValue := insertVec ⬝ᵥ insertVec with hlevDef
    set pairOneIns := design.atom keptOne ⬝ᵥ insertVec with hp1
    set pairTwoIns := design.atom keptTwo ⬝ᵥ insertVec with hp2
    set pairOnePl := design.atom keptOne ⬝ᵥ planar with hq1
    set pairTwoPl := design.atom keptTwo ⬝ᵥ planar with hq2
    -- after the `set`s: hinvSq is scaleInv ^ 2 = levValue⁻¹, hlevPos is
    -- 0 < levValue, hinvPos is 0 < levValue⁻¹, and hgateAt is already in the
    -- pair vocabulary.  The left side collapses to levValue⁻¹ * A^2, the
    -- right to levValue⁻¹ * (lev^2 + pair masses - lev) * B, and the gate
    -- supplies the strict inequality between A^2 and that product.
    have hcancel : levValue⁻¹ * levValue = 1 := inv_mul_cancel₀ hlevPos.ne'
    have hlhs : (scaleInv * pairOneIns * pairOnePl + scaleInv * pairTwoIns * pairTwoPl
          + scaleInv * levValue * 0) ^ 2
        = levValue⁻¹ * (pairOneIns * pairOnePl + pairTwoIns * pairTwoPl) ^ 2 := by
      rw [← hinvSq]
      ring
    have hrhs : ((scaleInv * pairOneIns) ^ 2 + (scaleInv * pairTwoIns) ^ 2
            + (scaleInv * levValue) ^ 2 - 1)
          * (pairOnePl ^ 2 + pairTwoPl ^ 2 + 0 ^ 2 - planar ⬝ᵥ planar)
        = (levValue⁻¹ * (pairOneIns ^ 2 + pairTwoIns ^ 2 + levValue ^ 2) - 1)
          * (pairOnePl ^ 2 + pairTwoPl ^ 2 - planar ⬝ᵥ planar) := by
      rw [← hinvSq]
      ring
    rw [hlhs, hrhs]
    have hfactor : levValue⁻¹ * (pairOneIns ^ 2 + pairTwoIns ^ 2 + levValue ^ 2) - 1
        = levValue⁻¹ * (levValue ^ 2 + pairOneIns ^ 2 + pairTwoIns ^ 2 - levValue) := by
      linear_combination hcancel
    rw [hfactor, mul_assoc]
    exact mul_lt_mul_of_pos_left hgateAt hinvPos

/-- **THE INSERT GATE FAILS SOMEWHERE AT A TIE.**  For every pair of atoms and
every heavy insert forming a `rank`-subset, some direction of the insert's
orthogonal plane witnesses the failure of the completion gate.  This is the
tie's pair-completion inequality system in kernel form — the second family of
constraints the sealed-boundary reconnaissance identified, complementary to
the tight-plane exchange system. -/
theorem exists_insertGateFailure_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) {keptOne keptTwo insertLabel : Fin size}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    (hcard : ({keptOne, keptTwo, insertLabel} : Finset (Fin size)).card = rank)
    (hinsertHeavy : 1 < design.atom insertLabel ⬝ᵥ design.atom insertLabel) :
    ∃ planar : Fin rank → ℝ, design.atom insertLabel ⬝ᵥ planar = 0 ∧ planar ≠ 0
      ∧ ((design.atom insertLabel ⬝ᵥ design.atom insertLabel) ^ 2
            + (design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
            + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2
            - (design.atom insertLabel ⬝ᵥ design.atom insertLabel))
          * ((design.atom keptOne ⬝ᵥ planar) ^ 2
            + (design.atom keptTwo ⬝ᵥ planar) ^ 2
            - planar ⬝ᵥ planar)
        ≤ ((design.atom keptOne ⬝ᵥ design.atom insertLabel)
              * (design.atom keptOne ⬝ᵥ planar)
            + (design.atom keptTwo ⬝ᵥ design.atom insertLabel)
              * (design.atom keptTwo ⬝ᵥ planar)) ^ 2 := by
  by_contra hnoWitness
  push Not at hnoWitness
  exact htie.2 ({keptOne, keptTwo, insertLabel} : Finset (Fin size)) hcard
    (posDef_insertCompletion_of_insertPlaneGate design hneKepts hneOneInsert
      hneTwoInsert hinsertHeavy
      (fun planar hplanarOrth hplanarNe => hnoWitness planar hplanarOrth hplanarNe))

end Gtz
