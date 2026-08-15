import Gtz.Design.CoverageRefuters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The row certificate atlas

Every unsigned cell matrix is a symmetric Z-matrix: the diagonal carries the
budget floors and every off-diagonal entry is minus a sum of masses.  For such
a matrix one positive vector with three strict row inequalities gives all
three leading minors.  The engine is one forest identity: the doubly scaled
matrix is a diagonal of cleared row sums plus a triangle Laplacian, and its
determinant is the matrix-tree forest sum, a polynomial with no negative term.

The module lands the scalar bridge, the row form of the master criterion, the
seven missing path cells (after which all sixteen spanning trees carry
moduli-only cells), the row corollary at the pendant tree with the second
coverage refuter as its witness, the subset pigeonhole for weights, and the
membership lemmas.  A cell hypothesis is now three LINEAR inequalities in the
moduli for each fixed integer certificate vector, so an atlas case is a
polyhedron.
-/

namespace Gtz

open Matrix Finset

/-! ## The scalar bridge: rows to minors -/

/-- **THE ROW CERTIFICATE BRIDGE.**  A symmetric `3x3` matrix with nonpositive
off-diagonal entries and one positive vector with three strict row readings
has positive leading minors.  The proof clears every division: the doubly
scaled matrix is a diagonal of positive cleared row sums plus a triangle
Laplacian, and the matrix-tree forest sum shows each scaled minor as a
polynomial with no negative term. -/
theorem unsignedMinors_of_rowCertificate
    {entryAA entryAB entryAC entryBB entryBC entryCC xA xB xC : ℝ}
    (hAB : entryAB ≤ 0) (hAC : entryAC ≤ 0) (hBC : entryBC ≤ 0)
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : 0 < entryAA * xA + entryAB * xB + entryAC * xC)
    (hrowB : 0 < entryAB * xA + entryBB * xB + entryBC * xC)
    (hrowC : 0 < entryAC * xA + entryBC * xB + entryCC * xC) :
    0 < entryAA ∧
      0 < entryAA * entryBB - entryAB ^ 2 ∧
      0 < entryAA * entryBB * entryCC - entryAA * entryBC ^ 2
        - entryAB ^ 2 * entryCC + 2 * entryAB * entryAC * entryBC
        - entryAC ^ 2 * entryBB := by
  have hsA : 0 < xA * (entryAA * xA + entryAB * xB + entryAC * xC) :=
    mul_pos hxA hrowA
  have hsB : 0 < xB * (entryAB * xA + entryBB * xB + entryBC * xC) :=
    mul_pos hxB hrowB
  have hsC : 0 < xC * (entryAC * xA + entryBC * xB + entryCC * xC) :=
    mul_pos hxC hrowC
  have hPc : 0 ≤ -entryAB * (xA * xB) :=
    mul_nonneg (neg_nonneg.mpr hAB) (mul_pos hxA hxB).le
  have hQc : 0 ≤ -entryAC * (xA * xC) :=
    mul_nonneg (neg_nonneg.mpr hAC) (mul_pos hxA hxC).le
  have hRc : 0 ≤ -entryBC * (xB * xC) :=
    mul_nonneg (neg_nonneg.mpr hBC) (mul_pos hxB hxC).le
  refine ⟨?_, ?_, ?_⟩
  · have key : xA ^ 2 * entryAA
        = xA * (entryAA * xA + entryAB * xB + entryAC * xC)
          + -entryAB * (xA * xB) + -entryAC * (xA * xC) := by ring
    nlinarith [key, hsA, hPc, hQc, pow_pos hxA 2]
  · have key : (xA * xB) ^ 2 * (entryAA * entryBB - entryAB ^ 2)
        = xA * (entryAA * xA + entryAB * xB + entryAC * xC)
            * (xB * (entryAB * xA + entryBB * xB + entryBC * xC))
          + xA * (entryAA * xA + entryAB * xB + entryAC * xC)
              * (-entryAB * (xA * xB) + -entryBC * (xB * xC))
          + xB * (entryAB * xA + entryBB * xB + entryBC * xC)
              * (-entryAB * (xA * xB) + -entryAC * (xA * xC))
          + (-entryAB * (xA * xB) * (-entryAC * (xA * xC))
            + -entryAB * (xA * xB) * (-entryBC * (xB * xC))
            + -entryAC * (xA * xC) * (-entryBC * (xB * xC))) := by ring
    have hchain : 0 < (xA * xB) ^ 2 * (entryAA * entryBB - entryAB ^ 2) := by
      rw [key]
      have hone := mul_pos hsA hsB
      have htwo := mul_nonneg hsA.le (add_nonneg hPc hRc)
      have hthree := mul_nonneg hsB.le (add_nonneg hPc hQc)
      have hfour := mul_nonneg hPc hQc
      have hfive := mul_nonneg hPc hRc
      have hsix := mul_nonneg hQc hRc
      linarith
    nlinarith [hchain, pow_pos (mul_pos hxA hxB) 2]
  · have key : (xA * xB * xC) ^ 2
        * (entryAA * entryBB * entryCC - entryAA * entryBC ^ 2
          - entryAB ^ 2 * entryCC + 2 * entryAB * entryAC * entryBC
          - entryAC ^ 2 * entryBB)
        = xA * (entryAA * xA + entryAB * xB + entryAC * xC)
            * (xB * (entryAB * xA + entryBB * xB + entryBC * xC))
            * (xC * (entryAC * xA + entryBC * xB + entryCC * xC))
          + xA * (entryAA * xA + entryAB * xB + entryAC * xC)
              * (xB * (entryAB * xA + entryBB * xB + entryBC * xC))
              * (-entryAC * (xA * xC) + -entryBC * (xB * xC))
          + xA * (entryAA * xA + entryAB * xB + entryAC * xC)
              * (xC * (entryAC * xA + entryBC * xB + entryCC * xC))
              * (-entryAB * (xA * xB) + -entryBC * (xB * xC))
          + xB * (entryAB * xA + entryBB * xB + entryBC * xC)
              * (xC * (entryAC * xA + entryBC * xB + entryCC * xC))
              * (-entryAB * (xA * xB) + -entryAC * (xA * xC))
          + (xA * (entryAA * xA + entryAB * xB + entryAC * xC)
              + xB * (entryAB * xA + entryBB * xB + entryBC * xC)
              + xC * (entryAC * xA + entryBC * xB + entryCC * xC))
            * (-entryAB * (xA * xB) * (-entryAC * (xA * xC))
              + -entryAB * (xA * xB) * (-entryBC * (xB * xC))
              + -entryAC * (xA * xC) * (-entryBC * (xB * xC))) := by ring
    have hchain : 0 < (xA * xB * xC) ^ 2
        * (entryAA * entryBB * entryCC - entryAA * entryBC ^ 2
          - entryAB ^ 2 * entryCC + 2 * entryAB * entryAC * entryBC
          - entryAC ^ 2 * entryBB) := by
      rw [key]
      have hone := mul_pos (mul_pos hsA hsB) hsC
      have htwo := mul_nonneg (mul_pos hsA hsB).le (add_nonneg hQc hRc)
      have hthree := mul_nonneg (mul_pos hsA hsC).le (add_nonneg hPc hRc)
      have hfour := mul_nonneg (mul_pos hsB hsC).le (add_nonneg hPc hQc)
      have hfive := mul_nonneg
        (by linarith : (0:ℝ) ≤ xA * (entryAA * xA + entryAB * xB + entryAC * xC)
          + xB * (entryAB * xA + entryBB * xB + entryBC * xC)
          + xC * (entryAC * xA + entryBC * xB + entryCC * xC))
        (add_nonneg (add_nonneg (mul_nonneg hPc hQc) (mul_nonneg hPc hRc))
          (mul_nonneg hQc hRc))
      linarith
    nlinarith [hchain, pow_pos (mul_pos (mul_pos hxA hxB) hxC) 2]

/-! ## The row form of the master criterion -/

/-- **THE UNSIGNED CYCLE ROW CRITERION.**  The master criterion with the three
minors replaced by one positive certificate vector and three strict row
inequalities, all LINEAR in the moduli for a fixed vector.  The bridge
recovers the minors, so no allocation and no determinant appears in a cell
hypothesis. -/
theorem posDef_directionChartGap_of_unsignedCycleRows
    (direction : Fin 6 → (Fin 3 → ℝ)) (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {selA selB selC outA outB outC : Fin 6}
    (huniv : ({selA, selB, selC, outA, outB, outC} : Finset (Fin 6)) = Finset.univ)
    (hAB : selA ≠ selB) (hAC : selA ≠ selC) (hBC : selB ≠ selC)
    (hAoA : selA ≠ outA) (hAoB : selA ≠ outB) (hAoC : selA ≠ outC)
    (hBoA : selB ≠ outA) (hBoB : selB ≠ outB) (hBoC : selB ≠ outC)
    (hCoA : selC ≠ outA) (hCoB : selC ≠ outB) (hCoC : selC ≠ outC)
    (hoAB : outA ≠ outB) (hoAC : outA ≠ outC) (hoBC : outB ≠ outC)
    (hspan : ∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0)
    {scaleA scaleB scaleC : ℝ}
    (hscaleA : scaleA ≠ 0) (hscaleB : scaleB ≠ 0) (hscaleC : scaleC ≠ 0)
    {eAA eAB eAC eBA eBB eBC eCA eCB eCC : ℝ}
    (hexpA : scaleA • direction outA
      = eAA • direction selA + eAB • direction selB + eAC • direction selC)
    (hexpB : scaleB • direction outB
      = eBA • direction selA + eBB • direction selB + eBC • direction selC)
    (hexpC : scaleC • direction outC
      = eCA • direction selA + eCB • direction selB + eCC • direction selC)
    {fAA fAB fAC fBA fBB fBC fCA fCB fCC : ℝ}
    (hfAA : |eAA| ≤ fAA) (hfAB : |eAB| ≤ fAB) (hfAC : |eAC| ≤ fAC)
    (hfBA : |eBA| ≤ fBA) (hfBB : |eBB| ≤ fBB) (hfBC : |eBC| ≤ fBC)
    (hfCA : |eCA| ≤ fCA) (hfCB : |eCB| ≤ fCB) (hfCC : |eCC| ≤ fCC)
    {demandA demandB demandC floorA floorB floorC : ℝ}
    (hdemandA : mass outA ≤ demandA * scaleA ^ 2)
    (hdemandB : mass outB ≤ demandB * scaleB ^ 2)
    (hdemandC : mass outC ≤ demandC * scaleC ^ 2)
    (hfloorA : floorA * weight selA ≤ mass selA * (1 - weight selA))
    (hfloorB : floorB * weight selB ≤ mass selB * (1 - weight selB))
    (hfloorC : floorC * weight selC ≤ mass selC * (1 - weight selC))
    {entryAA entryAB entryAC entryBB entryBC entryCC : ℝ}
    (hentryAA : entryAA
      = floorA - (demandA * fAA ^ 2 + demandB * fBA ^ 2 + demandC * fCA ^ 2))
    (hentryBB : entryBB
      = floorB - (demandA * fAB ^ 2 + demandB * fBB ^ 2 + demandC * fCB ^ 2))
    (hentryCC : entryCC
      = floorC - (demandA * fAC ^ 2 + demandB * fBC ^ 2 + demandC * fCC ^ 2))
    (hentryAB : entryAB
      = -(demandA * fAA * fAB + demandB * fBA * fBB + demandC * fCA * fCB))
    (hentryAC : entryAC
      = -(demandA * fAA * fAC + demandB * fBA * fBC + demandC * fCA * fCC))
    (hentryBC : entryBC
      = -(demandA * fAB * fAC + demandB * fBB * fBC + demandC * fCB * fCC))
    {xA xB xC : ℝ} (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : 0 < entryAA * xA + entryAB * xB + entryAC * xC)
    (hrowB : 0 < entryAB * xA + entryBB * xB + entryBC * xC)
    (hrowC : 0 < entryAC * xA + entryBC * xB + entryCC * xC) :
    (directionChartGap direction mass weight {selA, selB, selC}).PosDef := by
  have hdemandOf : ∀ (demand scale : ℝ) (outLabel : Fin 6), scale ≠ 0 →
      mass outLabel ≤ demand * scale ^ 2 → 0 ≤ demand := by
    intro demand scale outLabel hscale hdemand
    have hchain : (0 : ℝ) < demand * scale ^ 2 := (hmass outLabel).trans_le hdemand
    rcases mul_pos_iff.mp hchain with ⟨hpos, _⟩ | ⟨_, hneg⟩
    · exact hpos.le
    · exact absurd (by positivity : (0:ℝ) < scale ^ 2) (not_lt.mpr hneg.le)
  have hdA := hdemandOf demandA scaleA outA hscaleA hdemandA
  have hdB := hdemandOf demandB scaleB outB hscaleB hdemandB
  have hdC := hdemandOf demandC scaleC outC hscaleC hdemandC
  have hfAAnn : 0 ≤ fAA := (abs_nonneg _).trans hfAA
  have hfABnn : 0 ≤ fAB := (abs_nonneg _).trans hfAB
  have hfACnn : 0 ≤ fAC := (abs_nonneg _).trans hfAC
  have hfBAnn : 0 ≤ fBA := (abs_nonneg _).trans hfBA
  have hfBBnn : 0 ≤ fBB := (abs_nonneg _).trans hfBB
  have hfBCnn : 0 ≤ fBC := (abs_nonneg _).trans hfBC
  have hfCAnn : 0 ≤ fCA := (abs_nonneg _).trans hfCA
  have hfCBnn : 0 ≤ fCB := (abs_nonneg _).trans hfCB
  have hfCCnn : 0 ≤ fCC := (abs_nonneg _).trans hfCC
  have hABle : entryAB ≤ 0 := by
    rw [hentryAB]
    have := add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hdA hfAAnn) hfABnn)
      (mul_nonneg (mul_nonneg hdB hfBAnn) hfBBnn))
      (mul_nonneg (mul_nonneg hdC hfCAnn) hfCBnn)
    linarith
  have hACle : entryAC ≤ 0 := by
    rw [hentryAC]
    have := add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hdA hfAAnn) hfACnn)
      (mul_nonneg (mul_nonneg hdB hfBAnn) hfBCnn))
      (mul_nonneg (mul_nonneg hdC hfCAnn) hfCCnn)
    linarith
  have hBCle : entryBC ≤ 0 := by
    rw [hentryBC]
    have := add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg hdA hfABnn) hfACnn)
      (mul_nonneg (mul_nonneg hdB hfBBnn) hfBCnn))
      (mul_nonneg (mul_nonneg hdC hfCBnn) hfCCnn)
    linarith
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ := unsignedMinors_of_rowCertificate
    hABle hACle hBCle hxA hxB hxC hrowA hrowB hrowC
  exact posDef_directionChartGap_of_unsignedCycleMinors direction mass weight
    hmass hweight huniv hAB hAC hBC hAoA hAoB hAoC hBoA hBoB hBoC hCoA hCoB hCoC
    hoAB hoAC hoBC hspan hscaleA hscaleB hscaleC hexpA hexpB hexpC
    hfAA hfAB hfAC hfBA hfBB hfBC hfCA hfCB hfCC
    hdemandA hdemandB hdemandC hfloorA hfloorB hfloorC
    hentryAA hentryBB hentryCC hentryAB hentryAC hentryBC
    hcorner hminorTwo hminorDet

/-! ## The seven missing fundamental-cycle expansions -/

/-- Edge `2 = bc` in the path tree `{0, 1, 5}`. -/
theorem kFour_expansion_zeroOneFive_two :
    (1 : ℝ) • kFourDirection 2
      = (-1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 1
        + (0 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the path tree `{0, 1, 5}`. -/
theorem kFour_expansion_zeroOneFive_three :
    (1 : ℝ) • kFourDirection 3
      = (0 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 1
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the path tree `{0, 1, 5}`. -/
theorem kFour_expansion_zeroOneFive_four :
    (1 : ℝ) • kFourDirection 4
      = (-1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 1
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `1 = ac` in the path tree `{0, 2, 5}`. -/
theorem kFour_expansion_zeroTwoFive_one :
    (1 : ℝ) • kFourDirection 1
      = (1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 2
        + (0 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the path tree `{0, 2, 5}`. -/
theorem kFour_expansion_zeroTwoFive_three :
    (1 : ℝ) • kFourDirection 3
      = (1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the path tree `{0, 2, 5}`. -/
theorem kFour_expansion_zeroTwoFive_four :
    (1 : ℝ) • kFourDirection 4
      = (0 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `1 = ac` in the path tree `{0, 3, 5}`. -/
theorem kFour_expansion_zeroThreeFive_one :
    (1 : ℝ) • kFourDirection 1
      = (0 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 3
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `2 = bc` in the path tree `{0, 3, 5}`. -/
theorem kFour_expansion_zeroThreeFive_two :
    (1 : ℝ) • kFourDirection 2
      = (-1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 3
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the path tree `{0, 3, 5}`. -/
theorem kFour_expansion_zeroThreeFive_four :
    (1 : ℝ) • kFourDirection 4
      = (-1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 3
        + (0 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `1 = ac` in the path tree `{0, 4, 5}`. -/
theorem kFour_expansion_zeroFourFive_one :
    (1 : ℝ) • kFourDirection 1
      = (1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 4
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `2 = bc` in the path tree `{0, 4, 5}`. -/
theorem kFour_expansion_zeroFourFive_two :
    (1 : ℝ) • kFourDirection 2
      = (0 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 4
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the path tree `{0, 4, 5}`. -/
theorem kFour_expansion_zeroFourFive_three :
    (1 : ℝ) • kFourDirection 3
      = (1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 4
        + (0 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `2 = bc` in the path tree `{0, 1, 4}`. -/
theorem kFour_expansion_zeroOneFour_two :
    (1 : ℝ) • kFourDirection 2
      = (-1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 1
        + (0 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the path tree `{0, 1, 4}`. -/
theorem kFour_expansion_zeroOneFour_three :
    (1 : ℝ) • kFourDirection 3
      = (1 : ℝ) • kFourDirection 0 + (0 : ℝ) • kFourDirection 1
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the path tree `{0, 1, 4}`. -/
theorem kFour_expansion_zeroOneFour_five :
    (1 : ℝ) • kFourDirection 5
      = (1 : ℝ) • kFourDirection 0 + (-1 : ℝ) • kFourDirection 1
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `0 = ab` in the path tree `{1, 2, 4}`. -/
theorem kFour_expansion_oneTwoFour_zero :
    (1 : ℝ) • kFourDirection 0
      = (1 : ℝ) • kFourDirection 1 + (-1 : ℝ) • kFourDirection 2
        + (0 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the path tree `{1, 2, 4}`. -/
theorem kFour_expansion_oneTwoFour_three :
    (1 : ℝ) • kFourDirection 3
      = (1 : ℝ) • kFourDirection 1 + (-1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the path tree `{1, 2, 4}`. -/
theorem kFour_expansion_oneTwoFour_five :
    (1 : ℝ) • kFourDirection 5
      = (0 : ℝ) • kFourDirection 1 + (-1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `0 = ab` in the path tree `{1, 4, 5}`. -/
theorem kFour_expansion_oneFourFive_zero :
    (1 : ℝ) • kFourDirection 0
      = (1 : ℝ) • kFourDirection 1 + (-1 : ℝ) • kFourDirection 4
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `2 = bc` in the path tree `{1, 4, 5}`. -/
theorem kFour_expansion_oneFourFive_two :
    (1 : ℝ) • kFourDirection 2
      = (0 : ℝ) • kFourDirection 1 + (1 : ℝ) • kFourDirection 4
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the path tree `{1, 4, 5}`. -/
theorem kFour_expansion_oneFourFive_three :
    (1 : ℝ) • kFourDirection 3
      = (1 : ℝ) • kFourDirection 1 + (0 : ℝ) • kFourDirection 4
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-! ## The seven missing path cells -/

/-- **The path cell at `{0, 1, 5}`.** -/
theorem posDef_kFour_pathCell_zeroOneFive (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorOne floorFive : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorZero - (mass 2 + mass 4))
    (hminorTwo : 0 < (floorZero - (mass 2 + mass 4))
      * (floorOne - (mass 2 + mass 3 + mass 4)) - (mass 2 + mass 4) ^ 2)
    (hminorDet : 0 < (floorZero - (mass 2 + mass 4))
        * (floorOne - (mass 2 + mass 3 + mass 4)) * (floorFive - (mass 3 + mass 4))
      - (floorZero - (mass 2 + mass 4)) * (mass 3 + mass 4) ^ 2
      - (mass 2 + mass 4) ^ 2 * (floorFive - (mass 3 + mass 4))
      + 2 * (-(mass 2 + mass 4)) * (-(mass 4)) * (-(mass 3 + mass 4))
      - mass 4 ^ 2 * (floorOne - (mass 2 + mass 3 + mass 4))) :
    (directionChartGap kFourDirection mass weight
      ({0, 1, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 1) (selC := 5) (outA := 2) (outB := 3) (outC := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_zeroOneFive_two kFour_expansion_zeroOneFive_three
    kFour_expansion_zeroOneFive_four
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 0) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 2) (demandB := mass 3) (demandC := mass 4)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorOne hfloorFive
    (entryAA := floorZero - (mass 2 + mass 4))
    (entryBB := floorOne - (mass 2 + mass 3 + mass 4))
    (entryCC := floorFive - (mass 3 + mass 4))
    (entryAB := -(mass 2 + mass 4)) (entryAC := -(mass 4))
    (entryBC := -(mass 3 + mass 4))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The path cell at `{0, 2, 5}`.** -/
theorem posDef_kFour_pathCell_zeroTwoFive (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorTwo floorFive : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorZero - (mass 1 + mass 3))
    (hminorTwo : 0 < (floorZero - (mass 1 + mass 3))
      * (floorTwo - (mass 1 + mass 3 + mass 4)) - (mass 1 + mass 3) ^ 2)
    (hminorDet : 0 < (floorZero - (mass 1 + mass 3))
        * (floorTwo - (mass 1 + mass 3 + mass 4)) * (floorFive - (mass 3 + mass 4))
      - (floorZero - (mass 1 + mass 3)) * (mass 3 + mass 4) ^ 2
      - (mass 1 + mass 3) ^ 2 * (floorFive - (mass 3 + mass 4))
      + 2 * (-(mass 1 + mass 3)) * (-(mass 3)) * (-(mass 3 + mass 4))
      - mass 3 ^ 2 * (floorTwo - (mass 1 + mass 3 + mass 4))) :
    (directionChartGap kFourDirection mass weight
      ({0, 2, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 2) (selC := 5) (outA := 1) (outB := 3) (outC := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_zeroTwoFive_one kFour_expansion_zeroTwoFive_three
    kFour_expansion_zeroTwoFive_four
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 1) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 1) (demandB := mass 3) (demandC := mass 4)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorTwo hfloorFive
    (entryAA := floorZero - (mass 1 + mass 3))
    (entryBB := floorTwo - (mass 1 + mass 3 + mass 4))
    (entryCC := floorFive - (mass 3 + mass 4))
    (entryAB := -(mass 1 + mass 3)) (entryAC := -(mass 3))
    (entryBC := -(mass 3 + mass 4))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The path cell at `{0, 3, 5}`.** -/
theorem posDef_kFour_pathCell_zeroThreeFive (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorThree floorFive : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorZero - (mass 2 + mass 4))
    (hminorTwo : 0 < (floorZero - (mass 2 + mass 4))
      * (floorThree - (mass 1 + mass 2 + mass 4)) - (mass 2 + mass 4) ^ 2)
    (hminorDet : 0 < (floorZero - (mass 2 + mass 4))
        * (floorThree - (mass 1 + mass 2 + mass 4)) * (floorFive - (mass 1 + mass 2))
      - (floorZero - (mass 2 + mass 4)) * (mass 1 + mass 2) ^ 2
      - (mass 2 + mass 4) ^ 2 * (floorFive - (mass 1 + mass 2))
      + 2 * (-(mass 2 + mass 4)) * (-(mass 2)) * (-(mass 1 + mass 2))
      - mass 2 ^ 2 * (floorThree - (mass 1 + mass 2 + mass 4))) :
    (directionChartGap kFourDirection mass weight
      ({0, 3, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 3) (selC := 5) (outA := 1) (outB := 2) (outC := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_zeroThreeFive_one kFour_expansion_zeroThreeFive_two
    kFour_expansion_zeroThreeFive_four
    (fAA := 0) (fAB := 1) (fAC := 1) (fBA := 1) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 1) (demandB := mass 2) (demandC := mass 4)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorThree hfloorFive
    (entryAA := floorZero - (mass 2 + mass 4))
    (entryBB := floorThree - (mass 1 + mass 2 + mass 4))
    (entryCC := floorFive - (mass 1 + mass 2))
    (entryAB := -(mass 2 + mass 4)) (entryAC := -(mass 2))
    (entryBC := -(mass 1 + mass 2))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The path cell at `{0, 4, 5}`.** -/
theorem posDef_kFour_pathCell_zeroFourFive (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorFour floorFive : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorZero - (mass 1 + mass 3))
    (hminorTwo : 0 < (floorZero - (mass 1 + mass 3))
      * (floorFour - (mass 1 + mass 2 + mass 3)) - (mass 1 + mass 3) ^ 2)
    (hminorDet : 0 < (floorZero - (mass 1 + mass 3))
        * (floorFour - (mass 1 + mass 2 + mass 3)) * (floorFive - (mass 1 + mass 2))
      - (floorZero - (mass 1 + mass 3)) * (mass 1 + mass 2) ^ 2
      - (mass 1 + mass 3) ^ 2 * (floorFive - (mass 1 + mass 2))
      + 2 * (-(mass 1 + mass 3)) * (-(mass 1)) * (-(mass 1 + mass 2))
      - mass 1 ^ 2 * (floorFour - (mass 1 + mass 2 + mass 3))) :
    (directionChartGap kFourDirection mass weight
      ({0, 4, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 4) (selC := 5) (outA := 1) (outB := 2) (outC := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_zeroFourFive_one kFour_expansion_zeroFourFive_two
    kFour_expansion_zeroFourFive_three
    (fAA := 1) (fAB := 1) (fAC := 1) (fBA := 0) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 1) (demandB := mass 2) (demandC := mass 3)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorFour hfloorFive
    (entryAA := floorZero - (mass 1 + mass 3))
    (entryBB := floorFour - (mass 1 + mass 2 + mass 3))
    (entryCC := floorFive - (mass 1 + mass 2))
    (entryAB := -(mass 1 + mass 3)) (entryAC := -(mass 1))
    (entryBC := -(mass 1 + mass 2))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The path cell at `{0, 1, 4}`.** -/
theorem posDef_kFour_pathCell_zeroOneFour (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorOne floorFour : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hcorner : 0 < floorZero - (mass 2 + mass 3 + mass 5))
    (hminorTwo : 0 < (floorZero - (mass 2 + mass 3 + mass 5))
      * (floorOne - (mass 2 + mass 5)) - (mass 2 + mass 5) ^ 2)
    (hminorDet : 0 < (floorZero - (mass 2 + mass 3 + mass 5))
        * (floorOne - (mass 2 + mass 5)) * (floorFour - (mass 3 + mass 5))
      - (floorZero - (mass 2 + mass 3 + mass 5)) * mass 5 ^ 2
      - (mass 2 + mass 5) ^ 2 * (floorFour - (mass 3 + mass 5))
      + 2 * (-(mass 2 + mass 5)) * (-(mass 3 + mass 5)) * (-(mass 5))
      - (mass 3 + mass 5) ^ 2 * (floorOne - (mass 2 + mass 5))) :
    (directionChartGap kFourDirection mass weight
      ({0, 1, 4} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 1) (selC := 4) (outA := 2) (outB := 3) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_zeroOneFour_two kFour_expansion_zeroOneFour_three
    kFour_expansion_zeroOneFour_five
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 2) (demandB := mass 3) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorOne hfloorFour
    (entryAA := floorZero - (mass 2 + mass 3 + mass 5))
    (entryBB := floorOne - (mass 2 + mass 5))
    (entryCC := floorFour - (mass 3 + mass 5))
    (entryAB := -(mass 2 + mass 5)) (entryAC := -(mass 3 + mass 5))
    (entryBC := -(mass 5))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The path cell at `{1, 2, 4}`.** -/
theorem posDef_kFour_pathCell_oneTwoFour (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorOne floorTwo floorFour : ℝ}
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hcorner : 0 < floorOne - (mass 0 + mass 3))
    (hminorTwo : 0 < (floorOne - (mass 0 + mass 3))
      * (floorTwo - (mass 0 + mass 3 + mass 5)) - (mass 0 + mass 3) ^ 2)
    (hminorDet : 0 < (floorOne - (mass 0 + mass 3))
        * (floorTwo - (mass 0 + mass 3 + mass 5)) * (floorFour - (mass 3 + mass 5))
      - (floorOne - (mass 0 + mass 3)) * (mass 3 + mass 5) ^ 2
      - (mass 0 + mass 3) ^ 2 * (floorFour - (mass 3 + mass 5))
      + 2 * (-(mass 0 + mass 3)) * (-(mass 3)) * (-(mass 3 + mass 5))
      - mass 3 ^ 2 * (floorTwo - (mass 0 + mass 3 + mass 5))) :
    (directionChartGap kFourDirection mass weight
      ({1, 2, 4} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 1) (selB := 2) (selC := 4) (outA := 0) (outB := 3) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_oneTwoFour_zero kFour_expansion_oneTwoFour_three
    kFour_expansion_oneTwoFour_five
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 1) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 3) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorOne hfloorTwo hfloorFour
    (entryAA := floorOne - (mass 0 + mass 3))
    (entryBB := floorTwo - (mass 0 + mass 3 + mass 5))
    (entryCC := floorFour - (mass 3 + mass 5))
    (entryAB := -(mass 0 + mass 3)) (entryAC := -(mass 3))
    (entryBC := -(mass 3 + mass 5))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The path cell at `{1, 4, 5}`.** -/
theorem posDef_kFour_pathCell_oneFourFive (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorOne floorFour floorFive : ℝ}
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorOne - (mass 0 + mass 3))
    (hminorTwo : 0 < (floorOne - (mass 0 + mass 3))
      * (floorFour - (mass 0 + mass 2)) - mass 0 ^ 2)
    (hminorDet : 0 < (floorOne - (mass 0 + mass 3))
        * (floorFour - (mass 0 + mass 2)) * (floorFive - (mass 0 + mass 2 + mass 3))
      - (floorOne - (mass 0 + mass 3)) * (mass 0 + mass 2) ^ 2
      - mass 0 ^ 2 * (floorFive - (mass 0 + mass 2 + mass 3))
      + 2 * (-(mass 0)) * (-(mass 0 + mass 3)) * (-(mass 0 + mass 2))
      - (mass 0 + mass 3) ^ 2 * (floorFour - (mass 0 + mass 2))) :
    (directionChartGap kFourDirection mass weight
      ({1, 4, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 1) (selB := 4) (selC := 5) (outA := 0) (outB := 2) (outC := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_oneFourFive_zero kFour_expansion_oneFourFive_two
    kFour_expansion_oneFourFive_three
    (fAA := 1) (fAB := 1) (fAC := 1) (fBA := 0) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 0) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 2) (demandC := mass 3)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorOne hfloorFour hfloorFive
    (entryAA := floorOne - (mass 0 + mass 3))
    (entryBB := floorFour - (mass 0 + mass 2))
    (entryCC := floorFive - (mass 0 + mass 2 + mass 3))
    (entryAB := -(mass 0)) (entryAC := -(mass 0 + mass 3))
    (entryBC := -(mass 0 + mass 2))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-! ## The row corollary at the pendant tree, and its refuter witness -/

/-- **The pendant row cell at `{1, 2, 3}`.**  One positive vector and three
LINEAR inequalities in the moduli replace the three minors. -/
theorem posDef_kFour_pendantCell_oneTwoThree_ofRows (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorOne floorTwo floorThree xA xB xC : ℝ}
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : 0 < (floorOne - (mass 0 + mass 4 + mass 5)) * xA
      + (-(mass 0 + mass 4)) * xB + (-(mass 4 + mass 5)) * xC)
    (hrowB : 0 < (-(mass 0 + mass 4)) * xA
      + (floorTwo - (mass 0 + mass 4)) * xB + (-(mass 4)) * xC)
    (hrowC : 0 < (-(mass 4 + mass 5)) * xA
      + (-(mass 4)) * xB + (floorThree - (mass 4 + mass 5)) * xC) :
    (directionChartGap kFourDirection mass weight
      ({1, 2, 3} : Finset (Fin 6))).PosDef := by
  have hABle : -(mass 0 + mass 4) ≤ 0 := by
    have := (hmass 0).le; have := (hmass 4).le; linarith
  have hACle : -(mass 4 + mass 5) ≤ 0 := by
    have := (hmass 4).le; have := (hmass 5).le; linarith
  have hBCle : -(mass 4) ≤ 0 := by have := (hmass 4).le; linarith
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ := unsignedMinors_of_rowCertificate
    hABle hACle hBCle hxA hxB hxC hrowA hrowB hrowC
  refine posDef_kFour_pendantCell_oneTwoThree mass weight hmass hweight
    hfloorOne hfloorTwo hfloorThree hcorner
    (by ring_nf; ring_nf at hminorTwo; exact hminorTwo) ?_
  ring_nf
  ring_nf at hminorDet
  exact hminorDet

/-- **The second refuter carries a row certificate.**  At the interior point
that kills every star, the pendant tree fires from the vector `(8, 5, 1)`
through three rational row readings `22/105`, `29/70`, `227/15`.  The row
engine decides where the star cells and the trace cells are silent. -/
theorem coverageRefuterTwo_pendant_rowCertificate :
    (directionChartGap kFourDirection coverageRefuterTwoMass
      coverageRefuterTwoWeight ({1, 2, 3} : Finset (Fin 6))).PosDef := by
  refine posDef_kFour_pendantCell_oneTwoThree_ofRows coverageRefuterTwoMass
    coverageRefuterTwoWeight
    (fun label => by fin_cases label <;> norm_num [coverageRefuterTwoMass])
    (fun label => by fin_cases label <;> norm_num [coverageRefuterTwoWeight])
    (floorOne := 253 / 105) (floorTwo := 667 / 210) (floorThree := 29)
    (xA := 8) (xB := 5) (xC := 1) ?_ ?_ ?_ (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_ ?_ <;>
  norm_num [coverageRefuterTwoMass, coverageRefuterTwoWeight]

/-! ## The subset pigeonhole for chart weights -/

/-- **The subset pigeonhole.**  Chart weights sum to one, so every nonempty
label set contains a label with weight at most the reciprocal of the set
cardinality.  The heavy-label law is the full-set instance; the case atlas
reads it on tree and matching supports. -/
theorem directionChartPoint_exists_subset_light (point : DirectionChartPoint 6)
    {S : Finset (Fin 6)} (hS : S.Nonempty) :
    ∃ label ∈ S, (S.card : ℝ) * point.weight label ≤ 1 := by
  by_contra hall
  push Not at hall
  have hsub : ∑ label ∈ S, point.weight label ≤ 1 := by
    rw [← point.weight_sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      fun label _ _ => (point.weight_pos label).le
  have hlt : ∑ _label ∈ S, (1 : ℝ)
      < ∑ label ∈ S, (S.card : ℝ) * point.weight label :=
    Finset.sum_lt_sum_of_nonempty hS fun label hmem => hall label hmem
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hlt
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hsub hcard]

/-! ## The seven membership lemmas -/

/-- The path tree `{0, 1, 5}` is a spanning tree. -/
theorem pathTree_zeroOneFive_mem :
    ({0, 1, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The path tree `{0, 2, 5}` is a spanning tree. -/
theorem pathTree_zeroTwoFive_mem :
    ({0, 2, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The path tree `{0, 3, 5}` is a spanning tree. -/
theorem pathTree_zeroThreeFive_mem :
    ({0, 3, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The path tree `{0, 4, 5}` is a spanning tree. -/
theorem pathTree_zeroFourFive_mem :
    ({0, 4, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The path tree `{0, 1, 4}` is a spanning tree. -/
theorem pathTree_zeroOneFour_mem :
    ({0, 1, 4} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The path tree `{1, 2, 4}` is a spanning tree. -/
theorem pathTree_oneTwoFour_mem :
    ({1, 2, 4} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The path tree `{1, 4, 5}` is a spanning tree. -/
theorem pathTree_oneFourFive_mem :
    ({1, 4, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

end Gtz
