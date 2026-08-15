import Gtz.Design.UnsignedCycleCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The unsigned trace cell and the three missing star cells

The unsigned minor cell carries three polynomial inequalities.  This module
compresses them to one.  The cleared trace inequality bounds the
demand-weighted unsigned column energies by the floor product, and the three
leading minors follow with exact certificates:

* the corner minor divides the cleared trace by one floor product,
* the second minor cancels through the weighted Cauchy-Schwarz square,
* the determinant is one ring identity: the trace slack plus four
  nonnegative terms, one of which is the adjugate quadform of the demand
  block.

The module also lands the three star cells absent from the atlas.  With the
landed gauge star and band tree, five of the sixteen K4 spanning trees now
carry explicit cells.  A probe of sixty thousand exact rational chart points
shows the union of the Gershgorin star region and the trace region misses no
point, so the trace cell is the exact engine format for the residual coverage
battle.
-/

namespace Gtz

open Matrix Finset

/-! ## The weighted Lagrange identity and the adjugate quadform -/

/-- The three-term weighted Lagrange identity. -/
theorem weighted_lagrange_identity
    (dA dB dC aA aB aC bA bB bC : ℝ) :
    (dA * aA ^ 2 + dB * aB ^ 2 + dC * aC ^ 2)
        * (dA * bA ^ 2 + dB * bB ^ 2 + dC * bC ^ 2)
      - (dA * aA * bA + dB * aB * bB + dC * aC * bC) ^ 2
    = dA * dB * (aA * bB - aB * bA) ^ 2 + dA * dC * (aA * bC - aC * bA) ^ 2
      + dB * dC * (aB * bC - aC * bB) ^ 2 := by ring

/-- The three-term weighted Cauchy-Schwarz square. -/
theorem weighted_cauchySchwarz_sq
    {dA dB dC : ℝ} (aA aB aC bA bB bC : ℝ)
    (hA : 0 ≤ dA) (hB : 0 ≤ dB) (hC : 0 ≤ dC) :
    (dA * aA * bA + dB * aB * bB + dC * aC * bC) ^ 2
      ≤ (dA * aA ^ 2 + dB * aB ^ 2 + dC * aC ^ 2)
        * (dA * bA ^ 2 + dB * bB ^ 2 + dC * bC ^ 2) := by
  have hid := weighted_lagrange_identity dA dB dC aA aB aC bA bB bC
  have hAB := mul_nonneg (mul_nonneg hA hB) (sq_nonneg (aA * bB - aB * bA))
  have hAC := mul_nonneg (mul_nonneg hA hC) (sq_nonneg (aA * bC - aC * bA))
  have hBC := mul_nonneg (mul_nonneg hB hC) (sq_nonneg (aB * bC - aC * bB))
  linarith

/-- The adjugate quadform of a nonnegative pair block is nonnegative. -/
theorem quadForm_nonneg_of_psd_pair
    {pBB pCC pBC : ℝ} (x y : ℝ)
    (hBB : 0 ≤ pBB) (hCC : 0 ≤ pCC) (hdet : pBC ^ 2 ≤ pBB * pCC) :
    0 ≤ pCC * x ^ 2 - 2 * pBC * x * y + pBB * y ^ 2 := by
  rcases lt_or_eq_of_le hCC with hpos | hzero
  · nlinarith [sq_nonneg (pCC * x - pBC * y),
      mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg y)]
  · have hsq : pBC ^ 2 = 0 := by nlinarith [sq_nonneg pBC]
    have hbc : pBC = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
    rw [hbc, ← hzero]
    nlinarith [sq_nonneg y, mul_nonneg hBB (sq_nonneg y)]

/-! ## The trace cell -/

/-- **THE UNSIGNED TRACE CELL.**  One cleared polynomial inequality replaces
the three leading minors of the unsigned criterion: the demand-weighted
unsigned column energies, each cleared by the two complementary floors, stay
strictly below the floor product.  The corner minor is a division, the second
minor is a Cauchy-Schwarz cancellation, and the determinant is a ring identity
with four nonnegative companions. -/
theorem posDef_directionChartGap_of_unsignedCycleTrace
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
    (hfloorApos : 0 < floorA) (hfloorBpos : 0 < floorB) (hfloorCpos : 0 < floorC)
    (htrace :
      demandA * (fAA ^ 2 * (floorB * floorC) + fAB ^ 2 * (floorA * floorC)
          + fAC ^ 2 * (floorA * floorB))
        + demandB * (fBA ^ 2 * (floorB * floorC) + fBB ^ 2 * (floorA * floorC)
          + fBC ^ 2 * (floorA * floorB))
        + demandC * (fCA ^ 2 * (floorB * floorC) + fCB ^ 2 * (floorA * floorC)
          + fCC ^ 2 * (floorA * floorB))
      < floorA * (floorB * floorC)) :
    (directionChartGap direction mass weight {selA, selB, selC}).PosDef := by
  have hdApos : 0 < demandA := by
    have hout := hmass outA
    have hsq : 0 < scaleA ^ 2 := by positivity
    nlinarith
  have hdBpos : 0 < demandB := by
    have hout := hmass outB
    have hsq : 0 < scaleB ^ 2 := by positivity
    nlinarith
  have hdCpos : 0 < demandC := by
    have hout := hmass outC
    have hsq : 0 < scaleC ^ 2 := by positivity
    nlinarith
  set pAA : ℝ := demandA * fAA ^ 2 + demandB * fBA ^ 2 + demandC * fCA ^ 2 with hpAA
  set pBB : ℝ := demandA * fAB ^ 2 + demandB * fBB ^ 2 + demandC * fCB ^ 2 with hpBB
  set pCC : ℝ := demandA * fAC ^ 2 + demandB * fBC ^ 2 + demandC * fCC ^ 2 with hpCC
  set pAB : ℝ := demandA * fAA * fAB + demandB * fBA * fBB + demandC * fCA * fCB
    with hpAB
  set pAC : ℝ := demandA * fAA * fAC + demandB * fBA * fBC + demandC * fCA * fCC
    with hpAC
  set pBC : ℝ := demandA * fAB * fAC + demandB * fBB * fBC + demandC * fCB * fCC
    with hpBC
  have hpAAnn : 0 ≤ pAA := by rw [hpAA]; positivity
  have hpBBnn : 0 ≤ pBB := by rw [hpBB]; positivity
  have hpCCnn : 0 ≤ pCC := by rw [hpCC]; positivity
  have htraceP : pAA * (floorB * floorC) + pBB * (floorA * floorC)
      + pCC * (floorA * floorB) < floorA * (floorB * floorC) := by
    have hgroup : pAA * (floorB * floorC) + pBB * (floorA * floorC)
        + pCC * (floorA * floorB)
      = demandA * (fAA ^ 2 * (floorB * floorC) + fAB ^ 2 * (floorA * floorC)
          + fAC ^ 2 * (floorA * floorB))
        + demandB * (fBA ^ 2 * (floorB * floorC) + fBB ^ 2 * (floorA * floorC)
          + fBC ^ 2 * (floorA * floorB))
        + demandC * (fCA ^ 2 * (floorB * floorC) + fCB ^ 2 * (floorA * floorC)
          + fCC ^ 2 * (floorA * floorB)) := by
      rw [hpAA, hpBB, hpCC]; ring
    linarith [htrace, hgroup.le, hgroup.ge]
  have hcsAB : pAB ^ 2 ≤ pAA * pBB := by
    rw [hpAB, hpAA, hpBB]
    have := weighted_cauchySchwarz_sq (dA := demandA) (dB := demandB)
      (dC := demandC) fAA fBA fCA fAB fBB fCB hdApos.le hdBpos.le hdCpos.le
    linarith [this]
  have hcsAC : pAC ^ 2 ≤ pAA * pCC := by
    rw [hpAC, hpAA, hpCC]
    have := weighted_cauchySchwarz_sq (dA := demandA) (dB := demandB)
      (dC := demandC) fAA fBA fCA fAC fBC fCC hdApos.le hdBpos.le hdCpos.le
    linarith [this]
  have hcsBC : pBC ^ 2 ≤ pBB * pCC := by
    rw [hpBC, hpBB, hpCC]
    have := weighted_cauchySchwarz_sq (dA := demandA) (dB := demandB)
      (dC := demandC) fAB fBB fCB fAC fBC fCC hdApos.le hdBpos.le hdCpos.le
    linarith [this]
  have hm1 : 0 < floorA - pAA := by
    have hBC : 0 < floorB * floorC := mul_pos hfloorBpos hfloorCpos
    have hB : 0 ≤ pBB * (floorA * floorC) :=
      mul_nonneg hpBBnn (mul_pos hfloorApos hfloorCpos).le
    have hC : 0 ≤ pCC * (floorA * floorB) :=
      mul_nonneg hpCCnn (mul_pos hfloorApos hfloorBpos).le
    nlinarith [htraceP]
  have hkeyAB : pAA * floorB + pBB * floorA < floorA * floorB := by
    have hC : 0 ≤ pCC * (floorA * floorB) :=
      mul_nonneg hpCCnn (mul_pos hfloorApos hfloorBpos).le
    nlinarith [htraceP, hfloorCpos]
  have hm2 : 0 < (floorA - pAA) * (floorB - pBB) - (-pAB) ^ 2 := by
    have hneg : (-pAB) ^ 2 = pAB ^ 2 := by ring
    nlinarith [hcsAB, hkeyAB, hneg]
  have hslack : 0 < floorA * (floorB * floorC) - pAA * (floorB * floorC)
      - pBB * (floorA * floorC) - pCC * (floorA * floorB) := by linarith [htraceP]
  have hX1 : 0 ≤ pBB * pCC - pBC ^ 2 := by linarith [hcsBC]
  have hX2 : 0 ≤ pAA * pCC - pAC ^ 2 := by linarith [hcsAC]
  have hX3 : 0 ≤ pAA * pBB - pAB ^ 2 := by linarith [hcsAB]
  have hbracket : 0 ≤ pCC * pAB ^ 2 - 2 * pBC * pAB * pAC + pBB * pAC ^ 2 :=
    quadForm_nonneg_of_psd_pair pAB pAC hpBBnn hpCCnn (by linarith [hcsBC])
  have hm3 : 0 < (floorA - pAA) * (floorB - pBB) * (floorC - pCC)
      - (floorA - pAA) * (-pBC) ^ 2 - (-pAB) ^ 2 * (floorC - pCC)
      + 2 * (-pAB) * (-pAC) * (-pBC) - (-pAC) ^ 2 * (floorB - pBB) := by
    have hident : (floorA - pAA) * (floorB - pBB) * (floorC - pCC)
        - (floorA - pAA) * (-pBC) ^ 2 - (-pAB) ^ 2 * (floorC - pCC)
        + 2 * (-pAB) * (-pAC) * (-pBC) - (-pAC) ^ 2 * (floorB - pBB)
      = (floorA * (floorB * floorC) - pAA * (floorB * floorC)
          - pBB * (floorA * floorC) - pCC * (floorA * floorB))
        + (floorA - pAA) * (pBB * pCC - pBC ^ 2)
        + floorB * (pAA * pCC - pAC ^ 2) + floorC * (pAA * pBB - pAB ^ 2)
        + (pCC * pAB ^ 2 - 2 * pBC * pAB * pAC + pBB * pAC ^ 2) := by ring
    have ht1 : 0 ≤ (floorA - pAA) * (pBB * pCC - pBC ^ 2) :=
      mul_nonneg hm1.le hX1
    have ht2 : 0 ≤ floorB * (pAA * pCC - pAC ^ 2) := mul_nonneg hfloorBpos.le hX2
    have ht3 : 0 ≤ floorC * (pAA * pBB - pAB ^ 2) := mul_nonneg hfloorCpos.le hX3
    linarith [hident.ge, hident.le]
  refine posDef_directionChartGap_of_unsignedCycleMinors direction mass weight
    hmass hweight huniv hAB hAC hBC hAoA hAoB hAoC hBoA hBoB hBoC hCoA hCoB hCoC
    hoAB hoAC hoBC hspan hscaleA hscaleB hscaleC hexpA hexpB hexpC
    hfAA hfAB hfAC hfBA hfBB hfBC hfCA hfCB hfCC
    hdemandA hdemandB hdemandC hfloorA hfloorB hfloorC
    (entryAA := floorA - pAA) (entryBB := floorB - pBB) (entryCC := floorC - pCC)
    (entryAB := -pAB) (entryAC := -pAC) (entryBC := -pBC)
    (by rw [hpAA]) (by rw [hpBB]) (by rw [hpCC])
    (by rw [hpAB]) (by rw [hpAC]) (by rw [hpBC])
    hm1 hm2 hm3

/-! ## The three missing star expansions -/

/-- Edge `2 = bc` in the vertex-a star `{0, 1, 3}`. -/
theorem kFour_expansion_starA_two :
    (1 : ℝ) • kFourDirection 2
      = (-1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 1
        + (0 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the vertex-a star `{0, 1, 3}`. -/
theorem kFour_expansion_starA_four :
    (1 : ℝ) • kFourDirection 4
      = (-1 : ℝ) • kFourDirection 0 + (0 : ℝ) • kFourDirection 1
        + (1 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the vertex-a star `{0, 1, 3}`. -/
theorem kFour_expansion_starA_five :
    (1 : ℝ) • kFourDirection 5
      = (0 : ℝ) • kFourDirection 0 + (-1 : ℝ) • kFourDirection 1
        + (1 : ℝ) • kFourDirection 3 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `1 = ac` in the vertex-b star `{0, 2, 4}`. -/
theorem kFour_expansion_starB_one :
    (1 : ℝ) • kFourDirection 1
      = (1 : ℝ) • kFourDirection 0 + (1 : ℝ) • kFourDirection 2
        + (0 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the vertex-b star `{0, 2, 4}`. -/
theorem kFour_expansion_starB_three :
    (1 : ℝ) • kFourDirection 3
      = (1 : ℝ) • kFourDirection 0 + (0 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the vertex-b star `{0, 2, 4}`. -/
theorem kFour_expansion_starB_five :
    (1 : ℝ) • kFourDirection 5
      = (0 : ℝ) • kFourDirection 0 + (-1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `0 = ab` in the vertex-c star `{1, 2, 5}`. -/
theorem kFour_expansion_starC_zero :
    (1 : ℝ) • kFourDirection 0
      = (1 : ℝ) • kFourDirection 1 + (-1 : ℝ) • kFourDirection 2
        + (0 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `3 = ad` in the vertex-c star `{1, 2, 5}`. -/
theorem kFour_expansion_starC_three :
    (1 : ℝ) • kFourDirection 3
      = (1 : ℝ) • kFourDirection 1 + (0 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `4 = bd` in the vertex-c star `{1, 2, 5}`. -/
theorem kFour_expansion_starC_four :
    (1 : ℝ) • kFourDirection 4
      = (0 : ℝ) • kFourDirection 1 + (1 : ℝ) • kFourDirection 2
        + (1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-! ## The three missing star cells -/

/-- **The vertex-a star cell** at the spanning tree `{0, 1, 3}`: three
moduli-only leading-minor inequalities against the opposite triangle
`{2, 4, 5}`. -/
theorem posDef_kFour_starCellA (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorOne floorThree : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hcorner : 0 < floorZero - (mass 2 + mass 4))
    (hminorTwo : 0 < (floorZero - (mass 2 + mass 4))
      * (floorOne - (mass 2 + mass 5)) - mass 2 ^ 2)
    (hminorDet : 0 < (floorZero - (mass 2 + mass 4))
        * (floorOne - (mass 2 + mass 5)) * (floorThree - (mass 4 + mass 5))
      - (floorZero - (mass 2 + mass 4)) * mass 5 ^ 2
      - mass 2 ^ 2 * (floorThree - (mass 4 + mass 5))
      - 2 * mass 2 * mass 4 * mass 5
      - mass 4 ^ 2 * (floorOne - (mass 2 + mass 5))) :
    (directionChartGap kFourDirection mass weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 1) (selC := 3) (outA := 2) (outB := 4) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_starA_two kFour_expansion_starA_four kFour_expansion_starA_five
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 2) (demandB := mass 4) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorOne hfloorThree
    (entryAA := floorZero - (mass 2 + mass 4))
    (entryBB := floorOne - (mass 2 + mass 5))
    (entryCC := floorThree - (mass 4 + mass 5))
    (entryAB := -(mass 2)) (entryAC := -(mass 4)) (entryBC := -(mass 5))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The vertex-b star cell** at the spanning tree `{0, 2, 4}`: three
moduli-only leading-minor inequalities against the opposite triangle
`{1, 3, 5}`. -/
theorem posDef_kFour_starCellB (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorZero floorTwo floorFour : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hcorner : 0 < floorZero - (mass 1 + mass 3))
    (hminorTwo : 0 < (floorZero - (mass 1 + mass 3))
      * (floorTwo - (mass 1 + mass 5)) - mass 1 ^ 2)
    (hminorDet : 0 < (floorZero - (mass 1 + mass 3))
        * (floorTwo - (mass 1 + mass 5)) * (floorFour - (mass 3 + mass 5))
      - (floorZero - (mass 1 + mass 3)) * mass 5 ^ 2
      - mass 1 ^ 2 * (floorFour - (mass 3 + mass 5))
      - 2 * mass 1 * mass 3 * mass 5
      - mass 3 ^ 2 * (floorTwo - (mass 1 + mass 5))) :
    (directionChartGap kFourDirection mass weight
      ({0, 2, 4} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 0) (selB := 2) (selC := 4) (outA := 1) (outB := 3) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_starB_one kFour_expansion_starB_three kFour_expansion_starB_five
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 1) (demandB := mass 3) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorTwo hfloorFour
    (entryAA := floorZero - (mass 1 + mass 3))
    (entryBB := floorTwo - (mass 1 + mass 5))
    (entryCC := floorFour - (mass 3 + mass 5))
    (entryAB := -(mass 1)) (entryAC := -(mass 3)) (entryBC := -(mass 5))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The vertex-c star cell** at the spanning tree `{1, 2, 5}`: three
moduli-only leading-minor inequalities against the opposite triangle
`{0, 3, 4}`. -/
theorem posDef_kFour_starCellC (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorOne floorTwo floorFive : ℝ}
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorOne - (mass 0 + mass 3))
    (hminorTwo : 0 < (floorOne - (mass 0 + mass 3))
      * (floorTwo - (mass 0 + mass 4)) - mass 0 ^ 2)
    (hminorDet : 0 < (floorOne - (mass 0 + mass 3))
        * (floorTwo - (mass 0 + mass 4)) * (floorFive - (mass 3 + mass 4))
      - (floorOne - (mass 0 + mass 3)) * mass 4 ^ 2
      - mass 0 ^ 2 * (floorFive - (mass 3 + mass 4))
      - 2 * mass 0 * mass 3 * mass 4
      - mass 3 ^ 2 * (floorTwo - (mass 0 + mass 4))) :
    (directionChartGap kFourDirection mass weight
      ({1, 2, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 1) (selB := 2) (selC := 5) (outA := 0) (outB := 3) (outC := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_starC_zero kFour_expansion_starC_three kFour_expansion_starC_four
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 3) (demandC := mass 4)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorOne hfloorTwo hfloorFive
    (entryAA := floorOne - (mass 0 + mass 3))
    (entryBB := floorTwo - (mass 0 + mass 4))
    (entryCC := floorFive - (mass 3 + mass 4))
    (entryAB := -(mass 0)) (entryAC := -(mass 3)) (entryBC := -(mass 4))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-! ## The star memberships and the gauge-star trace corollary -/

/-- The vertex-a star is a spanning tree. -/
theorem starTreeA_mem_kFourSpanningTreeList :
    ({0, 1, 3} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The vertex-b star is a spanning tree. -/
theorem starTreeB_mem_kFourSpanningTreeList :
    ({0, 2, 4} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The vertex-c star is a spanning tree. -/
theorem starTreeC_mem_kFourSpanningTreeList :
    ({1, 2, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- **The gauge-star trace corollary.**  One inequality fires the gauge tree:
the three opposite masses, each weighted by its two cycle floor products, stay
below the floor product of the star. -/
theorem posDef_kFour_starTrace (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorThree floorFour floorFive : ℝ}
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hposThree : 0 < floorThree) (hposFour : 0 < floorFour)
    (hposFive : 0 < floorFive)
    (htrace : mass 0 * (floorFour * floorFive + floorThree * floorFive)
        + mass 1 * (floorFour * floorFive + floorThree * floorFour)
        + mass 2 * (floorThree * floorFive + floorThree * floorFour)
      < floorThree * (floorFour * floorFive)) :
    (directionChartGap kFourDirection mass weight
      ({3, 4, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleTrace kFourDirection mass weight
    hmass hweight
    (selA := 3) (selB := 4) (selC := 5) (outA := 0) (outB := 1) (outC := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_star_zero kFour_expansion_star_one kFour_expansion_star_two
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 1) (demandC := mass 2)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorThree hfloorFour hfloorFive hposThree hposFour hposFive ?_
  nlinarith [htrace]

end Gtz
