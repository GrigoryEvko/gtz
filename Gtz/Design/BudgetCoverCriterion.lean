import Gtz.Design.ChartReadingLaw
import Gtz.Wave.TenthLightChartWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The budget cover criterion

The covering criterion demands that the selection carry the maximal kappa
reading at every probe.  This module replaces that pointwise maximum with an
allocation certificate.  Each outside label expands in the selected triple,
and an allocated Cauchy-Schwarz step converts its mass demand into loads on
the three selected labels.  A selection is positive definite when each
selected label's total load stays strictly below its own budget
`mass * (1 - weight) / weight`.

The certificate hypotheses are polynomial inequalities in the moduli and the
allocations.  No weight normalization is necessary, no mean argument occurs,
and rational points discharge the hypotheses by `norm_num`.  The three-lines
instances close the module: the vertex cell, the free cell, and one exact
rational witness for each.  The consumer joint converts a per-point strict
triple on the tenth-heavy region into the registry obligation.
-/

namespace Gtz

open Matrix Finset

/-! ## The allocated Cauchy-Schwarz core -/

/-- The cleared three-term allocated Cauchy-Schwarz inequality.  The gap is an
exact sum of three squares. -/
theorem allocated_readingSq_le (expA expB expC readA readB readC uA uB uC : ℝ)
    (huA : 0 < uA) (huB : 0 < uB) (huC : 0 < uC) :
    (expA * readA + expB * readB + expC * readC) ^ 2 * (uA * uB * uC)
      ≤ (expA ^ 2 * (uB * uC) + expB ^ 2 * (uA * uC) + expC ^ 2 * (uA * uB))
        * (uA * readA ^ 2 + uB * readB ^ 2 + uC * readC ^ 2) := by
  nlinarith [mul_nonneg huC.le (sq_nonneg (expA * uB * readB - expB * uA * readA)),
    mul_nonneg huB.le (sq_nonneg (expA * uC * readC - expC * uA * readA)),
    mul_nonneg huA.le (sq_nonneg (expB * uC * readC - expC * uB * readB))]

/-- **The outside-demand bound.**  An outside label whose scaled direction
expands in the selected triple has its mass demand dominated pointwise by the
allocated loads, when the cleared budget inequality holds. -/
theorem outsideDemand_le_allocation {directionOut selVecA selVecB selVecC : Fin 3 → ℝ}
    {scale expA expB expC demand uA uB uC : ℝ}
    (hexp : scale • directionOut = expA • selVecA + expB • selVecB + expC • selVecC)
    (hscale : scale ≠ 0) (hdemand : 0 ≤ demand)
    (huA : 0 < uA) (huB : 0 < uB) (huC : 0 < uC)
    (hbudget : demand * (expA ^ 2 * (uB * uC) + expB ^ 2 * (uA * uC)
        + expC ^ 2 * (uA * uB)) ≤ scale ^ 2 * (uA * uB * uC))
    (probe : Fin 3 → ℝ) :
    demand * (directionOut ⬝ᵥ probe) ^ 2
      ≤ uA * (selVecA ⬝ᵥ probe) ^ 2 + uB * (selVecB ⬝ᵥ probe) ^ 2
        + uC * (selVecC ⬝ᵥ probe) ^ 2 := by
  have hread : scale * (directionOut ⬝ᵥ probe)
      = expA * (selVecA ⬝ᵥ probe) + expB * (selVecB ⬝ᵥ probe)
        + expC * (selVecC ⬝ᵥ probe) := by
    have hdot := congrArg (fun vec : Fin 3 → ℝ => vec ⬝ᵥ probe) hexp
    simpa [add_dotProduct, smul_dotProduct, smul_eq_mul] using hdot
  have hcs := allocated_readingSq_le expA expB expC (selVecA ⬝ᵥ probe)
    (selVecB ⬝ᵥ probe) (selVecC ⬝ᵥ probe) uA uB uC huA huB huC
  have hloadNonneg : 0 ≤ uA * (selVecA ⬝ᵥ probe) ^ 2 + uB * (selVecB ⬝ᵥ probe) ^ 2
      + uC * (selVecC ⬝ᵥ probe) ^ 2 := by positivity
  have hfactored : (demand * (directionOut ⬝ᵥ probe) ^ 2) * (scale ^ 2 * (uA * uB * uC))
      ≤ (uA * (selVecA ⬝ᵥ probe) ^ 2 + uB * (selVecB ⬝ᵥ probe) ^ 2
          + uC * (selVecC ⬝ᵥ probe) ^ 2) * (scale ^ 2 * (uA * uB * uC)) := by
    calc (demand * (directionOut ⬝ᵥ probe) ^ 2) * (scale ^ 2 * (uA * uB * uC))
        = demand * ((scale * (directionOut ⬝ᵥ probe)) ^ 2 * (uA * uB * uC)) := by
          ring
      _ = demand * ((expA * (selVecA ⬝ᵥ probe) + expB * (selVecB ⬝ᵥ probe)
            + expC * (selVecC ⬝ᵥ probe)) ^ 2 * (uA * uB * uC)) := by
          rw [hread]
      _ ≤ demand * ((expA ^ 2 * (uB * uC) + expB ^ 2 * (uA * uC)
            + expC ^ 2 * (uA * uB))
            * (uA * (selVecA ⬝ᵥ probe) ^ 2 + uB * (selVecB ⬝ᵥ probe) ^ 2
              + uC * (selVecC ⬝ᵥ probe) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs hdemand
      _ = demand * (expA ^ 2 * (uB * uC) + expB ^ 2 * (uA * uC)
            + expC ^ 2 * (uA * uB))
            * (uA * (selVecA ⬝ᵥ probe) ^ 2 + uB * (selVecB ⬝ᵥ probe) ^ 2
              + uC * (selVecC ⬝ᵥ probe) ^ 2) := by ring
      _ ≤ scale ^ 2 * (uA * uB * uC)
            * (uA * (selVecA ⬝ᵥ probe) ^ 2 + uB * (selVecB ⬝ᵥ probe) ^ 2
              + uC * (selVecC ⬝ᵥ probe) ^ 2) :=
          mul_le_mul_of_nonneg_right hbudget hloadNonneg
      _ = (uA * (selVecA ⬝ᵥ probe) ^ 2 + uB * (selVecB ⬝ᵥ probe) ^ 2
            + uC * (selVecC ⬝ᵥ probe) ^ 2) * (scale ^ 2 * (uA * uB * uC)) := by ring
  have hposFactor : (0 : ℝ) < scale ^ 2 * (uA * uB * uC) := by positivity
  exact le_of_mul_le_mul_right hfactored hposFactor

/-! ## The budget certificate -/

/-- **THE BUDGET CERTIFICATE.**  Six labels split into a selected triple and an
outside triple.  Each outside label expands in the selected directions with a
nonzero scale.  An allocation matrix converts the three outside demands into
loads, the cleared Cauchy-Schwarz budget bounds each outside label, and each
selected label keeps its total load strictly below the budget
`mass * (1 - weight) / weight`.  The chart gap of the selected triple is then
positive definite outright.  No weight normalization is used. -/
theorem posDef_directionChartGap_of_budgetCertificate
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
    {uAA uAB uAC uBA uBB uBC uCA uCB uCC : ℝ}
    (huAA : 0 < uAA) (huAB : 0 < uAB) (huAC : 0 < uAC)
    (huBA : 0 < uBA) (huBB : 0 < uBB) (huBC : 0 < uBC)
    (huCA : 0 < uCA) (huCB : 0 < uCB) (huCC : 0 < uCC)
    (hbudgetA : mass outA * (eAA ^ 2 * (uAB * uAC) + eAB ^ 2 * (uAA * uAC)
        + eAC ^ 2 * (uAA * uAB)) ≤ scaleA ^ 2 * (uAA * uAB * uAC))
    (hbudgetB : mass outB * (eBA ^ 2 * (uBB * uBC) + eBB ^ 2 * (uBA * uBC)
        + eBC ^ 2 * (uBA * uBB)) ≤ scaleB ^ 2 * (uBA * uBB * uBC))
    (hbudgetC : mass outC * (eCA ^ 2 * (uCB * uCC) + eCB ^ 2 * (uCA * uCC)
        + eCC ^ 2 * (uCA * uCB)) ≤ scaleC ^ 2 * (uCA * uCB * uCC))
    (hloadA : (uAA + uBA + uCA) * weight selA < mass selA * (1 - weight selA))
    (hloadB : (uAB + uBB + uCB) * weight selB < mass selB * (1 - weight selB))
    (hloadC : (uAC + uBC + uCC) * weight selC < mass selC * (1 - weight selC)) :
    (directionChartGap direction mass weight {selA, selB, selC}).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose direction mass weight {selA, selB, selC})
  rw [star_trivial, dotProduct_directionChartGap_mulVec_eq]
  have hselSum : (∑ label ∈ ({selA, selB, selC} : Finset (Fin 6)),
      mass label / weight label * (direction label ⬝ᵥ probe) ^ 2)
      = mass selA / weight selA * (direction selA ⬝ᵥ probe) ^ 2
        + mass selB / weight selB * (direction selB ⬝ᵥ probe) ^ 2
        + mass selC / weight selC * (direction selC ⬝ᵥ probe) ^ 2 := by
    rw [Finset.sum_insert (by simp [hAB, hAC]), Finset.sum_insert (by simp [hBC]),
      Finset.sum_singleton]
    ring
  have hunivSum : (∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
      = mass selA * (direction selA ⬝ᵥ probe) ^ 2
        + mass selB * (direction selB ⬝ᵥ probe) ^ 2
        + mass selC * (direction selC ⬝ᵥ probe) ^ 2
        + (mass outA * (direction outA ⬝ᵥ probe) ^ 2
          + mass outB * (direction outB ⬝ᵥ probe) ^ 2
          + mass outC * (direction outC ⬝ᵥ probe) ^ 2) := by
    rw [← huniv, Finset.sum_insert (by simp [hAB, hAC, hAoA, hAoB, hAoC]),
      Finset.sum_insert (by simp [hBC, hBoA, hBoB, hBoC]),
      Finset.sum_insert (by simp [hCoA, hCoB, hCoC]),
      Finset.sum_insert (by simp [hoAB, hoAC]), Finset.sum_insert (by simp [hoBC]),
      Finset.sum_singleton]
    ring
  have hboundA := outsideDemand_le_allocation hexpA hscaleA (hmass outA).le
    huAA huAB huAC hbudgetA probe
  have hboundB := outsideDemand_le_allocation hexpB hscaleB (hmass outB).le
    huBA huBB huBC hbudgetB probe
  have hboundC := outsideDemand_le_allocation hexpC hscaleC (hmass outC).le
    huCA huCB huCC hbudgetC probe
  have hgapOf : ∀ label : Fin 6, ∀ colsum : ℝ,
      colsum * weight label < mass label * (1 - weight label) →
      colsum < mass label / weight label - mass label := by
    intro label colsum hload
    have hone : (colsum + mass label) * weight label < mass label := by nlinarith
    have htwo := (lt_div_iff₀ (hweight label)).mpr hone
    linarith
  have hgapA := hgapOf selA (uAA + uBA + uCA) hloadA
  have hgapB := hgapOf selB (uAB + uBB + uCB) hloadB
  have hgapC := hgapOf selC (uAC + uBC + uCC) hloadC
  have hsomeRead : direction selA ⬝ᵥ probe ≠ 0 ∨ direction selB ⬝ᵥ probe ≠ 0
      ∨ direction selC ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨hzA, hzB, hzC⟩ := hall
    refine hne (hspan probe ?_)
    intro label
    have houtRead : ∀ (scale eA eB eC : ℝ) (outLabel : Fin 6),
        scale • direction outLabel
          = eA • direction selA + eB • direction selB + eC • direction selC →
        scale ≠ 0 → direction outLabel ⬝ᵥ probe = 0 := by
      intro scale eA eB eC outLabel hexp hscaleNe
      have hdot := congrArg (fun vec : Fin 3 → ℝ => vec ⬝ᵥ probe) hexp
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hdot
      rw [hzA, hzB, hzC] at hdot
      have hzero : scale * (direction outLabel ⬝ᵥ probe) = 0 := by linarith
      exact (mul_eq_zero.mp hzero).resolve_left hscaleNe
    have hmem : label ∈ ({selA, selB, selC, outA, outB, outC} : Finset (Fin 6)) := by
      rw [huniv]; exact Finset.mem_univ label
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hzA
    · exact hzB
    · exact hzC
    · exact houtRead scaleA eAA eAB eAC _ hexpA hscaleA
    · exact houtRead scaleB eBA eBB eBC _ hexpB hscaleB
    · exact houtRead scaleC eCA eCB eCC _ hexpC hscaleC
  rw [hselSum, hunivSum]
  have hsqA : (0 : ℝ) ≤ (direction selA ⬝ᵥ probe) ^ 2 := sq_nonneg _
  have hsqB : (0 : ℝ) ≤ (direction selB ⬝ᵥ probe) ^ 2 := sq_nonneg _
  have hsqC : (0 : ℝ) ≤ (direction selC ⬝ᵥ probe) ^ 2 := sq_nonneg _
  rcases hsomeRead with hres | hres | hres
  · have hresSq : (0 : ℝ) < (direction selA ⬝ᵥ probe) ^ 2 := by positivity
    nlinarith [hboundA, hboundB, hboundC,
      mul_lt_mul_of_pos_right hgapA hresSq,
      mul_le_mul_of_nonneg_right hgapB.le hsqB,
      mul_le_mul_of_nonneg_right hgapC.le hsqC]
  · have hresSq : (0 : ℝ) < (direction selB ⬝ᵥ probe) ^ 2 := by positivity
    nlinarith [hboundA, hboundB, hboundC,
      mul_le_mul_of_nonneg_right hgapA.le hsqA,
      mul_lt_mul_of_pos_right hgapB hresSq,
      mul_le_mul_of_nonneg_right hgapC.le hsqC]
  · have hresSq : (0 : ℝ) < (direction selC ⬝ᵥ probe) ^ 2 := by positivity
    nlinarith [hboundA, hboundB, hboundC,
      mul_le_mul_of_nonneg_right hgapA.le hsqA,
      mul_le_mul_of_nonneg_right hgapB.le hsqB,
      mul_lt_mul_of_pos_right hgapC hresSq]

/-! ## The three-lines expansions -/

/-- The inserted label `2` expands in the vertex triple at scale one. -/
theorem threeLines_expansion_insertTwo (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 2
      = (1 : ℝ) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 1
        + (0 : ℝ) • threeLinesDirection slide 3 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

/-- The inserted label `4` expands in the vertex triple at scale one. -/
theorem threeLines_expansion_insertFour (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 4
      = (1 : ℝ) • threeLinesDirection slide 0 + (0 : ℝ) • threeLinesDirection slide 1
        + (1 : ℝ) • threeLinesDirection slide 3 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

/-- The inserted label `5` expands in the vertex triple at scale one. -/
theorem threeLines_expansion_insertFive (slide : ℝ) :
    (1 : ℝ) • threeLinesDirection slide 5
      = (0 : ℝ) • threeLinesDirection slide 0 + (1 : ℝ) • threeLinesDirection slide 1
        + slide • threeLinesDirection slide 3 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

/-- The vertex label `0` expands in the free triple at scale `slide + 1`. -/
theorem threeLines_expansion_vertexZero (slide : ℝ) :
    (slide + 1) • threeLinesDirection slide 0
      = (1 : ℝ) • threeLinesDirection slide 2 + slide • threeLinesDirection slide 4
        + (-1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

/-- The vertex label `1` expands in the free triple at scale `slide + 1`. -/
theorem threeLines_expansion_vertexOne (slide : ℝ) :
    (slide + 1) • threeLinesDirection slide 1
      = slide • threeLinesDirection slide 2 + (-slide) • threeLinesDirection slide 4
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

/-- The vertex label `3` expands in the free triple at scale `slide + 1`. -/
theorem threeLines_expansion_vertexThree (slide : ℝ) :
    (slide + 1) • threeLinesDirection slide 3
      = (-1 : ℝ) • threeLinesDirection slide 2 + (1 : ℝ) • threeLinesDirection slide 4
        + (1 : ℝ) • threeLinesDirection slide 5 := by
  funext idx
  fin_cases idx <;> (simp [threeLinesDirection]; try ring)

/-! ## The two canonical budget cells -/

/-- **The vertex budget cell.**  At any chart moduli, an allocation with the
three cleared budgets and the three strict load bounds makes the vertex triple
`{0, 1, 3}` strictly dominating, at every slide. -/
theorem posDef_threeLines_vertexCell (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {uAA uAB uAC uBA uBB uBC uCA uCB uCC : ℝ}
    (huAA : 0 < uAA) (huAB : 0 < uAB) (huAC : 0 < uAC)
    (huBA : 0 < uBA) (huBB : 0 < uBB) (huBC : 0 < uBC)
    (huCA : 0 < uCA) (huCB : 0 < uCB) (huCC : 0 < uCC)
    (hbudgetTwo : mass 2 * (uAB * uAC + uAA * uAC) ≤ uAA * uAB * uAC)
    (hbudgetFour : mass 4 * (uBB * uBC + uBA * uBB) ≤ uBA * uBB * uBC)
    (hbudgetFive : mass 5 * (uCA * uCC + slide ^ 2 * (uCA * uCB)) ≤ uCA * uCB * uCC)
    (hloadZero : (uAA + uBA + uCA) * weight 0 < mass 0 * (1 - weight 0))
    (hloadOne : (uAB + uBB + uCB) * weight 1 < mass 1 * (1 - weight 1))
    (hloadThree : (uAC + uBC + uCC) * weight 3 < mass 3 * (1 - weight 3)) :
    (directionChartGap (threeLinesDirection slide) mass weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_budgetCertificate (threeLinesDirection slide)
    mass weight hmass hweight
    (selA := 0) (selB := 1) (selC := 3) (outA := 2) (outB := 4) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    (threeLines_expansion_insertTwo slide) (threeLines_expansion_insertFour slide)
    (threeLines_expansion_insertFive slide)
    huAA huAB huAC huBA huBB huBC huCA huCB huCC
    (by nlinarith [hbudgetTwo]) (by nlinarith [hbudgetFour])
    (by nlinarith [hbudgetFive])
    hloadZero hloadOne hloadThree

/-- **The free budget cell.**  At any chart moduli and any slide away from
`-1`, an allocation with the three cleared budgets and the three strict load
bounds makes the free triple `{2, 4, 5}` strictly dominating. -/
theorem posDef_threeLines_freeCell (slide : ℝ) (hslide : slide ≠ -1)
    (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {uAA uAB uAC uBA uBB uBC uCA uCB uCC : ℝ}
    (huAA : 0 < uAA) (huAB : 0 < uAB) (huAC : 0 < uAC)
    (huBA : 0 < uBA) (huBB : 0 < uBB) (huBC : 0 < uBC)
    (huCA : 0 < uCA) (huCB : 0 < uCB) (huCC : 0 < uCC)
    (hbudgetZero : mass 0 * (uAB * uAC + slide ^ 2 * (uAA * uAC) + uAA * uAB)
      ≤ (slide + 1) ^ 2 * (uAA * uAB * uAC))
    (hbudgetOne : mass 1 * (slide ^ 2 * (uBB * uBC) + slide ^ 2 * (uBA * uBC)
        + uBA * uBB)
      ≤ (slide + 1) ^ 2 * (uBA * uBB * uBC))
    (hbudgetThree : mass 3 * (uCB * uCC + uCA * uCC + uCA * uCB)
      ≤ (slide + 1) ^ 2 * (uCA * uCB * uCC))
    (hloadTwo : (uAA + uBA + uCA) * weight 2 < mass 2 * (1 - weight 2))
    (hloadFour : (uAB + uBB + uCB) * weight 4 < mass 4 * (1 - weight 4))
    (hloadFive : (uAC + uBC + uCC) * weight 5 < mass 5 * (1 - weight 5)) :
    (directionChartGap (threeLinesDirection slide) mass weight
      ({2, 4, 5} : Finset (Fin 6))).PosDef := by
  have hsucc : slide + 1 ≠ 0 := fun hzero => hslide (by linarith)
  exact posDef_directionChartGap_of_budgetCertificate (threeLinesDirection slide)
    mass weight hmass hweight
    (selA := 2) (selB := 4) (selC := 5) (outA := 0) (outB := 1) (outC := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := slide + 1) (scaleB := slide + 1) (scaleC := slide + 1)
    hsucc hsucc hsucc
    (threeLines_expansion_vertexZero slide) (threeLines_expansion_vertexOne slide)
    (threeLines_expansion_vertexThree slide)
    huAA huAB huAC huBA huBB huBC huCA huCB huCC
    (by nlinarith [hbudgetZero]) (by nlinarith [hbudgetOne])
    (by nlinarith [hbudgetThree])
    hloadTwo hloadFour hloadFive

/-! ## The exact rational witnesses -/

/-- The free-cell witness masses: vertex masses `1/6`, inserted masses `1/9`. -/
noncomputable def freeCellWitnessMass : Fin 6 → ℝ
  | 0 => 1 / 6
  | 1 => 1 / 6
  | 2 => 1 / 9
  | 3 => 1 / 6
  | 4 => 1 / 9
  | 5 => 1 / 9

/-- The uniform witness weights. -/
noncomputable def uniformWitnessWeight : Fin 6 → ℝ := fun _ => 1 / 6

/-- **The free cell fires in kernel** at slide one on the witness moduli, with
the uniform allocation `1/8`.  Each cleared budget reads as the exact equality
`1/128 = 1/128`. -/
theorem freeCell_certificate_witness :
    (directionChartGap (threeLinesDirection 1) freeCellWitnessMass
      uniformWitnessWeight ({2, 4, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_threeLines_freeCell 1 (by norm_num) _ _
    (fun label => by fin_cases label <;> norm_num [freeCellWitnessMass])
    (fun label => by norm_num [uniformWitnessWeight])
    (uAA := 1 / 8) (uAB := 1 / 8) (uAC := 1 / 8) (uBA := 1 / 8) (uBB := 1 / 8)
    (uBC := 1 / 8) (uCA := 1 / 8) (uCB := 1 / 8) (uCC := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ <;>
  norm_num [freeCellWitnessMass, uniformWitnessWeight]

/-- The vertex-cell witness weights: vertex weights `1/9`, inserted weights
`2/9`. -/
noncomputable def vertexCellWitnessWeight : Fin 6 → ℝ
  | 0 => 1 / 9
  | 1 => 1 / 9
  | 2 => 2 / 9
  | 3 => 1 / 9
  | 4 => 2 / 9
  | 5 => 2 / 9

/-- The uniform witness masses. -/
noncomputable def uniformWitnessMass : Fin 6 → ℝ := fun _ => 1 / 6

/-- **The vertex cell fires in kernel** at slide one on its witness moduli,
with the allocation `1/2` on the two circuit labels and `1/100` on the unused
one. -/
theorem vertexCell_certificate_witness :
    (directionChartGap (threeLinesDirection 1) uniformWitnessMass
      vertexCellWitnessWeight ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  refine posDef_threeLines_vertexCell 1 _ _
    (fun label => by norm_num [uniformWitnessMass])
    (fun label => by fin_cases label <;> norm_num [vertexCellWitnessWeight])
    (uAA := 1 / 2) (uAB := 1 / 2) (uAC := 1 / 100) (uBA := 1 / 2) (uBB := 1 / 100)
    (uBC := 1 / 2) (uCA := 1 / 100) (uCB := 1 / 2) (uCC := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ <;>
  norm_num [uniformWitnessMass, vertexCellWitnessWeight]

/-! ## The consumer joint -/

/-- **The registry joint.**  A strict triple at every tenth-heavy chart point
of the fundamental domain discharges the committed three-lines obligation.
The weak antecedent of the obligation is not consumed: strictness needs no
tie. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavy_of_heavyStrictTriple
    (hstrict : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
      ∀ point : DirectionChartPoint 6,
        (∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel) →
        ∃ selected : Finset (Fin 6), selected.card = 3 ∧
          (directionChartGap (threeLinesDirection slide) point.mass
            point.weight selected).PosDef) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavy := by
  intro slide hadmissible hfundamental point hheavy _hweak
  exact hstrict slide hadmissible hfundamental point hheavy

end Gtz
