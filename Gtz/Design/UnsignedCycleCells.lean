import Gtz.Design.BudgetCoverCriterion
import Gtz.Design.KFourChartClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The unsigned cycle cells

The budget certificate carries nine allocation witnesses.  This module removes
them.  For any probe, the chart gap dominates the unsigned cycle form read at
the absolute selected readings.  A cell is then three leading-minor
inequalities of one explicit `3x3` matrix in the moduli alone.

The chain: per-row Cauchy-Schwarz at the optimal allocation is the unsigned
row square, so the fixed-allocation certificate never beats the unsigned form,
and the unsigned form needs no witness.  The Sylvester lemma of the K4 closure
turns the matrix hypothesis into the three minors.

The module lands the master criterion for every direction family, the six K4
fundamental-cycle expansions at the gauge tree and at the band tree, the two
K4 cells with moduli-only hypotheses, the exact band witness with integer
minors `141`, `5490`, `14151`, the two three-lines cells in the same format,
the heavy-label law (a chart weight vector always carries a label at `1/6` or
more), and the K4 registry joint.
-/

namespace Gtz

open Matrix Finset

/-! ## The K4 span and the heavy-label law -/

/-- The K4 directions span: labels `3`, `4`, `5` are the standard basis. -/
theorem kFourDirection_span (probe : Fin 3 → ℝ)
    (hzero : ∀ label, kFourDirection label ⬝ᵥ probe = 0) : probe = 0 := by
  have hthree := hzero 3
  have hfour := hzero 4
  have hfive := hzero 5
  simp [kFourDirection_three, kFourDirection_four, kFourDirection_five,
    dotProduct, Fin.sum_univ_three] at hthree hfour hfive
  funext coordIndex
  fin_cases coordIndex
  · simpa using hthree
  · simpa using hfour
  · simpa using hfive

/-- **The heavy-label law.**  Six chart weights sum to one, so some label
carries at least `1/6`, hence at least `1/10`: the tenth-heavy hypothesis is
automatic at every chart point. -/
theorem directionChartPoint_exists_tenthHeavy (point : DirectionChartPoint 6) :
    ∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel := by
  by_contra hall
  push Not at hall
  have hbound : (∑ label, point.weight label) < ∑ _label : Fin 6, (1 : ℝ) / 10 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun label _ => hall label
  rw [point.weight_sum_one, Finset.sum_const, Finset.card_univ] at hbound
  norm_num at hbound

/-! ## The K4 fundamental-cycle expansions -/

/-- Edge `0 = ab` in the gauge tree `{3, 4, 5}`. -/
theorem kFour_expansion_star_zero :
    (1 : ℝ) • kFourDirection 0
      = (1 : ℝ) • kFourDirection 3 + (-1 : ℝ) • kFourDirection 4
        + (0 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `1 = ac` in the gauge tree `{3, 4, 5}`. -/
theorem kFour_expansion_star_one :
    (1 : ℝ) • kFourDirection 1
      = (1 : ℝ) • kFourDirection 3 + (0 : ℝ) • kFourDirection 4
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `2 = bc` in the gauge tree `{3, 4, 5}`. -/
theorem kFour_expansion_star_two :
    (1 : ℝ) • kFourDirection 2
      = (0 : ℝ) • kFourDirection 3 + (1 : ℝ) • kFourDirection 4
        + (-1 : ℝ) • kFourDirection 5 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `0 = ab` in the band tree `{1, 3, 4}`. -/
theorem kFour_expansion_band_zero :
    (1 : ℝ) • kFourDirection 0
      = (0 : ℝ) • kFourDirection 1 + (1 : ℝ) • kFourDirection 3
        + (-1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `2 = bc` in the band tree `{1, 3, 4}`. -/
theorem kFour_expansion_band_two :
    (1 : ℝ) • kFourDirection 2
      = (1 : ℝ) • kFourDirection 1 + (-1 : ℝ) • kFourDirection 3
        + (1 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- Edge `5 = cd` in the band tree `{1, 3, 4}`. -/
theorem kFour_expansion_band_five :
    (1 : ℝ) • kFourDirection 5
      = (-1 : ℝ) • kFourDirection 1 + (1 : ℝ) • kFourDirection 3
        + (0 : ℝ) • kFourDirection 4 := by
  funext idx
  fin_cases idx <;> (simp [kFourDirection]; try ring)

/-- The quadratic form of an explicit symmetric `3x3` matrix at an explicit
vector, in scalar shape. -/
theorem explicit_quadForm_eval (a b c d e f rA rB rC : ℝ) :
    (![rA, rB, rC] : Fin 3 → ℝ) ⬝ᵥ
        ((!![a, b, c; b, d, e; c, e, f] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![rA, rB, rC])
      = a * rA ^ 2 + 2 * b * (rA * rB) + 2 * c * (rA * rC)
        + d * rB ^ 2 + 2 * e * (rB * rC) + f * rC ^ 2 := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-! ## The master criterion -/

/-- **THE UNSIGNED CYCLE CRITERION.**  Six labels split into a selected triple
and an outside triple, each outside label expands in the selected directions
with a nonzero scale, and the absolute expansion coefficients are bounded by
the `f` data.  When the explicit `3x3` unsigned matrix built from demand
bounds and budget floors has positive leading minors, the chart gap of the
selected triple is positive definite outright.  No allocation appears: the
per-row Cauchy-Schwarz at the optimal allocation is the unsigned row square,
so this criterion dominates every fixed-allocation budget certificate. -/
theorem posDef_directionChartGap_of_unsignedCycleMinors
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
    (hcorner : 0 < entryAA)
    (hminorTwo : 0 < entryAA * entryBB - entryAB ^ 2)
    (hminorDet : 0 < entryAA * entryBB * entryCC - entryAA * entryBC ^ 2
      - entryAB ^ 2 * entryCC + 2 * entryAB * entryAC * entryBC
      - entryAC ^ 2 * entryBB) :
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
    ring_nf
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
  have hreadOf : ∀ (scale eA eB eC : ℝ) (outLabel : Fin 6),
      scale • direction outLabel
        = eA • direction selA + eB • direction selB + eC • direction selC →
      scale * (direction outLabel ⬝ᵥ probe)
        = eA * (direction selA ⬝ᵥ probe) + eB * (direction selB ⬝ᵥ probe)
          + eC * (direction selC ⬝ᵥ probe) := by
    intro scale eA eB eC outLabel hexp
    have hdot := congrArg (fun vec : Fin 3 → ℝ => vec ⬝ᵥ probe) hexp
    simpa [add_dotProduct, smul_dotProduct, smul_eq_mul] using hdot
  have hreadA := hreadOf scaleA eAA eAB eAC outA hexpA
  have hreadB := hreadOf scaleB eBA eBB eBC outB hexpB
  have hreadC := hreadOf scaleC eCA eCB eCC outC hexpC
  have hfAAnn : 0 ≤ fAA := (abs_nonneg _).trans hfAA
  have hfABnn : 0 ≤ fAB := (abs_nonneg _).trans hfAB
  have hfACnn : 0 ≤ fAC := (abs_nonneg _).trans hfAC
  have hfBAnn : 0 ≤ fBA := (abs_nonneg _).trans hfBA
  have hfBBnn : 0 ≤ fBB := (abs_nonneg _).trans hfBB
  have hfBCnn : 0 ≤ fBC := (abs_nonneg _).trans hfBC
  have hfCAnn : 0 ≤ fCA := (abs_nonneg _).trans hfCA
  have hfCBnn : 0 ≤ fCB := (abs_nonneg _).trans hfCB
  have hfCCnn : 0 ≤ fCC := (abs_nonneg _).trans hfCC
  have habsOf : ∀ (eA eB eC fA fB fC : ℝ), |eA| ≤ fA → |eB| ≤ fB → |eC| ≤ fC →
      |eA * (direction selA ⬝ᵥ probe) + eB * (direction selB ⬝ᵥ probe)
        + eC * (direction selC ⬝ᵥ probe)|
        ≤ fA * |direction selA ⬝ᵥ probe| + fB * |direction selB ⬝ᵥ probe|
          + fC * |direction selC ⬝ᵥ probe| := by
    intro eA eB eC fA fB fC hfA hfB hfC
    calc |eA * (direction selA ⬝ᵥ probe) + eB * (direction selB ⬝ᵥ probe)
          + eC * (direction selC ⬝ᵥ probe)|
        ≤ |eA * (direction selA ⬝ᵥ probe)| + |eB * (direction selB ⬝ᵥ probe)|
          + |eC * (direction selC ⬝ᵥ probe)| := abs_add_three _ _ _
      _ = |eA| * |direction selA ⬝ᵥ probe| + |eB| * |direction selB ⬝ᵥ probe|
          + |eC| * |direction selC ⬝ᵥ probe| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ fA * |direction selA ⬝ᵥ probe| + fB * |direction selB ⬝ᵥ probe|
          + fC * |direction selC ⬝ᵥ probe| := by
          have hA := mul_le_mul_of_nonneg_right hfA
            (abs_nonneg (direction selA ⬝ᵥ probe))
          have hB := mul_le_mul_of_nonneg_right hfB
            (abs_nonneg (direction selB ⬝ᵥ probe))
          have hC := mul_le_mul_of_nonneg_right hfC
            (abs_nonneg (direction selC ⬝ᵥ probe))
          linarith
  have houtOf : ∀ (scale eA eB eC fA fB fC demand : ℝ) (outLabel : Fin 6),
      scale ≠ 0 →
      scale * (direction outLabel ⬝ᵥ probe)
        = eA * (direction selA ⬝ᵥ probe) + eB * (direction selB ⬝ᵥ probe)
          + eC * (direction selC ⬝ᵥ probe) →
      |eA| ≤ fA → |eB| ≤ fB → |eC| ≤ fC →
      mass outLabel ≤ demand * scale ^ 2 →
      mass outLabel * (direction outLabel ⬝ᵥ probe) ^ 2
        ≤ demand * (fA * |direction selA ⬝ᵥ probe| + fB * |direction selB ⬝ᵥ probe|
            + fC * |direction selC ⬝ᵥ probe|) ^ 2 := by
    intro scale eA eB eC fA fB fC demand outLabel hscale hread hfA hfB hfC hdemand
    have hscaleSq : (0 : ℝ) < scale ^ 2 := by positivity
    have hdemandPos : 0 < demand := by
      have hchain : (0 : ℝ) < demand * scale ^ 2 := (hmass outLabel).trans_le hdemand
      rcases mul_pos_iff.mp hchain with ⟨hpos, _⟩ | ⟨_, hneg⟩
      · exact hpos
      · exact absurd hscaleSq (not_lt.mpr hneg.le)
    have habs := habsOf eA eB eC fA fB fC hfA hfB hfC
    have hsq : (scale * (direction outLabel ⬝ᵥ probe)) ^ 2
        ≤ (fA * |direction selA ⬝ᵥ probe| + fB * |direction selB ⬝ᵥ probe|
            + fC * |direction selC ⬝ᵥ probe|) ^ 2 := by
      rw [← sq_abs (scale * (direction outLabel ⬝ᵥ probe)), hread, pow_two, pow_two]
      exact mul_self_le_mul_self (abs_nonneg _) habs
    have hstepOne : mass outLabel * (direction outLabel ⬝ᵥ probe) ^ 2
        ≤ demand * (scale * (direction outLabel ⬝ᵥ probe)) ^ 2 := by
      calc mass outLabel * (direction outLabel ⬝ᵥ probe) ^ 2
          ≤ demand * scale ^ 2 * (direction outLabel ⬝ᵥ probe) ^ 2 :=
            mul_le_mul_of_nonneg_right hdemand
              (sq_nonneg (direction outLabel ⬝ᵥ probe))
        _ = demand * (scale * (direction outLabel ⬝ᵥ probe)) ^ 2 := by ring
    exact hstepOne.trans (mul_le_mul_of_nonneg_left hsq hdemandPos.le)
  have houtA := houtOf scaleA eAA eAB eAC fAA fAB fAC demandA outA hscaleA hreadA
    hfAA hfAB hfAC hdemandA
  have houtB := houtOf scaleB eBA eBB eBC fBA fBB fBC demandB outB hscaleB hreadB
    hfBA hfBB hfBC hdemandB
  have houtC := houtOf scaleC eCA eCB eCC fCA fCB fCC demandC outC hscaleC hreadC
    hfCA hfCB hfCC hdemandC
  have hgapOf : ∀ label : Fin 6, ∀ lower : ℝ,
      lower * weight label ≤ mass label * (1 - weight label) →
      lower * (direction label ⬝ᵥ probe) ^ 2
        ≤ mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
          - mass label * (direction label ⬝ᵥ probe) ^ 2 := by
    intro label lower hload
    have hsplit : mass label * (1 - weight label)
        = mass label - mass label * weight label := by ring
    rw [hsplit] at hload
    have hone : (lower + mass label) * weight label ≤ mass label := by
      have hkey : (lower + mass label) * weight label
          = lower * weight label + mass label * weight label := by ring
      rw [hkey]
      linarith only [hload]
    have htwo := (le_div_iff₀ (hweight label)).mpr hone
    have hthree : lower ≤ mass label / weight label - mass label := by
      linarith only [htwo]
    calc lower * (direction label ⬝ᵥ probe) ^ 2
        ≤ (mass label / weight label - mass label)
          * (direction label ⬝ᵥ probe) ^ 2 :=
          mul_le_mul_of_nonneg_right hthree (sq_nonneg (direction label ⬝ᵥ probe))
      _ = mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
          - mass label * (direction label ⬝ᵥ probe) ^ 2 := by ring
  have hfloorTermA := hgapOf selA floorA hfloorA
  have hfloorTermB := hgapOf selB floorB hfloorB
  have hfloorTermC := hgapOf selC floorC hfloorC
  have hsomeRead : direction selA ⬝ᵥ probe ≠ 0 ∨ direction selB ⬝ᵥ probe ≠ 0
      ∨ direction selC ⬝ᵥ probe ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨hzA, hzB, hzC⟩ := hall
    refine hne (hspan probe ?_)
    intro label
    have houtRead : ∀ (scale eA eB eC : ℝ) (outLabel : Fin 6),
        scale * (direction outLabel ⬝ᵥ probe)
          = eA * (direction selA ⬝ᵥ probe) + eB * (direction selB ⬝ᵥ probe)
            + eC * (direction selC ⬝ᵥ probe) →
        scale ≠ 0 → direction outLabel ⬝ᵥ probe = 0 := by
      intro scale eA eB eC outLabel hread hscaleNe
      rw [hzA, hzB, hzC] at hread
      have hzero : scale * (direction outLabel ⬝ᵥ probe) = 0 := by linarith
      exact (mul_eq_zero.mp hzero).resolve_left hscaleNe
    have hmem : label ∈ ({selA, selB, selC, outA, outB, outC} : Finset (Fin 6)) := by
      rw [huniv]; exact Finset.mem_univ label
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hzA
    · exact hzB
    · exact hzC
    · exact houtRead scaleA eAA eAB eAC _ hreadA hscaleA
    · exact houtRead scaleB eBA eBB eBC _ hreadB hscaleB
    · exact houtRead scaleC eCA eCB eCC _ hreadC hscaleC
  have hmat := posDef_of_leadingMinors_fin_three entryAA entryAB entryAC entryBB
    entryBC entryCC hcorner hminorTwo hminorDet
  have hrvec : ![|direction selA ⬝ᵥ probe|, |direction selB ⬝ᵥ probe|,
      |direction selC ⬝ᵥ probe|] ≠ 0 := by
    intro hzero
    rcases hsomeRead with hres | hres | hres
    · exact hres (abs_eq_zero.mp (by simpa using congrFun hzero 0))
    · exact hres (abs_eq_zero.mp (by simpa using congrFun hzero 1))
    · exact hres (abs_eq_zero.mp (by simpa using congrFun hzero 2))
  have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hmat).2 hrvec
  rw [star_trivial] at hquad
  rw [explicit_quadForm_eval] at hquad

  have hbridge : entryAA * |direction selA ⬝ᵥ probe| ^ 2
        + 2 * entryAB * (|direction selA ⬝ᵥ probe| * |direction selB ⬝ᵥ probe|)
        + 2 * entryAC * (|direction selA ⬝ᵥ probe| * |direction selC ⬝ᵥ probe|)
        + entryBB * |direction selB ⬝ᵥ probe| ^ 2
        + 2 * entryBC * (|direction selB ⬝ᵥ probe| * |direction selC ⬝ᵥ probe|)
        + entryCC * |direction selC ⬝ᵥ probe| ^ 2
      = floorA * (direction selA ⬝ᵥ probe) ^ 2
        + floorB * (direction selB ⬝ᵥ probe) ^ 2
        + floorC * (direction selC ⬝ᵥ probe) ^ 2
        - (demandA * (fAA * |direction selA ⬝ᵥ probe|
              + fAB * |direction selB ⬝ᵥ probe|
              + fAC * |direction selC ⬝ᵥ probe|) ^ 2
          + demandB * (fBA * |direction selA ⬝ᵥ probe|
              + fBB * |direction selB ⬝ᵥ probe|
              + fBC * |direction selC ⬝ᵥ probe|) ^ 2
          + demandC * (fCA * |direction selA ⬝ᵥ probe|
              + fCB * |direction selB ⬝ᵥ probe|
              + fCC * |direction selC ⬝ᵥ probe|) ^ 2) := by
    rw [hentryAA, hentryBB, hentryCC, hentryAB, hentryAC, hentryBC,
      ← sq_abs (direction selA ⬝ᵥ probe), ← sq_abs (direction selB ⬝ᵥ probe),
      ← sq_abs (direction selC ⬝ᵥ probe)]
    ring
  rw [hbridge] at hquad
  rw [hselSum, hunivSum]
  linarith only [hquad, houtA, houtB, houtC, hfloorTermA, hfloorTermB, hfloorTermC]

/-! ## The two K4 cells -/

/-- **The K4 gauge-star cell.**  Three moduli-only inequalities make the gauge
tree `{3, 4, 5}` strictly dominating: each tree edge's cleared budget floor
beats its unsigned cycle load, through the three leading minors. -/
theorem posDef_kFour_starCell (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorThree floorFour floorFive : ℝ}
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    (hcorner : 0 < floorThree - (mass 0 + mass 1))
    (hminorTwo : 0 < (floorThree - (mass 0 + mass 1))
      * (floorFour - (mass 0 + mass 2)) - mass 0 ^ 2)
    (hminorDet : 0 < (floorThree - (mass 0 + mass 1))
        * (floorFour - (mass 0 + mass 2)) * (floorFive - (mass 1 + mass 2))
      - (floorThree - (mass 0 + mass 1)) * mass 2 ^ 2
      - mass 0 ^ 2 * (floorFive - (mass 1 + mass 2))
      - 2 * mass 0 * mass 1 * mass 2
      - mass 1 ^ 2 * (floorFour - (mass 0 + mass 2))) :
    (directionChartGap kFourDirection mass weight
      ({3, 4, 5} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
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
    hfloorThree hfloorFour hfloorFive
    (entryAA := floorThree - (mass 0 + mass 1))
    (entryBB := floorFour - (mass 0 + mass 2))
    (entryCC := floorFive - (mass 1 + mass 2))
    (entryAB := -(mass 0)) (entryAC := -(mass 1)) (entryBC := -(mass 2))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The K4 band-tree cell.**  The same three-minor format at the tree
`{1, 3, 4}`, the designated tree of the canonical band inhabitant. -/
theorem posDef_kFour_bandTreeCell (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {floorOne floorThree floorFour : ℝ}
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hcorner : 0 < floorOne - (mass 2 + mass 5))
    (hminorTwo : 0 < (floorOne - (mass 2 + mass 5))
      * (floorThree - (mass 0 + mass 2 + mass 5)) - (mass 2 + mass 5) ^ 2)
    (hminorDet : 0 < (floorOne - (mass 2 + mass 5))
        * (floorThree - (mass 0 + mass 2 + mass 5)) * (floorFour - (mass 0 + mass 2))
      - (floorOne - (mass 2 + mass 5)) * (mass 0 + mass 2) ^ 2
      - (mass 2 + mass 5) ^ 2 * (floorFour - (mass 0 + mass 2))
      - 2 * (mass 2 + mass 5) * mass 2 * (mass 0 + mass 2)
      - mass 2 ^ 2 * (floorThree - (mass 0 + mass 2 + mass 5))) :
    (directionChartGap kFourDirection mass weight
      ({1, 3, 4} : Finset (Fin 6))).PosDef := by
  refine posDef_directionChartGap_of_unsignedCycleMinors kFourDirection mass weight
    hmass hweight
    (selA := 1) (selB := 3) (selC := 4) (outA := 0) (outB := 2) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    kFourDirection_span
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    kFour_expansion_band_zero kFour_expansion_band_two kFour_expansion_band_five
    (fAA := 0) (fAB := 1) (fAC := 1) (fBA := 1) (fBB := 1) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (demandA := mass 0) (demandB := mass 2) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorOne hfloorThree hfloorFour
    (entryAA := floorOne - (mass 2 + mass 5))
    (entryBB := floorThree - (mass 0 + mass 2 + mass 5))
    (entryCC := floorFour - (mass 0 + mass 2))
    (entryAB := -(mass 2 + mass 5)) (entryAC := -(mass 2))
    (entryBC := -(mass 0 + mass 2))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-! ## The exact band witness -/

/-- **The band inhabitant fires the unsigned cell** at the designated tree
`{1, 3, 4}` with exact integer minors `141`, `5490`, `14151`.  The budget
floors hold at exact equality: `144/10 = 144/10`, `45/10 = 45/10`,
`21/10 = 21/10`. -/
theorem bandResidual_unsignedCell_oneThreeFour :
    (directionChartGap kFourDirection bandResidualWitnessMass
      bandResidualWitnessWeight ({1, 3, 4} : Finset (Fin 6))).PosDef := by
  refine posDef_kFour_bandTreeCell bandResidualWitnessMass bandResidualWitnessWeight
    (fun label => by fin_cases label <;> norm_num [bandResidualWitnessMass])
    (fun label => by fin_cases label <;> norm_num [bandResidualWitnessWeight])
    (floorOne := 144) (floorThree := 45) (floorFour := 7)
    ?_ ?_ ?_ ?_ ?_ ?_ <;>
  norm_num [bandResidualWitnessMass, bandResidualWitnessWeight]

/-! ## The two three-lines cells in the unsigned format -/

/-- **The three-lines vertex cell, unsigned.**  The vertex triple `{0, 1, 3}`
closes from three moduli-only minors; the slide enters only through one
absolute bound `|slide| ≤ slideBound`. -/
theorem posDef_threeLines_vertexCellMinors (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {slideBound : ℝ} (hslideBound : |slide| ≤ slideBound)
    {floorZero floorOne floorThree : ℝ}
    (hfloorZero : floorZero * weight 0 ≤ mass 0 * (1 - weight 0))
    (hfloorOne : floorOne * weight 1 ≤ mass 1 * (1 - weight 1))
    (hfloorThree : floorThree * weight 3 ≤ mass 3 * (1 - weight 3))
    (hcorner : 0 < floorZero - (mass 2 + mass 4))
    (hminorTwo : 0 < (floorZero - (mass 2 + mass 4))
      * (floorOne - (mass 2 + mass 5)) - mass 2 ^ 2)
    (hminorDet : 0 < (floorZero - (mass 2 + mass 4))
        * (floorOne - (mass 2 + mass 5))
        * (floorThree - (mass 4 + mass 5 * slideBound ^ 2))
      - (floorZero - (mass 2 + mass 4)) * (mass 5 * slideBound) ^ 2
      - mass 2 ^ 2 * (floorThree - (mass 4 + mass 5 * slideBound ^ 2))
      - 2 * mass 2 * mass 4 * (mass 5 * slideBound)
      - mass 4 ^ 2 * (floorOne - (mass 2 + mass 5))) :
    (directionChartGap (threeLinesDirection slide) mass weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  have hslideBoundNonneg : 0 ≤ slideBound := (abs_nonneg _).trans hslideBound
  refine posDef_directionChartGap_of_unsignedCycleMinors (threeLinesDirection slide)
    mass weight hmass hweight
    (selA := 0) (selB := 1) (selC := 3) (outA := 2) (outB := 4) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    (threeLines_expansion_insertTwo slide) (threeLines_expansion_insertFour slide)
    (threeLines_expansion_insertFive slide)
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := slideBound)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hslideBound
    (demandA := mass 2) (demandB := mass 4) (demandC := mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorOne hfloorThree
    (entryAA := floorZero - (mass 2 + mass 4))
    (entryBB := floorOne - (mass 2 + mass 5))
    (entryCC := floorThree - (mass 4 + mass 5 * slideBound ^ 2))
    (entryAB := -(mass 2)) (entryAC := -(mass 4))
    (entryBC := -(mass 5 * slideBound))
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    hcorner (by ring_nf; ring_nf at hminorTwo; exact hminorTwo)
    (by ring_nf; ring_nf at hminorDet; exact hminorDet)

/-- **The three-lines free cell, unsigned.**  The free triple `{2, 4, 5}`
closes from three minors; the demands carry the `(slide + 1)^2` clearing and
the slide enters through the one absolute bound. -/
theorem posDef_threeLines_freeCellMinors (slide : ℝ) (hslide : slide ≠ -1)
    (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    {slideBound : ℝ} (hslideBound : |slide| ≤ slideBound)
    {demandZero demandOne demandThree : ℝ}
    (hdemandZero : mass 0 ≤ demandZero * (slide + 1) ^ 2)
    (hdemandOne : mass 1 ≤ demandOne * (slide + 1) ^ 2)
    (hdemandThree : mass 3 ≤ demandThree * (slide + 1) ^ 2)
    {floorTwo floorFour floorFive : ℝ}
    (hfloorTwo : floorTwo * weight 2 ≤ mass 2 * (1 - weight 2))
    (hfloorFour : floorFour * weight 4 ≤ mass 4 * (1 - weight 4))
    (hfloorFive : floorFive * weight 5 ≤ mass 5 * (1 - weight 5))
    {entryAA entryAB entryAC entryBB entryBC entryCC : ℝ}
    (hentryAA : entryAA
      = floorTwo - (demandZero + demandOne * slideBound ^ 2 + demandThree))
    (hentryBB : entryBB
      = floorFour - (demandZero * slideBound ^ 2 + demandOne * slideBound ^ 2
        + demandThree))
    (hentryCC : entryCC = floorFive - (demandZero + demandOne + demandThree))
    (hentryAB : entryAB
      = -(demandZero * slideBound + demandOne * slideBound ^ 2 + demandThree))
    (hentryAC : entryAC
      = -(demandZero + demandOne * slideBound + demandThree))
    (hentryBC : entryBC
      = -(demandZero * slideBound + demandOne * slideBound + demandThree))
    (hcorner : 0 < entryAA)
    (hminorTwo : 0 < entryAA * entryBB - entryAB ^ 2)
    (hminorDet : 0 < entryAA * entryBB * entryCC - entryAA * entryBC ^ 2
      - entryAB ^ 2 * entryCC + 2 * entryAB * entryAC * entryBC
      - entryAC ^ 2 * entryBB) :
    (directionChartGap (threeLinesDirection slide) mass weight
      ({2, 4, 5} : Finset (Fin 6))).PosDef := by
  have hsucc : slide + 1 ≠ 0 := fun hzero => hslide (by linarith)
  have hslideBoundNonneg : 0 ≤ slideBound := (abs_nonneg _).trans hslideBound
  refine posDef_directionChartGap_of_unsignedCycleMinors (threeLinesDirection slide)
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
    (fAA := 1) (fAB := slideBound) (fAC := 1) (fBA := slideBound)
    (fBB := slideBound) (fBC := 1) (fCA := 1) (fCB := 1) (fCC := 1)
    (by norm_num) hslideBound (by norm_num)
    hslideBound (by simpa using hslideBound) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hdemandZero hdemandOne hdemandThree
    hfloorTwo hfloorFour hfloorFive
    (entryAA := entryAA) (entryBB := entryBB) (entryCC := entryCC)
    (entryAB := entryAB) (entryAC := entryAC) (entryBC := entryBC)
    (by rw [hentryAA]; ring) (by rw [hentryBB]; ring) (by rw [hentryCC]; ring)
    (by rw [hentryAB]; ring) (by rw [hentryAC]; ring) (by rw [hentryBC]; ring)
    hcorner hminorTwo hminorDet

/-! ## The K4 registry joint -/

/-- The gauge tree is a spanning tree. -/
theorem starTree_mem_kFourSpanningTreeList :
    ({3, 4, 5} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- The band tree is a spanning tree. -/
theorem bandTree_mem_kFourSpanningTreeList :
    ({1, 3, 4} : Finset (Fin 6)) ∈ kFourSpanningTreeList := by decide

/-- **The K4 registry joint.**  A strict spanning tree at every chart point
discharges the committed tenth-heavy knife-band obligation verbatim: neither
the band antecedents nor the weak tree is consumed, and the heavy label is
automatic by the heavy-label law. -/
theorem kFourKnifeBandRefinedTenthHeavy_of_strictTree
    (hstrict : ∀ point : DirectionChartPoint 6,
      ∃ tree ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    KFourKnifeBandRefinedTenthHeavyWeakToStrict :=
  fun point _ _ _ _ => hstrict point

end Gtz
