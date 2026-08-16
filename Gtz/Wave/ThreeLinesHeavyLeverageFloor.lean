import Gtz.Wave.ThreeLinesMovedOrbitTraceWiring
import Gtz.Design.StratumEmptinessLedger
import Gtz.Reduction.MassGapDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The chart leverage floor, and the leverage narrowing of A2

`Gtz.leverage_one_le_of_isTie_sixThree` is unconditional at six labels, but it
speaks about a DESIGN atom.  This file carries it across the whitening weld and
lands it as a statement about a CHART point.

The transport is an exact identity.  A whitener `R` with `Rᵀ T R = 1` satisfies
`R Rᵀ = T⁻¹`, so the whitened atom of the label `c` has

  `leverageOf (design.atom c) = (mass c / weight c) * (d_c ⬝ᵥ (T⁻¹ *ᵥ d_c))`

where `T` is the total mass moment.  That number is the classical statistical
leverage score of the direction `d_c`.  The design-side floor `1 ≤ leverageOf`
therefore reads, on the chart and division-free,

  `weight c * det T  ≤  mass c * (d_c ⬝ᵥ (adjugate T *ᵥ d_c))`.

Six inequalities, polynomial in the masses and the slide, free at every chart
point that carries a weak card-three witness and no strict one.

* `Gtz.mul_transpose_eq_inv_of_congruence_to_one` — the whitener identity.
* `Gtz.exists_design_of_chartPoint_withLeverage` — the weld, strengthened to
  report the leverage of every whitened atom.
* `Gtz.ChartLeverageFloor` — the six division-free chart inequalities.
* `Gtz.chartLeverageFloor_of_no_posDef_triple` — the floor is free on the
  residual, at any six-label rank-three chart.
* `Gtz.sum_chartLeverageNumerator` — the leverage scores total `3 * det T`, so
  the floor carries exactly two units of slack.
* `Gtz.chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage_iff`
  — **the registry joint**: A2 with the leverage floor added as a hypothesis is
  equivalent to A2.  The narrowing is free.

The tenth-heavy premise that earlier A2 formulas carried is a different and
vacuous statement: six positive weights summing to one always leave one weight
at least `1/6`, so `Gtz.directionChartPoint_exists_tenthHeavy` holds at every
chart point.  The leverage floor is not vacuous.
-/

namespace Gtz

open Matrix Finset

/-! ## The whitener identity -/

/-- **A whitening congruence inverts the form it whitens.**  If `Rᵀ * form * R`
is the identity and `R` is invertible, then `R * Rᵀ` is the inverse of the
form. -/
theorem mul_transpose_eq_inv_of_congruence_to_one {rank : ℕ}
    {form whitener : Matrix (Fin rank) (Fin rank) ℝ}
    (hunit : IsUnit whitener.det)
    (hwhiten : whitenerᵀ * form * whitener = 1) :
    whitener * whitenerᵀ = form⁻¹ := by
  have hright : whitener * whitener⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hstep : whitener * whitenerᵀ * form = 1 := by
    calc whitener * whitenerᵀ * form
        = whitener * whitenerᵀ * form * (whitener * whitener⁻¹) := by
          rw [hright, Matrix.mul_one]
      _ = whitener * (whitenerᵀ * form * whitener) * whitener⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = whitener * 1 * whitener⁻¹ := by rw [hwhiten]
      _ = 1 := by rw [Matrix.mul_one, hright]
  exact (Matrix.inv_eq_left_inv hstep).symm

/-- The leverage of a transposed image is the quadratic form of `R * Rᵀ`. -/
theorem leverageOf_transpose_mulVec {rank : ℕ}
    (whitener : Matrix (Fin rank) (Fin rank) ℝ) (vec : Fin rank → ℝ) :
    leverageOf (whitenerᵀ *ᵥ vec) = vec ⬝ᵥ ((whitener * whitenerᵀ) *ᵥ vec) := by
  rw [leverageOf_eq_dotProduct, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, dotProduct_comm]

/-! ## The weld, strengthened to report leverage -/

/-- **The whitening weld with its leverage read off.**  Every chart point with a
positive definite mass moment is a weighted design whose atom leverages are the
statistical leverage scores of the chart directions against that moment.  The
transfer clauses are those of `Gtz.exists_design_of_chartPoint`. -/
theorem exists_design_of_chartPoint_withLeverage {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hmoment : (∑ label, point.mass label • atomMatrix (direction label)).PosDef) :
    ∃ design : WeightedDesign size 3, design.weight = point.weight ∧
      (∀ selected : Finset (Fin size),
        ((subsetSum design selected - 1).PosDef
            ↔ (directionChartGap direction point.mass point.weight selected).PosDef)
          ∧ (Dominates design selected
            ↔ (directionChartGap direction point.mass point.weight selected).PosSemidef)) ∧
      ∀ label : Fin size,
        leverageOf (design.atom label)
          = point.mass label / point.weight label *
              (direction label ⬝ᵥ
                ((∑ l, point.mass l • atomMatrix (direction l))⁻¹ *ᵥ direction label)) := by
  classical
  have hmassNonneg : ∀ label, 0 ≤ point.mass label := fun label => (point.mass_pos label).le
  have hframe : frameOperatorOfAtoms (chartAtomFamily direction point.mass point.weight)
      point.weight = ∑ label, point.mass label • atomMatrix (direction label) :=
    frameOperatorOfAtoms_chartAtomFamily direction point.mass point.weight hmassNonneg
      point.weight_pos
  obtain ⟨congruence, hunit, hcongruence⟩ := exists_congruence_to_one (hframe ▸ hmoment)
  have hwhiten : congruenceᵀ * (∑ label, point.weight label
      • atomMatrix (chartAtomFamily direction point.mass point.weight label))
      * congruence = 1 := hcongruence
  refine ⟨whitenedFamilyDesign (chartAtomFamily direction point.mass point.weight) point.weight
      point.weight_pos point.weight_sum_one congruence hwhiten, rfl, ?_, ?_⟩
  · intro selected
    have hmomentEq : subsetSum (whitenedFamilyDesign
          (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
          point.weight_sum_one congruence hwhiten) selected
        = congruenceᵀ * subsetSumOfAtoms (chartAtomFamily direction point.mass point.weight)
            selected * congruence := by
      rw [whitenedDesign_subsetSum_eq, sum_atomMatrix_conj, subsetSumOfAtoms]
    have hgapEq : subsetSum (whitenedFamilyDesign
          (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
          point.weight_sum_one congruence hwhiten) selected - 1
        = congruenceᵀ * directionChartGap direction point.mass point.weight selected
            * congruence := by
      rw [hmomentEq, ← hcongruence,
        directionChartGap_eq_frameGap direction point.mass point.weight hmassNonneg
          point.weight_pos selected,
        frameOperatorOfAtoms, Matrix.mul_assoc congruenceᵀ, Matrix.mul_assoc congruenceᵀ,
        ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_assoc]
    have hsymmetric : (directionChartGap direction point.mass point.weight selected)ᵀ
        = directionChartGap direction point.mass point.weight selected :=
      directionChartGap_transpose direction point.mass point.weight selected
    refine ⟨?_, ?_⟩
    · rw [hgapEq]
      exact (posDef_congr_right hsymmetric hunit).symm
    · show (subsetSum _ selected - 1).PosSemidef ↔ _
      rw [hgapEq]
      exact (posSemidef_congr_right hsymmetric hunit).symm
  · intro label
    have hinv : congruence * congruenceᵀ
        = (∑ l, point.mass l • atomMatrix (direction l))⁻¹ := by
      refine mul_transpose_eq_inv_of_congruence_to_one hunit ?_
      have : (∑ label, point.weight label
          • atomMatrix (chartAtomFamily direction point.mass point.weight label))
          = ∑ l, point.mass l • atomMatrix (direction l) := by
        rw [← frameOperatorOfAtoms, hframe]
      rwa [this] at hwhiten
    have hratio : 0 ≤ point.mass label / point.weight label :=
      div_nonneg (hmassNonneg label) (point.weight_pos label).le
    show leverageOf (congruenceᵀ *ᵥ chartAtomFamily direction point.mass point.weight label) = _
    rw [chartAtomFamily, Matrix.mulVec_smul, leverageOf_smul,
      Real.sq_sqrt hratio, leverageOf_transpose_mulVec, hinv]

/-! ## The chart leverage floor -/

/-- The determinant-cleared statistical leverage of one chart direction against
the total mass moment. -/
noncomputable def chartLeverageNumerator {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (label : Fin size) : ℝ :=
  mass label *
    (direction label ⬝ᵥ
      ((∑ l, mass l • atomMatrix (direction l)).adjugate *ᵥ direction label))

/-- **The chart leverage floor.**  Every weight is at most the statistical
leverage of its own direction.  Division-free: the determinant of the mass
moment multiplies the weight instead of dividing the leverage. -/
def ChartLeverageFloor {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size) : Prop :=
  ∀ label : Fin size,
    point.weight label * (∑ l, point.mass l • atomMatrix (direction l)).det
      ≤ chartLeverageNumerator direction point.mass label

/-- The quadratic form of the inverse mass moment, cleared of its
determinant. -/
theorem dotProduct_inv_mulVec_eq {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) (label : Fin size) :
    direction label ⬝ᵥ ((∑ l, mass l • atomMatrix (direction l))⁻¹ *ᵥ direction label)
      = ((∑ l, mass l • atomMatrix (direction l)).det)⁻¹ *
          (direction label ⬝ᵥ
            ((∑ l, mass l • atomMatrix (direction l)).adjugate *ᵥ direction label)) := by
  have hinv : (∑ l, mass l • atomMatrix (direction l))⁻¹
      = ((∑ l, mass l • atomMatrix (direction l)).det)⁻¹
        • (∑ l, mass l • atomMatrix (direction l)).adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [hinv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **The leverage floor is free on the residual.**  At any six-label rank-three
chart point with a positive definite mass moment, a weak card-three witness and
no strict card-three gap force the six leverage inequalities. -/
theorem chartLeverageFloor_of_no_posDef_triple
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hmoment : (∑ l, point.mass l • atomMatrix (direction l)).PosDef)
    (hweak : ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosSemidef)
    (hnone : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (directionChartGap direction point.mass point.weight selected).PosDef) :
    ChartLeverageFloor direction point := by
  obtain ⟨design, hweight, htransfer, hleverage⟩ :=
    exists_design_of_chartPoint_withLeverage direction point hmoment
  have htie : IsTie design := by
    refine ⟨?_, ?_⟩
    · obtain ⟨selected, hcard, hpsd⟩ := hweak
      exact ⟨selected, hcard, (htransfer selected).2.mpr hpsd⟩
    · intro selected hcard hpd
      exact hnone selected hcard ((htransfer selected).1.mp hpd)
  have hdetPos : 0 < (∑ l, point.mass l • atomMatrix (direction l)).det := hmoment.det_pos
  intro label
  have hfloor : (1 : ℝ) ≤ leverageOf (design.atom label) :=
    leverage_one_le_of_isTie_sixThree design htie label
  rw [hleverage label, dotProduct_inv_mulVec_eq direction point.mass label] at hfloor
  have hweightPos : 0 < point.weight label := point.weight_pos label
  have hscaled := mul_le_mul_of_nonneg_right hfloor
    (mul_pos hweightPos hdetPos).le
  rw [one_mul] at hscaled
  refine le_trans hscaled (le_of_eq ?_)
  rw [chartLeverageNumerator]
  field_simp

/-! ## The total slack -/

/-- **The leverage scores total three determinants.**  This is `tr (T⁻¹ T) = 3`
cleared of its denominator, and it holds at every size with no positivity
hypothesis at all. -/
theorem sum_chartLeverageNumerator {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) :
    ∑ label, chartLeverageNumerator direction mass label
      = 3 * (∑ l, mass l • atomMatrix (direction l)).det := by
  have hpair : ∀ label : Fin size,
      chartLeverageNumerator direction mass label
        = ((∑ l, mass l • atomMatrix (direction l)).adjugate
            * (mass label • atomMatrix (direction label))).trace := by
    intro label
    rw [chartLeverageNumerator, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      trace_mul_atomMatrix_massGap]
  rw [Finset.sum_congr rfl fun label _ => hpair label, ← Matrix.trace_sum,
    ← Matrix.mul_sum, Matrix.adjugate_mul, Matrix.trace_smul, Matrix.trace_one]
  simp [mul_comm]

/-- On the residual the six slacks are nonnegative and total exactly two
determinants. -/
theorem sum_leverage_slack_eq_two_det (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6) :
    ∑ label, (chartLeverageNumerator direction point.mass label
        - point.weight label * (∑ l, point.mass l • atomMatrix (direction l)).det)
      = 2 * (∑ l, point.mass l • atomMatrix (direction l)).det := by
  rw [Finset.sum_sub_distrib, sum_chartLeverageNumerator, ← Finset.sum_mul,
    point.weight_sum_one, one_mul]
  ring

/-! ## The registry joint -/

/-- The registry A2 formula with the leverage floor added as a hypothesis. -/
def ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage :
    Prop :=
  ∀ slide : ℝ, ∀ hadmissible : IsAdmissibleThreeLinesParameter slide, 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      ChartLeverageFloor (threeLinesDirection slide) point →
      ¬ ThreeLinesBudgetCellFires slide point →
      ¬ ThreeLinesReadingCoverCellFires slide point →
      ¬ ThreeLinesSevenOrbitTraceAtlasCellFires slide hadmissible.1 point →
      (∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- **The narrowing is free.**  The leverage-floor form of A2 proves the
registry A2 formula: a point that already carries a strict card-three gap is
finished, and a point that carries none satisfies the floor. -/
theorem chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_of_leverage
    (hleverage :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines := by
  intro slide hadmissible hfundamental point hbudget hreading hatlas hweak
  by_cases hstrict : ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight selected).PosDef
  · exact hstrict
  · push Not at hstrict
    refine hleverage slide hadmissible hfundamental point ?_ hbudget hreading hatlas hweak
    obtain ⟨witness, hcard, _, _, _, hpsd⟩ := hweak
    exact chartLeverageFloor_of_no_posDef_triple (threeLinesDirection slide) point
      (posDef_massMoment_threeLinesDirection slide point) ⟨witness, hcard, hpsd⟩ hstrict

/-- The registry A2 formula restricts to the leverage-floor form. -/
theorem leverageThreeLinesFundamentalDomain_of_sevenOrbitTraceBlind
    (hblind :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage := by
  intro slide hadmissible hfundamental point _hfloor hbudget hreading hatlas hweak
  exact hblind slide hadmissible hfundamental point hbudget hreading hatlas hweak

/-- **The registry joint.**  Adding the six leverage inequalities to A2 is an
exact formula sharpening, not a stronger sufficient condition. -/
theorem
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage_iff_blind :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage ↔
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines :=
  ⟨chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_of_leverage,
    leverageThreeLinesFundamentalDomain_of_sevenOrbitTraceBlind⟩

/-- The leverage-floor A2 formula is equivalent to the public chart
statement. -/
theorem
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage_iff :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLinesLeverage_iff_blind.trans
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff

end Gtz
