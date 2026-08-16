import Gtz.Wave.ComplementInvariantCell
import Gtz.Design.CrossLeverageBudget

/-!
# The omitted triple in projection coordinates, and the row-budget cell

The full-selection gap is the slack Laplacian, so the chart leverages are the
diagonal of a rank-three orthogonal projection: they total three
(`Gtz.sum_chartLeverage_eq_three`) and none exceeds one
(`Gtz.chartLeverage_le_one`).  The corpus already spends the row identity of
that projection on the TWO BY TWO complement minor
(`Gtz.pair_minor_pos_of_leverage_slack`).  It never spends it on the
DETERMINANT, and that is what this file does.

Write `w` for a weight, `omega = 1 - w` for the co-weight, `pivotSlack` for
`Gtz.chartPivotSlack` and `leverage` for `Gtz.chartLeverage`.  The off-diagonal
of the projection is carried root-free by

  `crossLeverageSq a b = chartSlack a * chartSlack b * fullInverseForm a b ^ 2`,

which is the SQUARE of a projection entry and needs no square root.  Two
dictionary facts drive everything:

* `crossLeverageSq_eq_pairBoostedCrossSq_mul` — the boosted cross of a pair is
  the cross leverage divided by the two co-weights;
* `sum_erase_crossLeverageSq` — the row identity, `sum over b <> a` of the cross
  leverage is `leverage a * (1 - leverage a)`.

The first turns the pair budget of `Gtz.ComplementInvariantCell` into a
determinant in projection coordinates,

  `pairDetBudget i j k * omega i * omega j * omega k
     = pivotSlack i * pivotSlack j * pivotSlack k
       - pivotSlack i * crossLeverageSq j k
       - pivotSlack j * crossLeverageSq i k
       - pivotSlack k * crossLeverageSq i j`,

and the pivot cross sum becomes `leverage i * crossLeverageSq j k + ...`.  The
second caps every cross leverage inside a triple by a row budget, and summing
the three rows gives

  `crossLeverageSq i j + crossLeverageSq i k + crossLeverageSq j k
     <= (leverage i * (1 - leverage i) + leverage j * (1 - leverage j)
          + leverage k * (1 - leverage k)) / 2`.

Together they give `posDef_directionChartGap_compl_triple_of_leverageRow`: a
strictly positive definite selection from the pivot slacks and the leverages
ALONE, with no cross entry anywhere in the hypothesis.  That is the three by
three analogue of the landed pair certificate.

The file closes with the refutation SHAPE of the pair-budget cover.  A chart
point at which every omitted triple has a NON-POSITIVE pair budget cannot
satisfy `Gtz.PairBudgetCovers`, because the cover demands a strictly positive
budget, and `not_pairBudgetCovers_of_forall_budget_nonpos` spends exactly that.
Such points exist and carry strictly positive definite selections, so the cover
is strictly stronger than the consolidated conclusion.  The mechanism is
`tripleBoostedCross_neg_of_budget_nonpos_of_det_pos`: where the budget is
non-positive and the determinant positive, the whole of the positivity lives in
the SIGN of the triple cross, and the pinning identity says pair data reads only
its square.
-/

namespace Gtz

variable {size : ℕ}

/-! ## 1. The cross leverage: the projection off-diagonal, squared -/

/-- **THE CROSS LEVERAGE, SQUARED.**  The slack-weighted square of an
off-diagonal inverse-form entry.  This is the square of an off-diagonal entry of
the projection whose diagonal is the chart leverage, and being a square it needs
no root. -/
noncomputable def crossLeverageSq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size) : ℝ :=
  chartSlack mass weight a * chartSlack mass weight b
    * (fullInverseForm direction mass weight a b) ^ 2

theorem crossLeverageSq_comm (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (a b : Fin size) :
    crossLeverageSq direction mass weight a b = crossLeverageSq direction mass weight b a := by
  simp only [crossLeverageSq]
  rw [fullInverseForm_comm direction mass weight huniv a b]
  ring

theorem crossLeverageSq_nonneg (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a b : Fin size)
    (hslackA : 0 ≤ chartSlack mass weight a) (hslackB : 0 ≤ chartSlack mass weight b) :
    0 ≤ crossLeverageSq direction mass weight a b := by
  simp only [crossLeverageSq]
  exact mul_nonneg (mul_nonneg hslackA hslackB) (sq_nonneg _)

/-- The diagonal cross leverage is the square of the leverage. -/
theorem crossLeverageSq_self (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (a : Fin size) :
    crossLeverageSq direction mass weight a a
      = chartLeverage direction mass weight a ^ 2 := by
  simp only [crossLeverageSq, chartLeverage]
  ring

/-- **THE DICTIONARY.**  The boosted cross of a pair is the cross leverage with
the two co-weights removed.  This is what carries the pair budget of the
complement into projection coordinates. -/
theorem crossLeverageSq_eq_pairBoostedCrossSq_mul (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {a b : Fin size}
    (hwa : weight a ≠ 0) (hwb : weight b ≠ 0) :
    crossLeverageSq direction mass weight a b
      = pairBoostedCrossSq direction mass weight a b
        * ((1 - weight a) * (1 - weight b)) := by
  simp only [crossLeverageSq, pairBoostedCrossSq]
  rw [← one_sub_weight_mul_boost mass weight hwa, ← one_sub_weight_mul_boost mass weight hwb]
  ring

/-! ## 2. The row identity of the projection -/

/-- **THE ROW IDENTITY IN PROJECTION COORDINATES.**  The off-diagonal cross
leverages of a label total the leverage against its own cap slack.  This is the
landed off-diagonal row energy, scaled by the label's own slack. -/
theorem sum_erase_crossLeverageSq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) (a : Fin size) :
    ∑ b ∈ Finset.univ.erase a, crossLeverageSq direction mass weight a b
      = chartLeverage direction mass weight a
        * (1 - chartLeverage direction mass weight a) := by
  classical
  have hrow := sum_erase_chartSlack_mul_fullInverseForm_sq direction mass weight huniv a
  have hpull : ∑ b ∈ Finset.univ.erase a, crossLeverageSq direction mass weight a b
      = chartSlack mass weight a
        * ∑ b ∈ Finset.univ.erase a,
            chartSlack mass weight b * (fullInverseForm direction mass weight a b) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by simp only [crossLeverageSq]; ring
  rw [hpull, hrow, chartLeverage]
  ring

/-- **THE PAIR ROW BOUND.**  Two distinct partners of a label spend at most the
label's whole row budget.  No cross entry appears on the right. -/
theorem crossLeverageSq_pair_le_rowBudget (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ c, 0 ≤ chartSlack mass weight c)
    {a b c : Fin size} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    crossLeverageSq direction mass weight a b + crossLeverageSq direction mass weight a c
      ≤ chartLeverage direction mass weight a
        * (1 - chartLeverage direction mass weight a) := by
  classical
  have hsub : ({b, c} : Finset (Fin size)) ⊆ Finset.univ.erase a := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.mem_erase.mpr ⟨fun h => hab h.symm, Finset.mem_univ x⟩
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      exact Finset.mem_erase.mpr ⟨fun h => hac h.symm, Finset.mem_univ x⟩
  have hpair : ∑ x ∈ ({b, c} : Finset (Fin size)), crossLeverageSq direction mass weight a x
      = crossLeverageSq direction mass weight a b
        + crossLeverageSq direction mass weight a c :=
    Finset.sum_pair hbc
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ => crossLeverageSq_nonneg direction mass weight a x (hslack a) (hslack x))
  rw [hpair] at hmono
  rw [← sum_erase_crossLeverageSq direction mass weight huniv a]
  exact hmono

/-- **THE TRIPLE ROW BOUND.**  The three cross leverages inside a triple total
at most half the sum of the three row budgets.  Each pair is counted by exactly
two of the three rows, which is where the halving comes from. -/
theorem sum_crossLeverageSq_triple_le (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ c, 0 ≤ chartSlack mass weight c)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    crossLeverageSq direction mass weight i j + crossLeverageSq direction mass weight i k
        + crossLeverageSq direction mass weight j k
      ≤ (chartLeverage direction mass weight i
            * (1 - chartLeverage direction mass weight i)
          + chartLeverage direction mass weight j
            * (1 - chartLeverage direction mass weight j)
          + chartLeverage direction mass weight k
            * (1 - chartLeverage direction mass weight k)) / 2 := by
  have hrowI := crossLeverageSq_pair_le_rowBudget direction mass weight huniv hslack hij hik hjk
  have hrowJ := crossLeverageSq_pair_le_rowBudget direction mass weight huniv hslack
    (Ne.symm hij) hjk hik
  have hrowK := crossLeverageSq_pair_le_rowBudget direction mass weight huniv hslack
    (Ne.symm hik) (Ne.symm hjk) hij
  have hsymJI : crossLeverageSq direction mass weight j i
      = crossLeverageSq direction mass weight i j :=
    crossLeverageSq_comm direction mass weight huniv j i
  have hsymKI : crossLeverageSq direction mass weight k i
      = crossLeverageSq direction mass weight i k :=
    crossLeverageSq_comm direction mass weight huniv k i
  have hsymKJ : crossLeverageSq direction mass weight k j
      = crossLeverageSq direction mass weight j k :=
    crossLeverageSq_comm direction mass weight huniv k j
  rw [hsymJI] at hrowJ
  rw [hsymKI, hsymKJ] at hrowK
  linarith

/-! ## 3. The budget and the cross sum in projection coordinates -/

/-- **THE PAIR BUDGET IN PROJECTION COORDINATES.**  Scaled by the three
co-weights, the pair budget is the determinant of the pivot-slack diagonal
against the cross leverages, with the triple term removed.  Every quantity on
the right is a projection reading. -/
theorem pairDetBudget_mul_coweight_eq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i j k : Fin size}
    (hwi : weight i ≠ 0) (hwj : weight j ≠ 0) (hwk : weight k ≠ 0) :
    pairDetBudget direction mass weight i j k
        * ((1 - weight i) * (1 - weight j) * (1 - weight k))
      = chartPivotSlack direction mass weight i * chartPivotSlack direction mass weight j
          * chartPivotSlack direction mass weight k
        - chartPivotSlack direction mass weight i * crossLeverageSq direction mass weight j k
        - chartPivotSlack direction mass weight j * crossLeverageSq direction mass weight i k
        - chartPivotSlack direction mass weight k * crossLeverageSq direction mass weight i j := by
  simp only [pairDetBudget, chartPivotSlack]
  rw [crossLeverageSq_eq_pairBoostedCrossSq_mul direction mass weight hwj hwk,
    crossLeverageSq_eq_pairBoostedCrossSq_mul direction mass weight hwi hwk,
    crossLeverageSq_eq_pairBoostedCrossSq_mul direction mass weight hwi hwj]
  ring

/-- **THE PIVOT CROSS SUM IN PROJECTION COORDINATES.**  Scaled by the same three
co-weights, the pivot cross sum pairs each leverage with the cross leverage of
the other two. -/
theorem pivotCrossSum_mul_coweight_eq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i j k : Fin size}
    (hwi : weight i ≠ 0) (hwj : weight j ≠ 0) (hwk : weight k ≠ 0) :
    pivotCrossSum direction mass weight i j k
        * ((1 - weight i) * (1 - weight j) * (1 - weight k))
      = chartLeverage direction mass weight i * crossLeverageSq direction mass weight j k
        + chartLeverage direction mass weight j * crossLeverageSq direction mass weight i k
        + chartLeverage direction mass weight k * crossLeverageSq direction mass weight i j := by
  simp only [pivotCrossSum]
  rw [crossLeverageSq_eq_pairBoostedCrossSq_mul direction mass weight hwj hwk,
    crossLeverageSq_eq_pairBoostedCrossSq_mul direction mass weight hwi hwk,
    crossLeverageSq_eq_pairBoostedCrossSq_mul direction mass weight hwi hwj,
    chartLeverage_eq_one_sub_weight_mul_fullPivot direction mass weight hwi,
    chartLeverage_eq_one_sub_weight_mul_fullPivot direction mass weight hwj,
    chartLeverage_eq_one_sub_weight_mul_fullPivot direction mass weight hwk]
  ring

/-! ## 4. The row-budget cell -/

/-- **THE BUDGET MINUS THE CROSS SUM, BOUNDED BY ROW DATA ALONE.**  Every cross
leverage is capped by the row budgets, so the scaled difference of the pair
budget and the pivot cross sum is bounded below by a quantity that mentions no
cross entry at all. -/
theorem pairDetBudget_sub_pivotCrossSum_mul_coweight_ge (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ c, 0 ≤ chartSlack mass weight c)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hwi : weight i ≠ 0) (hwj : weight j ≠ 0) (hwk : weight k ≠ 0)
    (cap : ℝ)
    (hcapI : chartPivotSlack direction mass weight i
      + chartLeverage direction mass weight i ≤ cap)
    (hcapJ : chartPivotSlack direction mass weight j
      + chartLeverage direction mass weight j ≤ cap)
    (hcapK : chartPivotSlack direction mass weight k
      + chartLeverage direction mass weight k ≤ cap)
    (hcapNonneg : 0 ≤ cap) :
    chartPivotSlack direction mass weight i * chartPivotSlack direction mass weight j
        * chartPivotSlack direction mass weight k
      - cap * ((chartLeverage direction mass weight i
            * (1 - chartLeverage direction mass weight i)
          + chartLeverage direction mass weight j
            * (1 - chartLeverage direction mass weight j)
          + chartLeverage direction mass weight k
            * (1 - chartLeverage direction mass weight k)) / 2)
      ≤ (pairDetBudget direction mass weight i j k
            - pivotCrossSum direction mass weight i j k)
          * ((1 - weight i) * (1 - weight j) * (1 - weight k)) := by
  have hbudget := pairDetBudget_mul_coweight_eq direction mass weight hwi hwj hwk
  have hcross := pivotCrossSum_mul_coweight_eq direction mass weight hwi hwj hwk
  have hrow := sum_crossLeverageSq_triple_le direction mass weight huniv hslack hij hik hjk
  have hij0 := crossLeverageSq_nonneg direction mass weight i j (hslack i) (hslack j)
  have hik0 := crossLeverageSq_nonneg direction mass weight i k (hslack i) (hslack k)
  have hjk0 := crossLeverageSq_nonneg direction mass weight j k (hslack j) (hslack k)
  have hexpand : (pairDetBudget direction mass weight i j k
        - pivotCrossSum direction mass weight i j k)
      * ((1 - weight i) * (1 - weight j) * (1 - weight k))
      = chartPivotSlack direction mass weight i * chartPivotSlack direction mass weight j
          * chartPivotSlack direction mass weight k
        - (chartPivotSlack direction mass weight i + chartLeverage direction mass weight i)
            * crossLeverageSq direction mass weight j k
        - (chartPivotSlack direction mass weight j + chartLeverage direction mass weight j)
            * crossLeverageSq direction mass weight i k
        - (chartPivotSlack direction mass weight k + chartLeverage direction mass weight k)
            * crossLeverageSq direction mass weight i j := by
    rw [sub_mul, hbudget, hcross]; ring
  rw [hexpand]
  nlinarith [hrow, hij0, hik0, hjk0, hcapI, hcapJ, hcapK, hcapNonneg,
    mul_le_mul_of_nonneg_right hcapI hjk0, mul_le_mul_of_nonneg_right hcapJ hik0,
    mul_le_mul_of_nonneg_right hcapK hij0]

/-- **THE ROW-BUDGET CELL.**  A strictly positive definite selection out of the
pivot slacks and the leverages ALONE.  No cross entry, no boosted cross and no
determinant appears in the hypothesis.  This is the three by three analogue of
the landed pair certificate `Gtz.pair_minor_pos_of_leverage_slack`. -/
theorem posDef_directionChartGap_compl_triple_of_leverageRow
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hmass : ∀ c, 0 < mass c) (hweight : ∀ c, 0 < weight c) (hwlt : ∀ c, weight c < 1)
    (hpivot : fullPivot direction mass weight i < 1)
    (hpair : pairBoostedCrossSq direction mass weight i j
      < (1 - fullPivot direction mass weight i) * (1 - fullPivot direction mass weight j))
    (cap : ℝ) (hcapNonneg : 0 ≤ cap)
    (hcapI : chartPivotSlack direction mass weight i
      + chartLeverage direction mass weight i ≤ cap)
    (hcapJ : chartPivotSlack direction mass weight j
      + chartLeverage direction mass weight j ≤ cap)
    (hcapK : chartPivotSlack direction mass weight k
      + chartLeverage direction mass weight k ≤ cap)
    (hcell : cap * ((chartLeverage direction mass weight i
            * (1 - chartLeverage direction mass weight i)
          + chartLeverage direction mass weight j
            * (1 - chartLeverage direction mass weight j)
          + chartLeverage direction mass weight k
            * (1 - chartLeverage direction mass weight k)) / 2)
      < chartPivotSlack direction mass weight i * chartPivotSlack direction mass weight j
          * chartPivotSlack direction mass weight k) :
    (directionChartGap direction mass weight
      (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef := by
  have hslack : ∀ c, 0 ≤ chartSlack mass weight c := fun c =>
    (chartSlack_pos mass weight c (hmass c) (hweight c) (hwlt c)).le
  have hboost : ∀ c, 0 ≤ mass c / weight c := fun c => (div_pos (hmass c) (hweight c)).le
  have hge := pairDetBudget_sub_pivotCrossSum_mul_coweight_ge direction mass weight huniv hslack
    hij hik hjk (ne_of_gt (hweight i)) (ne_of_gt (hweight j)) (ne_of_gt (hweight k))
    cap hcapI hcapJ hcapK hcapNonneg
  have hcoI : (0 : ℝ) < 1 - weight i := by linarith [hwlt i]
  have hcoJ : (0 : ℝ) < 1 - weight j := by linarith [hwlt j]
  have hcoK : (0 : ℝ) < 1 - weight k := by linarith [hwlt k]
  have hprod : (0 : ℝ) < (1 - weight i) * (1 - weight j) * (1 - weight k) :=
    mul_pos (mul_pos hcoI hcoJ) hcoK
  have hdiffpos : 0 < (pairDetBudget direction mass weight i j k
      - pivotCrossSum direction mass weight i j k)
      * ((1 - weight i) * (1 - weight j) * (1 - weight k)) := by linarith
  have hdiff : pivotCrossSum direction mass weight i j k
      < pairDetBudget direction mass weight i j k := by
    by_contra hcon
    push Not at hcon
    nlinarith [hdiffpos, hprod, hcon]
  exact posDef_directionChartGap_compl_triple_of_hadamardBudget direction mass weight
    hij hik hjk hboost (div_pos (hmass i) (hweight i)) (div_pos (hmass j) (hweight j))
    (div_pos (hmass k) (hweight k)) huniv hpivot hpair hdiff

/-! ## 5. The refutation shape of the pair-budget cover -/

/-- **A NON-POSITIVE BUDGET AT EVERY TRIPLE REFUTES THE COVER.**  The cover
demands a strictly positive pair budget, so a chart point whose every omitted
triple carries a non-positive budget cannot satisfy it.  Nothing about positive
definiteness is used, which is why the refutation costs one inequality for each
triple and no determinant. -/
theorem not_pairBudgetCovers_of_forall_budget_nonpos
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hnonpos : ∀ i j k : Fin size, i ≠ j → i ≠ k → j ≠ k →
      pairDetBudget direction point.mass point.weight i j k ≤ 0) :
    ¬ PairBudgetCovers direction := by
  intro hcover
  obtain ⟨i, j, k, hij, hik, hjk, _, _, hA, _⟩ := hcover point
  exact absurd hA (not_lt.mpr (hnonpos i j k hij hik hjk))

/-- **The cover is strictly stronger than the consolidated conclusion.**  A
point can carry a strictly positive definite selection and still fail the pair
budget at every triple, because the budget is only the sign-blind half of the
determinant.  This is the statement the witness below inhabits. -/
theorem pairBudgetCovers_strictly_stronger_shape
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hnonpos : ∀ i j k : Fin size, i ≠ j → i ≠ k → j ≠ k →
      pairDetBudget direction point.mass point.weight i j k ≤ 0)
    (hsome : ∃ selected : Finset (Fin size), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosDef) :
    (¬ PairBudgetCovers direction) ∧ ∃ selected : Finset (Fin size), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosDef :=
  ⟨not_pairBudgetCovers_of_forall_budget_nonpos direction point hnonpos, hsome⟩

/-! ## 6. The sign of the triple cross is the whole deficit -/

/-- **THE DEFICIT OF PAIR DATA IS EXACTLY TWICE THE TRIPLE CROSS.**  The
determinant of the complement, divided by the three boosts, is the budget less
twice the triple cross, and the pair data pins only the square of that cross.
So a reader of pair data must certify the worse sign, and the amount it gives
away is `2 * |W|`. -/
theorem pairBudget_deficit_eq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) :
    (pairDetBudget direction mass weight i j k
        - 2 * tripleBoostedCross direction mass weight i j k)
      - (pairDetBudget direction mass weight i j k
        - 2 * |tripleBoostedCross direction mass weight i j k|)
      = 2 * (|tripleBoostedCross direction mass weight i j k|
          - tripleBoostedCross direction mass weight i j k) := by
  ring

/-- **A NEGATIVE BUDGET FORCES A NEGATIVE TRIPLE CROSS AT A WORKING TRIPLE.**
If the budget is non-positive and the determinant is positive, the triple cross
carries the whole positivity and is strictly negative.  This is the exact
mechanism by which the witness below defeats every reader of pair data. -/
theorem tripleBoostedCross_neg_of_budget_nonpos_of_det_pos
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (hbudget : pairDetBudget direction mass weight i j k ≤ 0)
    (hdet : 0 < complementTripleDeterminant direction mass weight i j k) :
    tripleBoostedCross direction mass weight i j k < 0 := by
  have hiff := (complementTripleDeterminant_pos_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK).mp hdet
  linarith

/-- **AND THEN THE PAIR-BUDGET CELL CANNOT FIRE THERE.**  With a non-positive
budget the square condition is unreachable, whatever the boosted crosses are.
So the cell is silent at exactly the triples the witness needs. -/
theorem not_pairBudget_cell_of_budget_nonpos
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hbudget : pairDetBudget direction mass weight i j k ≤ 0) :
    ¬ (0 < pairDetBudget direction mass weight i j k
      ∧ 4 * (pairBoostedCrossSq direction mass weight i j
          * pairBoostedCrossSq direction mass weight i k
          * pairBoostedCrossSq direction mass weight j k)
        < pairDetBudget direction mass weight i j k ^ 2) := by
  rintro ⟨hpos, -⟩
  linarith

end Gtz
