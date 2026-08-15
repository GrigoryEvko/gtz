/-
# The cross-leverage budget

`Gtz.sum_chartLeverage_eq_three` reads the DIAGONAL of the inverse form against
the slacks and returns the rank.  It says nothing about the off-diagonal, and the
off-diagonal is exactly what a card-three selection needs: the diagonal of the
complement matrix decides the one-by-one minors, the cross entries decide the
rest.

The slack Laplacian supplies the missing law.  Insert the full gap, written as
the slack-weighted atom sum, between the two inverses of a product of inverse
form entries.  One inverse cancels, and the whole ROW energy of a label collapses
to its own diagonal entry:

  `∑ j, s_j * G_ij ^ 2 = G_ii`     (the chart row energy law)

Removing the diagonal term leaves the slack of the leverage cap:

  `∑ j ≠ i, s_j * G_ij ^ 2 = G_ii * (1 - λ_i)`

That is a CEILING on the cross entries of a row, priced by the label's own
leverage.  A pair of labels fails its two-by-two minor only when its cross entry
is large, so the ceiling caps how many partners a label can fail against.  The
budget below states that cap without any division.

The pivot slack `x_i = (1 - w_i)(1 - π_i)` is the natural unit: it is the
diagonal of the complement matrix after the co-weight scaling that makes the
chart and the design agree.  In those units the budget reads

  `x_i * ∑ (j failing with i), x_j ≤ λ_i * (1 - λ_i)`

and the right side is capped by the leverage sum.  At `(6,3)` the leverages total
three over six labels, so the whole cross budget is at most `3/2`.
-/
import Mathlib
import Gtz.Design.ComplementPairCriterion
import Gtz.Design.PivotGramIdempotent

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ## 1. The chart row energy law -/

/-- **The chart row energy law.**  The full-selection gap is the slack
Laplacian, so inserting it between the two inverses of a squared inverse form
entry cancels one inverse.  The slack-weighted energy of a label's whole row of
cross entries is its own diagonal entry.  No positivity beyond invertibility of
the gap is used. -/
theorem sum_chartSlack_mul_fullInverseForm_sq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i : Fin size) :
    ∑ j, chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2
      = fullInverseForm direction mass weight i i := by
  classical
  have hdet : IsUnit (directionChartGap direction mass weight Finset.univ).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt huniv.det_pos)
  have hgapT : (directionChartGap direction mass weight Finset.univ)ᵀ
      = directionChartGap direction mass weight Finset.univ :=
    directionChartGap_transpose direction mass weight Finset.univ
  have hinvT : ((directionChartGap direction mass weight Finset.univ)⁻¹)ᵀ
      = (directionChartGap direction mass weight Finset.univ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hgapT]
  -- the inverse form is the dual probe read against the direction
  have hread : ∀ j : Fin size,
      fullInverseForm direction mass weight i j
        = ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction i)
            ⬝ᵥ direction j := by
    intro j
    rw [dotProduct_comm, fullInverseForm]
    exact dotProduct_mulVec_comm_of_transpose hinvT (direction i) (direction j)
  -- each summand is the dual probe read against one slack-scaled atom
  have hterm : ∀ j : Fin size,
      chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2
        = ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction i) ⬝ᵥ
            ((chartSlack mass weight j • atomMatrix (direction j)) *ᵥ
              ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction i)) := by
    intro j
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix_mulVec, dotProduct_smul,
      smul_eq_mul, hread j,
      dotProduct_comm (direction j)
        ((directionChartGap direction mass weight Finset.univ)⁻¹ *ᵥ direction i)]
    ring
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j), ← dotProduct_sum,
    ← Matrix.sum_mulVec, ← slackLaplacian, ← directionChartGap_univ_eq_slackLaplacian,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec,
    fullInverseForm, dotProduct_comm]

/-- **The off-diagonal row energy.**  Removing the diagonal term from the row
energy leaves the diagonal entry scaled by the slack of the leverage cap. -/
theorem sum_erase_chartSlack_mul_fullInverseForm_sq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (i : Fin size) :
    ∑ j ∈ Finset.univ.erase i,
        chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2
      = fullInverseForm direction mass weight i i
          * (1 - chartLeverage direction mass weight i) := by
  classical
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun j => chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2)
    (Finset.mem_univ i)
  rw [sum_chartSlack_mul_fullInverseForm_sq direction mass weight huniv i] at hsplit
  have hlev : chartLeverage direction mass weight i
      = chartSlack mass weight i * fullInverseForm direction mass weight i i := rfl
  rw [hlev]
  nlinarith [hsplit]

/-! ## 2. The leverage cap -/

/-- **The leverage cap.**  Every chart leverage is at most one.  The row energy
dominates its own diagonal term, and the diagonal entry is nonnegative. -/
theorem chartLeverage_le_one (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ j, 0 ≤ chartSlack mass weight j) (i : Fin size) :
    chartLeverage direction mass weight i ≤ 1 := by
  classical
  have hoff := sum_erase_chartSlack_mul_fullInverseForm_sq direction mass weight huniv i
  have hnonneg : 0 ≤ ∑ j ∈ Finset.univ.erase i,
      chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hslack j) (sq_nonneg _)
  have hdiag := fullInverseForm_self_nonneg direction mass weight huniv i
  rw [hoff] at hnonneg
  rcases hdiag.lt_or_eq with hpos | hzero
  · nlinarith [hnonneg, hpos]
  · have : chartLeverage direction mass weight i = 0 := by
      rw [chartLeverage, ← hzero]; ring
    linarith [this]

/-! ## 3. The pivot slack -/

/-- **The pivot slack of a label.**  The co-weight against the defect of the full
pivot.  This is the diagonal of the complement matrix in the units that make the
chart and the design agree, and the pivot exclusion says exactly that an omitted
label carries positive pivot slack. -/
noncomputable def chartPivotSlack (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i : Fin size) : ℝ :=
  (1 - weight i) * (1 - fullPivot direction mass weight i)

/-- The pivot slack is the co-weight less the leverage. -/
theorem chartPivotSlack_eq_sub_leverage (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) {i : Fin size} (hw : weight i ≠ 0) :
    chartPivotSlack direction mass weight i
      = (1 - weight i) - chartLeverage direction mass weight i := by
  rw [chartPivotSlack, chartLeverage_eq_one_sub_weight_mul_fullPivot direction mass weight hw]
  ring

/-- The co-weight scales the boost to the slack. -/
theorem one_sub_weight_mul_boost (mass weight : Fin size → ℝ) {i : Fin size}
    (hw : weight i ≠ 0) :
    (1 - weight i) * (mass i / weight i) = chartSlack mass weight i := by
  rw [chartSlack]
  field_simp

/-! ## 4. The budget -/

/-- **The cross-leverage budget.**  Fix a label and any set of partners whose
two-by-two complement minor with it fails.  Each failing partner spends at least
the product of the two pivot slacks out of the label's off-diagonal row energy,
and that energy is capped by the label's own leverage.  So the pivot slack of the
label, times the total pivot slack of every partner it fails against, is at most
the leverage times its cap slack.  Division-free, and generic in the size and the
direction family. -/
theorem chartPivotSlack_mul_sum_le_leverage_slack (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hmass : ∀ j, 0 < mass j) (hweight : ∀ j, 0 < weight j) (hwlt : ∀ j, weight j < 1)
    (i : Fin size) (bad : Finset (Fin size)) (hbad : bad ⊆ Finset.univ.erase i)
    (hfail : ∀ j ∈ bad,
      (1 - fullPivot direction mass weight i) * (1 - fullPivot direction mass weight j)
        ≤ (mass i / weight i) * (mass j / weight j)
            * (fullInverseForm direction mass weight i j) ^ 2) :
    chartPivotSlack direction mass weight i
        * ∑ j ∈ bad, chartPivotSlack direction mass weight j
      ≤ chartLeverage direction mass weight i
          * (1 - chartLeverage direction mass weight i) := by
  classical
  have hslackPos : ∀ j, 0 < chartSlack mass weight j := fun j =>
    chartSlack_pos mass weight j (hmass j) (hweight j) (hwlt j)
  -- each failing partner spends the product of the two pivot slacks
  have hstep : ∀ j ∈ bad,
      chartPivotSlack direction mass weight i * chartPivotSlack direction mass weight j
        ≤ chartSlack mass weight i
            * (chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2) := by
    intro j hj
    have hcoi : (0 : ℝ) < 1 - weight i := by linarith [hwlt i]
    have hcoj : (0 : ℝ) < 1 - weight j := by linarith [hwlt j]
    have hmul := mul_le_mul_of_nonneg_left (hfail j hj) (le_of_lt (mul_pos hcoi hcoj))
    have hleft : (1 - weight i) * (1 - weight j)
        * ((1 - fullPivot direction mass weight i)
            * (1 - fullPivot direction mass weight j))
        = chartPivotSlack direction mass weight i
            * chartPivotSlack direction mass weight j := by
      rw [chartPivotSlack, chartPivotSlack]; ring
    have hright : (1 - weight i) * (1 - weight j)
        * ((mass i / weight i) * (mass j / weight j)
            * (fullInverseForm direction mass weight i j) ^ 2)
        = chartSlack mass weight i
            * (chartSlack mass weight j
                * (fullInverseForm direction mass weight i j) ^ 2) := by
      rw [← one_sub_weight_mul_boost mass weight (ne_of_gt (hweight i)),
        ← one_sub_weight_mul_boost mass weight (ne_of_gt (hweight j))]
      ring
    rw [hleft, hright] at hmul
    exact hmul
  -- sum the pointwise bound over the failing partners
  have hsum : chartPivotSlack direction mass weight i
      * ∑ j ∈ bad, chartPivotSlack direction mass weight j
      ≤ chartSlack mass weight i
          * ∑ j ∈ bad,
              chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hstep
  -- the failing partners cost at most the whole off-diagonal row energy
  have hmono : ∑ j ∈ bad,
        chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2
      ≤ ∑ j ∈ Finset.univ.erase i,
        chartSlack mass weight j * (fullInverseForm direction mass weight i j) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hbad
      (fun j _ _ => mul_nonneg (hslackPos j).le (sq_nonneg _))
  have hrow := sum_erase_chartSlack_mul_fullInverseForm_sq direction mass weight huniv i
  have hscaled := mul_le_mul_of_nonneg_left hmono (hslackPos i).le
  rw [hrow] at hscaled
  have hlev : chartSlack mass weight i
      * (fullInverseForm direction mass weight i i
          * (1 - chartLeverage direction mass weight i))
      = chartLeverage direction mass weight i
          * (1 - chartLeverage direction mass weight i) := by
    rw [chartLeverage]; ring
  rw [hlev] at hscaled
  linarith [hsum, hscaled]

/-- **The pair certificate.**  If the leverage budget of a label is strictly
smaller than the product of the two pivot slacks, the two-by-two complement minor
of that pair is strictly positive.  This reads a pair from the two pivots and the
two weights alone, with no cross entry. -/
theorem pair_minor_pos_of_leverage_slack (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hmass : ∀ j, 0 < mass j) (hweight : ∀ j, 0 < weight j) (hwlt : ∀ j, weight j < 1)
    {i j : Fin size} (hij : j ≠ i)
    (hbudget : chartLeverage direction mass weight i
        * (1 - chartLeverage direction mass weight i)
      < chartPivotSlack direction mass weight i * chartPivotSlack direction mass weight j) :
    (mass i / weight i) * (mass j / weight j)
        * (fullInverseForm direction mass weight i j) ^ 2
      < (1 - fullPivot direction mass weight i)
          * (1 - fullPivot direction mass weight j) := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : ({j} : Finset (Fin size)) ⊆ Finset.univ.erase i := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ x⟩
  have hbud := chartPivotSlack_mul_sum_le_leverage_slack direction mass weight huniv
    hmass hweight hwlt i {j} hsub (by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact hcon)
  rw [Finset.sum_singleton] at hbud
  linarith [hbud, hbudget]

/-! ## 5. The total budget at six labels -/

/-- **The cross budget ceiling at six labels.**  The leverages total three, so
the sum of every label's leverage cap slack is three less the sum of the squared
leverages, and six squares summing from a total of three are at least `3/2`. -/
theorem sum_chartLeverage_mul_one_sub_le (direction : Fin 6 → (Fin 3 → ℝ))
    (mass weight : Fin 6 → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    ∑ i, chartLeverage direction mass weight i
        * (1 - chartLeverage direction mass weight i) ≤ 3 / 2 := by
  classical
  set lev : Fin 6 → ℝ := fun i => chartLeverage direction mass weight i with hlev
  have hsum : ∑ i, lev i = 3 := sum_chartLeverage_eq_three direction mass weight huniv
  have hexpand : ∑ i, lev i * (1 - lev i) = (∑ i, lev i) - ∑ i, lev i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexpand, hsum]
  have hsq : (3 : ℝ) / 2 ≤ ∑ i, lev i ^ 2 := by
    rw [Fin.sum_univ_six] at hsum ⊢
    nlinarith [sq_nonneg (lev 0 - lev 1), sq_nonneg (lev 0 - lev 2), sq_nonneg (lev 0 - lev 3),
      sq_nonneg (lev 0 - lev 4), sq_nonneg (lev 0 - lev 5), sq_nonneg (lev 1 - lev 2),
      sq_nonneg (lev 1 - lev 3), sq_nonneg (lev 1 - lev 4), sq_nonneg (lev 1 - lev 5),
      sq_nonneg (lev 2 - lev 3), sq_nonneg (lev 2 - lev 4), sq_nonneg (lev 2 - lev 5),
      sq_nonneg (lev 3 - lev 4), sq_nonneg (lev 3 - lev 5), sq_nonneg (lev 4 - lev 5)]
  linarith [hsq]

/-- **The complementary leverage budget.**  A label of full pivot at least one
carries leverage at least its own co-weight, because the leverage is the pivot
scaled by that co-weight.  So a set of such heavy labels absorbs its own
cardinality less its total weight, and the labels outside it share only what the
rank leaves.  At six labels with three heavy ones the outside labels carry
leverage at most the heavy weight, which is at most one. -/
theorem sum_chartLeverage_compl_le (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6)
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (heavy : Finset (Fin 6))
    (hheavy : ∀ c ∈ heavy, 1 ≤ fullPivot direction point.mass point.weight c) :
    ∑ c ∈ heavyᶜ, chartLeverage direction point.mass point.weight c
      ≤ 3 - (heavy.card : ℝ) + ∑ c ∈ heavy, point.weight c := by
  classical
  have hwlt : ∀ c : Fin 6, point.weight c < 1 := fun c =>
    chartPoint_weight_lt_one point c
  -- a heavy label carries at least its co-weight in leverage
  have hstep : ∀ c ∈ heavy,
      1 - point.weight c ≤ chartLeverage direction point.mass point.weight c := by
    intro c hc
    rw [chartLeverage_eq_one_sub_weight_mul_fullPivot direction point.mass point.weight
      (ne_of_gt (point.weight_pos c))]
    have hco : (0 : ℝ) < 1 - point.weight c := by linarith [hwlt c]
    nlinarith [hheavy c hc, hco]
  have hheavySum : (heavy.card : ℝ) - ∑ c ∈ heavy, point.weight c
      ≤ ∑ c ∈ heavy, chartLeverage direction point.mass point.weight c := by
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    linarith [hsum]
  have hsplit : ∑ c ∈ heavy, chartLeverage direction point.mass point.weight c
      + ∑ c ∈ heavyᶜ, chartLeverage direction point.mass point.weight c = 3 := by
    rw [Finset.sum_add_sum_compl]
    exact sum_chartLeverage_eq_three direction point.mass point.weight huniv
  linarith [hheavySum, hsplit]

/-- **The pivot slacks total two at six labels.**  The weights are a probability
vector and the leverages total the rank, so the pivot slacks total `6 - 1 - 3`. -/
theorem sum_chartPivotSlack_eq_two (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6)
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef) :
    ∑ i, chartPivotSlack direction point.mass point.weight i = 2 := by
  classical
  have hstep : ∀ i : Fin 6, chartPivotSlack direction point.mass point.weight i
      = (1 - point.weight i) - chartLeverage direction point.mass point.weight i := fun i =>
    chartPivotSlack_eq_sub_leverage direction point.mass point.weight
      (ne_of_gt (point.weight_pos i))
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, sum_chartLeverage_eq_three direction point.mass point.weight huniv,
    point.weight_sum_one]
  norm_num

end Gtz
