import Gtz.Wave.ThreeLinesHeavyReadingCoverRefuter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The weight-free excess floor

The two allocated budget cells split into a MASS half and a WEIGHT half.  The
mass half asks three inequalities in the outside masses alone.  The weight half
asks three LOAD inequalities of the shape

  `(allocation column sum) * weight c  <  mass c * (1 - weight c)`,

which is exactly `allocation column sum < chartExcess mass weight c`.  The
chart excess is the one place a weight survives.

The leverage floor removes it.  On the A2 residual the floor reads
`weight c * det T ≤ leverage c`, and that inequality is EQUIVALENT to

  `mass c * (det T - leverage c) ≤ chartExcess mass weight c * leverage c`,

a lower bound on the chart excess whose right-hand side is the only place a
weight occurs.  Feeding it into a load condition eliminates the weight
completely: a load condition stated in masses and slide alone implies the
budget cell's own load condition at every residual point.

* `Gtz.chartLeverageNumerator_le_det` — the leverage never exceeds the
  determinant.  Unconditional at every chart point with an invertible moment.
* `Gtz.chartExcess_mul_leverageNumerator_ge` — the weight-free excess floor.
* `Gtz.chartLoad_of_massOnlyLoad` — the load bridge.
* `Gtz.ThreeLinesMassOnlyVertexCellFires`, `Gtz.ThreeLinesMassOnlyFreeCellFires`
  — the two budget cells with every weight eliminated.
* `Gtz.exists_posDef_threeLines_of_massOnlyCellFires` — either mass-only cell
  supplies a strict card-three chart gap on the residual.
* `Gtz.leverageFloorFailurePoint` — the leverage floor is NOT vacuous: at the
  uniform mass and the slide one, a weight of one half already breaks it.

HONEST LIMIT.  The mass-only cells are SUFFICIENT conditions for the budget
cells, not new ones.  Adding their negations to A2 gains nothing, because the
budget blindness already implies them.  What they buy is decidability: the
firing test now reads masses and the slide only, and a solver never has to
guess a weight.
-/

namespace Gtz

open Matrix Finset

/-! ## The leverage never exceeds the determinant -/

/-- **The leverage is capped by the determinant.**  This is the chart reading of
the per-atom ceiling `Gtz.weighted_leverage_le_one`. -/
theorem chartLeverageNumerator_le_det {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size)
    (hmoment : (∑ l, point.mass l • atomMatrix (direction l)).PosDef) (label : Fin size) :
    chartLeverageNumerator direction point.mass label
      ≤ (∑ l, point.mass l • atomMatrix (direction l)).det := by
  obtain ⟨design, hweight, -, hleverage⟩ :=
    exists_design_of_chartPoint_withLeverage direction point hmoment
  have hshare := weighted_leverage_le_one design label
  rw [hweight, hleverage label,
    dotProduct_inv_mulVec_eq direction point.mass label] at hshare
  have hw : 0 < point.weight label := point.weight_pos label
  have hdet : 0 < (∑ l, point.mass l • atomMatrix (direction l)).det := hmoment.det_pos
  have hrewrite : point.weight label *
      (point.mass label / point.weight label *
        (((∑ l, point.mass l • atomMatrix (direction l)).det)⁻¹ *
          (direction label ⬝ᵥ
            ((∑ l, point.mass l • atomMatrix (direction l)).adjugate *ᵥ direction label))))
      = chartLeverageNumerator direction point.mass label
          / (∑ l, point.mass l • atomMatrix (direction l)).det := by
    rw [chartLeverageNumerator]
    field_simp
  rw [hrewrite, div_le_one hdet] at hshare
  exact hshare

/-- On the residual the leverage is strictly positive: the floor alone bounds it
below by the weight times the determinant. -/
theorem chartLeverageNumerator_pos_of_floor {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size)
    (hdet : 0 < (∑ l, point.mass l • atomMatrix (direction l)).det)
    (hfloor : ChartLeverageFloor direction point) (label : Fin size) :
    0 < chartLeverageNumerator direction point.mass label :=
  lt_of_lt_of_le (mul_pos (point.weight_pos label) hdet) (hfloor label)

/-! ## The weight-free excess floor -/

/-- **The weight-free excess floor.**  The leverage floor is exactly a lower
bound on the chart excess whose data is the masses and the direction family.
The two inequalities are equivalent, cleared of every denominator. -/
theorem chartExcess_mul_leverageNumerator_ge {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (hfloor : ChartLeverageFloor direction point) (label : Fin size) :
    point.mass label *
        ((∑ l, point.mass l • atomMatrix (direction l)).det
          - chartLeverageNumerator direction point.mass label)
      ≤ chartExcess point.mass point.weight label
          * chartLeverageNumerator direction point.mass label := by
  have hw : 0 < point.weight label := point.weight_pos label
  have hm : 0 < point.mass label := point.mass_pos label
  have hkey := hfloor label
  rw [chartExcess, div_mul_eq_mul_div, le_div_iff₀ hw]
  nlinarith [mul_le_mul_of_nonneg_left hkey hm.le]

/-- **The load bridge.**  A load condition stated in the masses and the
determinant alone implies the load condition that a budget cell demands. -/
theorem chartLoad_of_massOnlyLoad {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (point : DirectionChartPoint size)
    (hdet : 0 < (∑ l, point.mass l • atomMatrix (direction l)).det)
    (hfloor : ChartLeverageFloor direction point) (label : Fin size) (loadSum : ℝ)
    (hload : loadSum * chartLeverageNumerator direction point.mass label
      < point.mass label *
        ((∑ l, point.mass l • atomMatrix (direction l)).det
          - chartLeverageNumerator direction point.mass label)) :
    loadSum * point.weight label < point.mass label * (1 - point.weight label) := by
  have hpos := chartLeverageNumerator_pos_of_floor direction point hdet hfloor label
  have hw : 0 < point.weight label := point.weight_pos label
  have hchain : loadSum * chartLeverageNumerator direction point.mass label
      < chartExcess point.mass point.weight label
        * chartLeverageNumerator direction point.mass label :=
    lt_of_lt_of_le hload (chartExcess_mul_leverageNumerator_ge direction point hfloor label)
  have hless : loadSum < chartExcess point.mass point.weight label :=
    lt_of_mul_lt_mul_right (by linarith [hchain]) hpos.le
  have hexcess : chartExcess point.mass point.weight label * point.weight label
      = point.mass label * (1 - point.weight label) := by
    rw [chartExcess]
    field_simp
  calc loadSum * point.weight label
      < chartExcess point.mass point.weight label * point.weight label :=
        mul_lt_mul_of_pos_right hless hw
    _ = point.mass label * (1 - point.weight label) := hexcess

/-! ## The two mass-only budget cells -/

/-- The determinant of the three-lines mass moment. -/
noncomputable def threeLinesMomentDet (slide : ℝ) (mass : Fin 6 → ℝ) : ℝ :=
  (∑ l, mass l • atomMatrix (threeLinesDirection slide l)).det

/-- The determinant-cleared leverage of one three-lines label. -/
noncomputable def threeLinesLeverage (slide : ℝ) (mass : Fin 6 → ℝ) (label : Fin 6) : ℝ :=
  chartLeverageNumerator (threeLinesDirection slide) mass label

/-- **The mass-only vertex cell.**  The three mass budget conditions of
`Gtz.ThreeLinesVertexBudgetCellFires`, with its three load conditions replaced
by weight-free ones. -/
def ThreeLinesMassOnlyVertexCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ allocation : ThreeLinesPositiveAllocation,
    point.mass 2 *
        (allocation.uAB * allocation.uAC + allocation.uAA * allocation.uAC)
      ≤ allocation.uAA * allocation.uAB * allocation.uAC ∧
    point.mass 4 *
        (allocation.uBB * allocation.uBC + allocation.uBA * allocation.uBB)
      ≤ allocation.uBA * allocation.uBB * allocation.uBC ∧
    point.mass 5 *
        (allocation.uCA * allocation.uCC +
          slide ^ 2 * (allocation.uCA * allocation.uCB))
      ≤ allocation.uCA * allocation.uCB * allocation.uCC ∧
    (allocation.uAA + allocation.uBA + allocation.uCA)
        * threeLinesLeverage slide point.mass 0
      < point.mass 0 * (threeLinesMomentDet slide point.mass
          - threeLinesLeverage slide point.mass 0) ∧
    (allocation.uAB + allocation.uBB + allocation.uCB)
        * threeLinesLeverage slide point.mass 1
      < point.mass 1 * (threeLinesMomentDet slide point.mass
          - threeLinesLeverage slide point.mass 1) ∧
    (allocation.uAC + allocation.uBC + allocation.uCC)
        * threeLinesLeverage slide point.mass 3
      < point.mass 3 * (threeLinesMomentDet slide point.mass
          - threeLinesLeverage slide point.mass 3)

/-- **The mass-only free cell.**  The same elimination at the free triple. -/
def ThreeLinesMassOnlyFreeCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ allocation : ThreeLinesPositiveAllocation,
    point.mass 0 *
        (allocation.uAB * allocation.uAC +
          slide ^ 2 * (allocation.uAA * allocation.uAC) +
          allocation.uAA * allocation.uAB)
      ≤ (slide + 1) ^ 2 * (allocation.uAA * allocation.uAB * allocation.uAC) ∧
    point.mass 1 *
        (slide ^ 2 * (allocation.uBB * allocation.uBC) +
          slide ^ 2 * (allocation.uBA * allocation.uBC) +
          allocation.uBA * allocation.uBB)
      ≤ (slide + 1) ^ 2 * (allocation.uBA * allocation.uBB * allocation.uBC) ∧
    point.mass 3 *
        (allocation.uCB * allocation.uCC + allocation.uCA * allocation.uCC +
          allocation.uCA * allocation.uCB)
      ≤ (slide + 1) ^ 2 * (allocation.uCA * allocation.uCB * allocation.uCC) ∧
    (allocation.uAA + allocation.uBA + allocation.uCA)
        * threeLinesLeverage slide point.mass 2
      < point.mass 2 * (threeLinesMomentDet slide point.mass
          - threeLinesLeverage slide point.mass 2) ∧
    (allocation.uAB + allocation.uBB + allocation.uCB)
        * threeLinesLeverage slide point.mass 4
      < point.mass 4 * (threeLinesMomentDet slide point.mass
          - threeLinesLeverage slide point.mass 4) ∧
    (allocation.uAC + allocation.uBC + allocation.uCC)
        * threeLinesLeverage slide point.mass 5
      < point.mass 5 * (threeLinesMomentDet slide point.mass
          - threeLinesLeverage slide point.mass 5)

/-- The mass-only vertex cell implies the vertex budget cell on the residual. -/
theorem threeLinesVertexBudgetCellFires_of_massOnly (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hfloor : ChartLeverageFloor (threeLinesDirection slide) point)
    (hcell : ThreeLinesMassOnlyVertexCellFires slide point) :
    ThreeLinesVertexBudgetCellFires slide point := by
  obtain ⟨allocation, htwo, hfour, hfive, hzero, hone, hthree⟩ := hcell
  have hdet : 0 < (∑ l, point.mass l • atomMatrix (threeLinesDirection slide l)).det :=
    (posDef_massMoment_threeLinesDirection slide point).det_pos
  exact ⟨allocation, htwo, hfour, hfive,
    chartLoad_of_massOnlyLoad _ point hdet hfloor 0 _ hzero,
    chartLoad_of_massOnlyLoad _ point hdet hfloor 1 _ hone,
    chartLoad_of_massOnlyLoad _ point hdet hfloor 3 _ hthree⟩

/-- The mass-only free cell implies the free budget cell on the residual. -/
theorem threeLinesFreeBudgetCellFires_of_massOnly (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hfloor : ChartLeverageFloor (threeLinesDirection slide) point)
    (hcell : ThreeLinesMassOnlyFreeCellFires slide point) :
    ThreeLinesFreeBudgetCellFires slide point := by
  obtain ⟨allocation, hzero, hone, hthree, htwo, hfour, hfive⟩ := hcell
  have hdet : 0 < (∑ l, point.mass l • atomMatrix (threeLinesDirection slide l)).det :=
    (posDef_massMoment_threeLinesDirection slide point).det_pos
  exact ⟨allocation, hzero, hone, hthree,
    chartLoad_of_massOnlyLoad _ point hdet hfloor 2 _ htwo,
    chartLoad_of_massOnlyLoad _ point hdet hfloor 4 _ hfour,
    chartLoad_of_massOnlyLoad _ point hdet hfloor 5 _ hfive⟩

/-- **Either mass-only cell supplies a strict card-three chart gap.**  The only
weight-side input is the leverage floor, which is free on the residual. -/
theorem exists_posDef_threeLines_of_massOnlyCellFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hfloor : ChartLeverageFloor (threeLinesDirection slide) point)
    (hcell : ThreeLinesMassOnlyVertexCellFires slide point ∨
      ThreeLinesMassOnlyFreeCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with hvertex | hfree
  · exact ⟨{0, 1, 3}, by decide,
      posDef_threeLines_vertexCell_of_fires slide point
        (threeLinesVertexBudgetCellFires_of_massOnly slide point hfloor hvertex)⟩
  · exact ⟨{2, 4, 5}, by decide,
      posDef_threeLines_freeCell_of_fires slide hadmissible point
        (threeLinesFreeBudgetCellFires_of_massOnly slide point hfloor hfree)⟩

/-! ## The leverage floor is not vacuous -/

/-- Uniform masses. -/
noncomputable def leverageFloorFailureMass : Fin 6 → ℝ := fun _ => 1

/-- One heavy weight, five light ones. -/
noncomputable def leverageFloorFailureWeight : Fin 6 → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 10
  | 2 => 1 / 10
  | 3 => 1 / 10
  | 4 => 1 / 10
  | 5 => 1 / 10

/-- A chart point at the slide one whose first weight overshoots its own
leverage. -/
noncomputable def leverageFloorFailurePoint : DirectionChartPoint 6 where
  mass := leverageFloorFailureMass
  weight := leverageFloorFailureWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [leverageFloorFailureMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [leverageFloorFailureWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [leverageFloorFailureWeight]

/-- The mass moment of that point is the matrix `2 I + J`. -/
theorem leverageFloorFailure_moment :
    (∑ l, leverageFloorFailurePoint.mass l • atomMatrix (threeLinesDirection 1 l))
      = !![3, 1, 1; 1, 3, 1; 1, 1, 3] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [Fin.sum_univ_six, leverageFloorFailurePoint, leverageFloorFailureMass,
      atomMatrix, threeLinesDirection, Matrix.vecMulVec_apply] <;> norm_num

/-- **The leverage floor is not vacuous.**  At the uniform mass and the slide
one every leverage equals two fifths of the determinant, so a weight of one
half already breaks the floor. -/
theorem leverageFloorFailurePoint_not_chartLeverageFloor :
    ¬ ChartLeverageFloor (threeLinesDirection 1) leverageFloorFailurePoint := by
  intro hfloor
  have hzero := hfloor 0
  have hdetValue : (!![3, 1, 1; 1, 3, 1; 1, 1, 3] : Matrix (Fin 3) (Fin 3) ℝ).det = 20 := by
    rw [Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [chartLeverageNumerator, leverageFloorFailure_moment, hdetValue,
    Matrix.adjugate_fin_three_of] at hzero
  simp [threeLinesDirection, leverageFloorFailurePoint, leverageFloorFailureMass,
    leverageFloorFailureWeight, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hzero
  norm_num at hzero

end Gtz
