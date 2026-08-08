import Gtz.Design.RigidityBridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace Gtz
open Matrix Finset
variable {size : ℕ}

theorem directionChartGap_eq_excessSplit (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (selected : Finset (Fin size)) :
    directionChartGap direction mass weight selected
      = (∑ label ∈ selected,
          (mass label * (1 - weight label) / weight label) • atomMatrix (direction label))
        - ∑ label ∈ selectedᶜ, mass label • atomMatrix (direction label) := by
  classical
  have hsplit : ∑ label, mass label • atomMatrix (direction label)
      = (∑ label ∈ selected, mass label • atomMatrix (direction label))
        + ∑ label ∈ selectedᶜ, mass label • atomMatrix (direction label) :=
    (Finset.sum_add_sum_compl selected
      (fun label => mass label • atomMatrix (direction label))).symm
  have hcombine : ∀ label ∈ selected,
      (mass label / weight label) • atomMatrix (direction label)
        - mass label • atomMatrix (direction label)
      = (mass label * (1 - weight label) / weight label)
          • atomMatrix (direction label) := by
    intro label _
    rw [← sub_smul]
    congr 1
    field_simp [hweightNe label]
  rw [directionChartGap, hsplit, sub_add_eq_sub_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl hcombine

/-- The weight EXCESS of a chart label: `m (1 - w) / w`, the coefficient a
SELECTED direction contributes to the chart gap. -/
noncomputable def chartExcess (mass weight : Fin size → ℝ) (label : Fin size) : ℝ :=
  mass label * (1 - weight label) / weight label

theorem chartExcess_pos (mass weight : Fin size → ℝ) (label : Fin size)
    (hmassPos : 0 < mass label) (hweightPos : 0 < weight label)
    (hweightLtOne : weight label < 1) : 0 < chartExcess mass weight label := by
  rw [chartExcess]
  exact div_pos (mul_pos hmassPos (by linarith)) hweightPos

/-- A symmetric `3 x 3` matrix whose diagonal strictly dominates bounds on its
off-diagonal magnitudes is positive definite.  The bounds are given as squares,
so no absolute value appears. -/
private theorem crossTermBound (bound cross leftVal rightVal : ℝ)
    (hboundNonneg : 0 ≤ bound) (hsquare : cross ^ 2 ≤ bound ^ 2) :
    0 ≤ bound * (leftVal ^ 2 + rightVal ^ 2) + 2 * cross * leftVal * rightVal := by
  have hsumNonneg : (0 : ℝ) ≤ leftVal ^ 2 + rightVal ^ 2 := by positivity
  by_cases hsign : 0 ≤ cross
  · have hle : cross ≤ bound := by
      nlinarith [hsquare, hsign, hboundNonneg, sq_nonneg (cross - bound)]
    have hgap : 0 ≤ (bound - cross) * (leftVal ^ 2 + rightVal ^ 2) :=
      mul_nonneg (by linarith) hsumNonneg
    have hsquareTerm : 0 ≤ cross * (leftVal + rightVal) ^ 2 :=
      mul_nonneg hsign (sq_nonneg _)
    nlinarith [hgap, hsquareTerm]
  · push Not at hsign
    have hle : -cross ≤ bound := by
      nlinarith [hsquare, hsign, hboundNonneg, sq_nonneg (cross + bound)]
    have hgap : 0 ≤ (bound + cross) * (leftVal ^ 2 + rightVal ^ 2) :=
      mul_nonneg (by linarith) hsumNonneg
    have hsquareTerm : 0 ≤ (-cross) * (leftVal - rightVal) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [hgap, hsquareTerm]

theorem posDef_of_dominance_fin_three
    (diagOne diagTwo diagThree boundOneTwo boundOneThree boundTwoThree
      crossOneTwo crossOneThree crossTwoThree : ℝ)
    (hboundOneTwo : 0 ≤ boundOneTwo) (hboundOneThree : 0 ≤ boundOneThree)
    (hboundTwoThree : 0 ≤ boundTwoThree)
    (hsquareOneTwo : crossOneTwo ^ 2 ≤ boundOneTwo ^ 2)
    (hsquareOneThree : crossOneThree ^ 2 ≤ boundOneThree ^ 2)
    (hsquareTwoThree : crossTwoThree ^ 2 ≤ boundTwoThree ^ 2)
    (hdominateOne : boundOneTwo + boundOneThree < diagOne)
    (hdominateTwo : boundOneTwo + boundTwoThree < diagTwo)
    (hdominateThree : boundOneThree + boundTwoThree < diagThree) :
    (!![diagOne, crossOneTwo, crossOneThree;
        crossOneTwo, diagTwo, crossTwoThree;
        crossOneThree, crossTwoThree, diagThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hform : vecArg ⬝ᵥ ((!![diagOne, crossOneTwo, crossOneThree;
          crossOneTwo, diagTwo, crossTwoThree;
          crossOneThree, crossTwoThree, diagThree]
        : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = diagOne * vecArg 0 ^ 2 + diagTwo * vecArg 1 ^ 2 + diagThree * vecArg 2 ^ 2
          + 2 * crossOneTwo * vecArg 0 * vecArg 1
          + 2 * crossOneThree * vecArg 0 * vecArg 2
          + 2 * crossTwoThree * vecArg 1 * vecArg 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    have hone := crossTermBound boundOneTwo crossOneTwo (vecArg 0) (vecArg 1)
      hboundOneTwo hsquareOneTwo
    have htwo := crossTermBound boundOneThree crossOneThree (vecArg 0) (vecArg 2)
      hboundOneThree hsquareOneThree
    have hthree := crossTermBound boundTwoThree crossTwoThree (vecArg 1) (vecArg 2)
      hboundTwoThree hsquareTwoThree
    have hcoord : vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by funext coordIndex; fin_cases coordIndex <;> simp [hall.1, hall.2.1, hall.2.2])
    rcases hcoord with hcoord | hcoord | hcoord <;>
      [ (have hsq : 0 < vecArg 0 ^ 2 := by positivity);
        (have hsq : 0 < vecArg 1 ^ 2 := by positivity);
        (have hsq : 0 < vecArg 2 ^ 2 := by positivity)] <;>
      nlinarith [hone, htwo, hthree, sq_nonneg (vecArg 0), sq_nonneg (vecArg 1),
        sq_nonneg (vecArg 2)]

/-! ## The three-lines chart: the triangle cell

The chart's three lines are the three coordinate planes and its triangle is the
coordinate frame `{0, 1, 3}`, so the triangle gap has a closed form in the six
masses, the three triangle excesses and the slide. -/

theorem threeLinesGap_triangle_eq (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) :
    directionChartGap (threeLinesDirection slide) mass weight {0, 1, 3}
      = !![chartExcess mass weight 0 - mass 2 - mass 4, -mass 2, -mass 4;
           -mass 2, chartExcess mass weight 1 - mass 2 - mass 5, -(slide * mass 5);
           -mass 4, -(slide * mass 5),
             chartExcess mass weight 3 - mass 4 - slide ^ 2 * mass 5] := by
  classical
  rw [directionChartGap_eq_excessSplit _ mass weight hweightNe]
  have hcompl : ({0, 1, 3} : Finset (Fin 6))ᶜ = {2, 4, 5} := by decide
  rw [hcompl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [atomMatrix, chartExcess,
      threeLinesDirection_zero, threeLinesDirection_one, threeLinesDirection_two,
      threeLinesDirection_three, threeLinesDirection_four, threeLinesDirection_five,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] <;>
    ring

/-- **The triangle cell of the three-lines chart.**  When each triangle label's
weight excess strictly dominates twice the side masses it meets, the coordinate
triple `{0, 1, 3}` dominates STRICTLY.  `slideBound` is any bound on `|slide|`,
so the statement stays absolute-value free and holds on the whole admissible
parameter line, fundamental domain included. -/
theorem threeLines_triangle_posDef_of_dominance (slide slideBound : ℝ)
    (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0)
    (hmassTwo : 0 ≤ mass 2) (hmassFour : 0 ≤ mass 4) (hmassFive : 0 ≤ mass 5)
    (hslideBoundNonneg : 0 ≤ slideBound) (hslideSquare : slide ^ 2 ≤ slideBound ^ 2)
    (hdominateZero : 2 * (mass 2 + mass 4) < chartExcess mass weight 0)
    (hdominateOne : 2 * mass 2 + mass 5 * (1 + slideBound) < chartExcess mass weight 1)
    (hdominateThree : 2 * mass 4 + mass 5 * (slide ^ 2 + slideBound)
      < chartExcess mass weight 3) :
    (directionChartGap (threeLinesDirection slide) mass weight {0, 1, 3}).PosDef := by
  rw [threeLinesGap_triangle_eq slide mass weight hweightNe]
  refine posDef_of_dominance_fin_three _ _ _ (mass 2) (mass 4) (slideBound * mass 5)
    _ _ _ hmassTwo hmassFour (mul_nonneg hslideBoundNonneg hmassFive) ?_ ?_ ?_ ?_ ?_ ?_
  · nlinarith [sq_nonneg (mass 2)]
  · nlinarith [sq_nonneg (mass 4)]
  · nlinarith [hslideSquare, sq_nonneg (mass 5), mul_nonneg hslideBoundNonneg hmassFive]
  · linarith
  · nlinarith [hdominateOne]
  · nlinarith [hdominateThree]

end Gtz
