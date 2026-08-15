/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.TypeAExchangeReduction
import Gtz.Design.GaugeWallKernelLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The gauge-wall type-A exchange is false

`Gtz.KFourGaugeWallTypeAExchange` was isolated after an exact-rational sweep
reported a positive one-label exchange at every sampled type-A stall on the
canonical gauge wall.  The statement is nevertheless false.  This module ships
an exact rational point satisfying its **full** antecedent:

* the gauge-star gap is the positive rank-one form
  `(1 / 21025) * (1,72,72)(1,72,72)^T`;
* the two displayed kernel vectors are nonzero and noncollinear;
* pointer `2` is outside the wall star, is orthogonal to the second kernel, and
  reads strictly positively at the tight kernel on every selection containing
  it;
* the four-cycle `{0,1,4,5}` is positive definite and stalled;
* all eight one-label exchanges out of that four-cycle fail positive
  definiteness.

This is not a counterexample to the K4 chart statement.  The nonlocal spanning
trees `{0,2,3}` and `{1,2,3}` are both positive definite.  The fixture therefore
does two jobs: it refutes the exchange selection and identifies the correct
repair.  The type-A producer must ask directly for a strict tree, not for an
exchange adjacent to the stalled four-cycle.
-/

namespace Gtz

open Matrix

/-! ## 1. The exact wall point -/

/-- The weights of the exchange refuter.  Almost all weight sits at the gauge
axis label `3`; the two labels of the stalled cycle adjacent to the thin axis
carry `1/144`, and the remaining dust is `1/18000`. -/
noncomputable def gaugeTypeAExchangeRefuterWeight : Fin 6 → ℝ
  | 0 => 1 / 144
  | 1 => 1 / 144
  | 2 => 1 / 18000
  | 3 => 17747 / 18000
  | 4 => 1 / 18000
  | 5 => 1 / 18000

/-- The masses of the exchange refuter.  They are the canonical gauge-wall
parametrization at axis `(1,72,72)/145` and scale one. -/
noncomputable def gaugeTypeAExchangeRefuterMass : Fin 6 → ℝ
  | 0 => 72 / 21025
  | 1 => 72 / 21025
  | 2 => 5184 / 21025
  | 3 => 17747 / 36685
  | 4 => 72 / 2609855
  | 5 => 72 / 2609855

/-- The exact rational chart point refuting the wall exchange. -/
noncomputable def gaugeTypeAExchangeRefuterPoint : DirectionChartPoint 6 where
  mass := gaugeTypeAExchangeRefuterMass
  weight := gaugeTypeAExchangeRefuterWeight
  mass_pos := by
    intro label
    fin_cases label <;> norm_num [gaugeTypeAExchangeRefuterMass]
  weight_pos := by
    intro label
    fin_cases label <;> norm_num [gaugeTypeAExchangeRefuterWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num [gaugeTypeAExchangeRefuterWeight]

@[simp] theorem gaugeTypeAExchangeRefuterPoint_mass_eq :
    gaugeTypeAExchangeRefuterPoint.mass = gaugeTypeAExchangeRefuterMass := rfl

@[simp] theorem gaugeTypeAExchangeRefuterPoint_weight_eq :
    gaugeTypeAExchangeRefuterPoint.weight = gaugeTypeAExchangeRefuterWeight := rfl

/-- The positive wall axis. -/
noncomputable def gaugeTypeAExchangeRefuterAxis : Fin 3 → ℝ := ![1, 72, 72]

/-- The tight kernel carrying pointer `2`. -/
noncomputable def gaugeTypeAExchangeRefuterTight : Fin 3 → ℝ := ![0, 1, -1]

/-- The second wall kernel, chosen orthogonal to chart direction `2`. -/
noncomputable def gaugeTypeAExchangeRefuterSecond : Fin 3 → ℝ := ![-144, 1, 1]

/-- The stalled type-A four-cycle. -/
def gaugeTypeAExchangeRefuterSelection : Finset (Fin 6) := {0, 1, 4, 5}

/-! ## 2. The full gauge-wall corank package -/

/-- The gauge wall is exactly a positive rank-one axis atom. -/
theorem gaugeTypeAExchangeRefuter_wall_gap_eq :
    directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight ({3, 4, 5} : Finset (Fin 6))
      = (1 / 21025 : ℝ) • atomMatrix gaugeTypeAExchangeRefuterAxis := by
  rw [kFourGap_treeThreeFourFive_eq]
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [gaugeTypeAExchangeRefuterPoint,
      gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
      gaugeTypeAExchangeRefuterAxis, atomMatrix, Matrix.vecMulVec_apply]

/-- In particular, the wall gap is positive semidefinite. -/
theorem gaugeTypeAExchangeRefuter_wall_posSemidef :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef := by
  rw [gaugeTypeAExchangeRefuter_wall_gap_eq]
  exact (posSemidef_atomMatrix gaugeTypeAExchangeRefuterAxis).smul (by norm_num)

theorem gaugeTypeAExchangeRefuter_tight_ne :
    gaugeTypeAExchangeRefuterTight ≠ 0 := by
  intro hzero
  have h := congrFun hzero 1
  norm_num [gaugeTypeAExchangeRefuterTight] at h

theorem gaugeTypeAExchangeRefuter_second_ne :
    gaugeTypeAExchangeRefuterSecond ≠ 0 := by
  intro hzero
  have h := congrFun hzero 0
  norm_num [gaugeTypeAExchangeRefuterSecond] at h

/-- The tight vector lies in the wall kernel. -/
theorem gaugeTypeAExchangeRefuter_tight_kernel :
    directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight ({3, 4, 5} : Finset (Fin 6))
          *ᵥ gaugeTypeAExchangeRefuterTight = 0 := by
  rw [gaugeTypeAExchangeRefuter_wall_gap_eq, Matrix.smul_mulVec,
    atomMatrix_mulVec_eq_smul]
  norm_num [gaugeTypeAExchangeRefuterAxis, gaugeTypeAExchangeRefuterTight,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-- The second vector lies in the wall kernel. -/
theorem gaugeTypeAExchangeRefuter_second_kernel :
    directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight ({3, 4, 5} : Finset (Fin 6))
          *ᵥ gaugeTypeAExchangeRefuterSecond = 0 := by
  rw [gaugeTypeAExchangeRefuter_wall_gap_eq, Matrix.smul_mulVec,
    atomMatrix_mulVec_eq_smul]
  norm_num [gaugeTypeAExchangeRefuterAxis, gaugeTypeAExchangeRefuterSecond,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-- Pointer direction `2` is invisible to the second kernel vector. -/
theorem gaugeTypeAExchangeRefuter_pointer_orthogonal :
    kFourDirection 2 ⬝ᵥ gaugeTypeAExchangeRefuterSecond = 0 := by
  norm_num [kFourDirection, gaugeTypeAExchangeRefuterSecond, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-- The two wall kernels are genuinely independent. -/
theorem gaugeTypeAExchangeRefuter_not_collinear :
    ¬ ∃ scale : ℝ,
      gaugeTypeAExchangeRefuterSecond = scale • gaugeTypeAExchangeRefuterTight := by
  rintro ⟨scale, hscale⟩
  have h := congrFun hscale 0
  norm_num [gaugeTypeAExchangeRefuterSecond,
    gaugeTypeAExchangeRefuterTight] at h

/-- The singleton pointer already reads positively at the tight kernel. -/
theorem gaugeTypeAExchangeRefuter_pointer_singleton_pos :
    0 < gaugeTypeAExchangeRefuterTight ⬝ᵥ
      (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight {2}
          *ᵥ gaugeTypeAExchangeRefuterTight) := by
  rw [dotProduct_directionChartGap_mulVec_eq, Finset.sum_singleton,
    Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterPoint,
    gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    gaugeTypeAExchangeRefuterTight, kFourDirection, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-- The singleton collapse upgrades the exact reading to every selection
containing pointer `2`. -/
theorem gaugeTypeAExchangeRefuter_pointer_reads :
    ∀ swap : Finset (Fin 6), 2 ∈ swap →
      0 < gaugeTypeAExchangeRefuterTight ⬝ᵥ
        (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
          gaugeTypeAExchangeRefuterPoint.weight swap
            *ᵥ gaugeTypeAExchangeRefuterTight) := by
  exact ((pointer_swaps_iff_singleton
    (mass := gaugeTypeAExchangeRefuterPoint.mass)
    (weight := gaugeTypeAExchangeRefuterPoint.weight) kFourDirection
    (fun label => (gaugeTypeAExchangeRefuterPoint.mass_pos label).le)
    gaugeTypeAExchangeRefuterPoint.weight_pos 2
    gaugeTypeAExchangeRefuterTight).2
      gaugeTypeAExchangeRefuter_pointer_singleton_pos)

/-- The refuter satisfies the entire original-tree corank-two package, not a
weakened rank-one surrogate. -/
theorem gaugeTypeAExchangeRefuter_corankTwoData :
    KFourTreeGapCorankTwoData gaugeTypeAExchangeRefuterPoint
      ({3, 4, 5} : Finset (Fin 6)) := by
  exact ⟨gaugeTypeAExchangeRefuterTight, gaugeTypeAExchangeRefuterSecond, 2,
    gaugeTypeAExchangeRefuter_tight_ne, by decide,
    gaugeTypeAExchangeRefuter_tight_kernel,
    gaugeTypeAExchangeRefuter_pointer_reads,
    gaugeTypeAExchangeRefuter_second_ne,
    gaugeTypeAExchangeRefuter_second_kernel,
    gaugeTypeAExchangeRefuter_pointer_orthogonal,
    gaugeTypeAExchangeRefuter_not_collinear⟩

/-! ## 3. The stalled positive four-cycle -/

/-- The exact stalled-cycle gap. -/
theorem gaugeTypeAExchangeRefuter_selection_gap_eq :
    directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight gaugeTypeAExchangeRefuterSelection
      = !![2636461 / 5319325, -10296 / 21025, -10296 / 21025;
            -10296 / 21025, 15552 / 21025, 5184 / 21025;
            -10296 / 21025, 5184 / 21025, 15552 / 21025] := by
  simp only [gaugeTypeAExchangeRefuterSelection, directionChartGap,
    gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
      kFourDirection, atomMatrix, Matrix.sub_apply, Matrix.vecMulVec_apply]

/-- The four-cycle is strictly positive definite. -/
theorem gaugeTypeAExchangeRefuter_selection_posDef :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight
      gaugeTypeAExchangeRefuterSelection).PosDef := by
  rw [gaugeTypeAExchangeRefuter_selection_gap_eq]
  exact posDef_of_leadingMinors_fin_three
    (2636461 / 5319325) (-10296 / 21025) (-10296 / 21025)
    (15552 / 21025) (5184 / 21025) (15552 / 21025)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### Its four erasures fail -/

theorem gaugeTypeAExchangeRefuter_erase_zero_det_nonpos :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {1, 4, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem gaugeTypeAExchangeRefuter_erase_one_det_nonpos :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 4, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem gaugeTypeAExchangeRefuter_erase_four_det_nonpos :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 1, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem gaugeTypeAExchangeRefuter_erase_five_det_nonpos :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 1, 4}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- No one-label erasure of the positive four-cycle remains positive definite. -/
theorem gaugeTypeAExchangeRefuter_no_posDef_erase :
    ∀ label ∈ gaugeTypeAExchangeRefuterSelection,
      ¬ (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight
          (gaugeTypeAExchangeRefuterSelection.erase label)).PosDef := by
  intro label hmem hpd
  fin_cases label
  · have hdet := hpd.det_pos
    change 0 < (directionChartGap kFourDirection
      gaugeTypeAExchangeRefuterPoint.mass gaugeTypeAExchangeRefuterPoint.weight
      (gaugeTypeAExchangeRefuterSelection.erase 0)).det at hdet
    have hset : gaugeTypeAExchangeRefuterSelection.erase 0 = {1, 4, 5} := by decide
    rw [hset] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_erase_zero_det_nonpos) hdet
  · have hdet := hpd.det_pos
    change 0 < (directionChartGap kFourDirection
      gaugeTypeAExchangeRefuterPoint.mass gaugeTypeAExchangeRefuterPoint.weight
      (gaugeTypeAExchangeRefuterSelection.erase 1)).det at hdet
    have hset : gaugeTypeAExchangeRefuterSelection.erase 1 = {0, 4, 5} := by decide
    rw [hset] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_erase_one_det_nonpos) hdet
  · simp [gaugeTypeAExchangeRefuterSelection] at hmem
  · simp [gaugeTypeAExchangeRefuterSelection] at hmem
  · have hdet := hpd.det_pos
    change 0 < (directionChartGap kFourDirection
      gaugeTypeAExchangeRefuterPoint.mass gaugeTypeAExchangeRefuterPoint.weight
      (gaugeTypeAExchangeRefuterSelection.erase 4)).det at hdet
    have hset : gaugeTypeAExchangeRefuterSelection.erase 4 = {0, 1, 5} := by decide
    rw [hset] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_erase_four_det_nonpos) hdet
  · have hdet := hpd.det_pos
    change 0 < (directionChartGap kFourDirection
      gaugeTypeAExchangeRefuterPoint.mass gaugeTypeAExchangeRefuterPoint.weight
      (gaugeTypeAExchangeRefuterSelection.erase 5)).det at hdet
    have hset : gaugeTypeAExchangeRefuterSelection.erase 5 = {0, 1, 4} := by decide
    rw [hset] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_erase_five_det_nonpos) hdet

/-- Therefore the four-cycle is stalled. -/
theorem gaugeTypeAExchangeRefuter_selection_stall :
    ∀ label ∈ gaugeTypeAExchangeRefuterSelection,
      1 ≤ chartLadderPivot kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight gaugeTypeAExchangeRefuterSelection
          label := by
  exact (stall_iff_no_posDef_erase kFourDirection
    gaugeTypeAExchangeRefuterPoint.mass gaugeTypeAExchangeRefuterPoint.weight
    gaugeTypeAExchangeRefuterPoint.mass_pos
    gaugeTypeAExchangeRefuterPoint.weight_pos
    gaugeTypeAExchangeRefuterSelection
    gaugeTypeAExchangeRefuter_selection_posDef).2
      gaugeTypeAExchangeRefuter_no_posDef_erase

/-! ## 4. All eight adjacent exchanges fail -/

/-- The eight possible exchanges out of the named four-cycle, enumerated once. -/
theorem gaugeTypeAExchangeRefuter_exchange_enumeration :
    ∀ leaving ∈ gaugeTypeAExchangeRefuterSelection, ∀ entering : Fin 6,
      entering ∉ gaugeTypeAExchangeRefuterSelection →
      insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {1, 2, 4, 5}
        ∨ insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {0, 2, 4, 5}
        ∨ insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {0, 1, 2, 5}
        ∨ insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {0, 1, 2, 4}
        ∨ insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {1, 3, 4, 5}
        ∨ insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {0, 3, 4, 5}
        ∨ insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {0, 1, 3, 5}
        ∨ insert entering (gaugeTypeAExchangeRefuterSelection.erase leaving)
          = {0, 1, 3, 4} := by
  decide

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_1245 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {1, 2, 4, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_0245 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 2, 4, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_0125 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 1, 2, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_0124 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 1, 2, 4}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_1345 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {1, 3, 4, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_0345 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 3, 4, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_0135 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 1, 3, 5}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

private theorem gaugeTypeAExchangeRefuter_gap_det_nonpos_0134 :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 1, 3, 4}).det ≤ 0 := by
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- **EVERY ONE-LABEL EXCHANGE FAILS.** -/
theorem gaugeTypeAExchangeRefuter_no_posDef_exchange :
    ∀ leaving ∈ gaugeTypeAExchangeRefuterSelection, ∀ entering : Fin 6,
      entering ∉ gaugeTypeAExchangeRefuterSelection →
      ¬ (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight
          (insert entering
            (gaugeTypeAExchangeRefuterSelection.erase leaving))).PosDef := by
  intro leaving hleaving entering hentering hpd
  have hdet := hpd.det_pos
  rcases gaugeTypeAExchangeRefuter_exchange_enumeration leaving hleaving entering
      hentering with h | h | h | h | h | h | h | h
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_1245) hdet
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_0245) hdet
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_0125) hdet
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_0124) hdet
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_1345) hdet
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_0345) hdet
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_0135) hdet
  · rw [h] at hdet
    exact (not_lt_of_ge gaugeTypeAExchangeRefuter_gap_det_nonpos_0134) hdet

/-! ## 5. The repair is nonlocal, not impossible -/

/-- A nonlocal spanning tree is positive definite at the same point. -/
theorem gaugeTypeAExchangeRefuter_tree_zeroTwoThree_posDef :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {0, 2, 3}).PosDef := by
  rw [posDef_finThree_iff_cornerBlockDet _
    (directionChartGap_transpose kFourDirection
      gaugeTypeAExchangeRefuterPoint.mass gaugeTypeAExchangeRefuterPoint.weight
      {0, 2, 3})]
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- The symmetric nonlocal spanning tree is positive definite as well. -/
theorem gaugeTypeAExchangeRefuter_tree_oneTwoThree_posDef :
    (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
      gaugeTypeAExchangeRefuterPoint.weight {1, 2, 3}).PosDef := by
  rw [posDef_finThree_iff_cornerBlockDet _
    (directionChartGap_transpose kFourDirection
      gaugeTypeAExchangeRefuterPoint.mass gaugeTypeAExchangeRefuterPoint.weight
      {1, 2, 3})]
  simp only [directionChartGap, gaugeTypeAExchangeRefuterPoint_mass_eq,
    gaugeTypeAExchangeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [gaugeTypeAExchangeRefuterMass, gaugeTypeAExchangeRefuterWeight,
    kFourDirection, atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- The fixture satisfies the chart conclusion.  It refutes only the local
exchange mechanism. -/
theorem gaugeTypeAExchangeRefuter_hasStrictTree :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight tree).PosDef := by
  exact ⟨{0, 2, 3}, by decide,
    gaugeTypeAExchangeRefuter_tree_zeroTwoThree_posDef⟩

/-! ## 6. The exact refutation -/

/-- **THE GAUGE-WALL TYPE-A EXCHANGE IS FALSE.**  All hypotheses of the named
wall statement hold at the exact point above, while every one-label exchange
fails. -/
theorem not_kFourGaugeWallTypeAExchange : ¬ KFourGaugeWallTypeAExchange := by
  intro hexchange
  have hcard : gaugeTypeAExchangeRefuterSelection.card = 4 := by decide
  have hmatching : gaugeTypeAExchangeRefuterSelectionᶜ = ({2, 3} : Finset (Fin 6)) := by
    decide
  obtain ⟨leaving, hleaving, entering, hentering, hpd⟩ :=
    hexchange gaugeTypeAExchangeRefuterPoint gaugeTypeAExchangeRefuterSelection
      hcard (Or.inr (Or.inr hmatching))
      gaugeTypeAExchangeRefuter_corankTwoData
      gaugeTypeAExchangeRefuter_selection_posDef
      gaugeTypeAExchangeRefuter_selection_stall
  exact gaugeTypeAExchangeRefuter_no_posDef_exchange leaving hleaving entering
    hentering hpd

end Gtz
