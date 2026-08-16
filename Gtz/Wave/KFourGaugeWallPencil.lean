import Gtz.Wave.KFourSignedTreeLaplacian

/-!
# The gauge wall as a two-factor pencil

`Gtz.KFourGaugeStarCorankWallClosure` reduces, by the landed
`Gtz.kFourGaugeStarCorankWallClosure_of_nineTrees`, to a statement about NINE
spanning trees on the three-equation gauge wall.  Each of the nine holds two
triangle labels and one gauge label.  This module decides the shape of those nine
gaps and supplies the engine that makes six of the nine cheap.

## What is new here

**A positive companion to the rank obstruction.**
`Gtz.posDef_sum_three_smul_atomMatrix` proves a positive combination of three
atom matrices positive definite as soon as the three axes are independent.  The
corpus had only the negative side: `Gtz.det_add_smul_atomMatrix_pair` says two
atoms never fill three dimensions, and
`Gtz.not_posDef_directionChartGap_of_blindProbe` kills a selection that misses a
probe.  The statement here mentions no chart, no size and no stratum.

**The exchange law is one indicator identity.**
`Gtz.signedGapWeight_sub_signedGapWeight` says that between ANY two selections the
signed gap weight moves by the conductance times the difference of two
indicators.  A label inside both selections, or outside both, does not move.
Summing it gives `Gtz.directionChartGap_sub_eq_pencil`, which writes the
difference of two chart gaps as one signed conductance pencil.  Both statements
are stratum free.  The landed `Gtz.signedGapWeight_twoGaugeOne` is the single
exchange this generalises.

**The positive factor of a one-gauge-edge tree is positive definite on the wall,
and it does not see which gauge label the tree keeps.**  A tree of the nine is
`{a, b, c}` with `a, b` triangle labels and `c` a gauge label.  Its gap is the
gauge-star gap plus the two kept triangle conductances, minus the two excluded
gauge conductances.  The first two summands depend only on the EXCLUDED triangle
label, and section 5 proves them positive definite at every wall point:
`Gtz.posDef_wallPositivePart_dropZero`, `_dropOne` and `_dropTwo`.  The
independence input is section 4, where all three triangle drops give the SAME
reading `mass 0 * mass 1 + mass 0 * mass 2 + mass 1 * mass 2`.

**The negative factor is monotone.**  `Gtz.posDef_sub_gaugeDrop_of_le` shows that
lowering either excluded conductance preserves strict domination.  With
`Gtz.kFourConductance_eq_heavyMass_div` the conductance is the heavy mass over
the co-weight, and on the wall the heavy mass is pinned by the triangle masses
alone, so the only freedom left in the negative factor is the two excluded gauge
WEIGHTS.

## What this module does NOT do

It does not close `Gtz.KFourGaugeStarCorankWallClosure`.  The residual after the
landed `Gtz.kFourGaugeStarCorankWallClosure_of_nineTrees` is a nine-way
existential, and this module supplies its two factors and their signs, not the
dispatch between them.
-/

namespace Gtz

open scoped BigOperators
open Finset Matrix

/-! ## 1. A positive combination of three independent atoms is positive definite -/

/-- **THE POSITIVE COMPANION OF THE RANK OBSTRUCTION.**  Three atom matrices with
positive coefficients fill three dimensions exactly when their axes do.  The
quadratic form is a positive combination of three squares, so it vanishes only
where all three readings vanish, and independence sends that to the origin. -/
theorem posDef_sum_three_smul_atomMatrix
    {axisOne axisTwo axisThree : Fin 3 → ℝ} {scaleOne scaleTwo scaleThree : ℝ}
    (hone : 0 < scaleOne) (htwo : 0 < scaleTwo) (hthree : 0 < scaleThree)
    (hindependent : ∀ probe : Fin 3 → ℝ,
      axisOne ⬝ᵥ probe = 0 → axisTwo ⬝ᵥ probe = 0 → axisThree ⬝ᵥ probe = 0 → probe = 0) :
    (scaleOne • atomMatrix axisOne + scaleTwo • atomMatrix axisTwo
      + scaleThree • atomMatrix axisThree).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun probe hprobeNe => ?_⟩
  · ext rowIndex colIndex
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  · have hread : ∀ (scale : ℝ) (axis : Fin 3 → ℝ),
        probe ⬝ᵥ ((scale • atomMatrix axis) *ᵥ probe) = scale * (axis ⬝ᵥ probe) ^ 2 := by
      intro scale axis
      rw [smul_atomMatrix_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm]
      ring
    have hexpand : probe ⬝ᵥ ((scaleOne • atomMatrix axisOne + scaleTwo • atomMatrix axisTwo
          + scaleThree • atomMatrix axisThree) *ᵥ probe)
        = scaleOne * (axisOne ⬝ᵥ probe) ^ 2 + scaleTwo * (axisTwo ⬝ᵥ probe) ^ 2
          + scaleThree * (axisThree ⬝ᵥ probe) ^ 2 := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
        hread, hread, hread]
    rw [star_trivial, hexpand]
    have hnonnegOne : 0 ≤ scaleOne * (axisOne ⬝ᵥ probe) ^ 2 :=
      mul_nonneg hone.le (sq_nonneg _)
    have hnonnegTwo : 0 ≤ scaleTwo * (axisTwo ⬝ᵥ probe) ^ 2 :=
      mul_nonneg htwo.le (sq_nonneg _)
    have hnonnegThree : 0 ≤ scaleThree * (axisThree ⬝ᵥ probe) ^ 2 :=
      mul_nonneg hthree.le (sq_nonneg _)
    rcases eq_or_ne (axisOne ⬝ᵥ probe) 0 with hzeroOne | hposOne
    · rcases eq_or_ne (axisTwo ⬝ᵥ probe) 0 with hzeroTwo | hposTwo
      · rcases eq_or_ne (axisThree ⬝ᵥ probe) 0 with hzeroThree | hposThree
        · exact absurd (hindependent probe hzeroOne hzeroTwo hzeroThree) hprobeNe
        · have : 0 < scaleThree * (axisThree ⬝ᵥ probe) ^ 2 :=
            mul_pos hthree (by positivity)
          linarith
      · have : 0 < scaleTwo * (axisTwo ⬝ᵥ probe) ^ 2 := mul_pos htwo (by positivity)
        linarith
    · have : 0 < scaleOne * (axisOne ⬝ᵥ probe) ^ 2 := mul_pos hone (by positivity)
      linarith

/-! ## 2. The conductance is the heavy mass over the co-weight -/

/-- **THE CONDUCTANCE READS THE HEAVY MASS.**  `kappa = m / w` and
`h = m (1 - w) / w`, so `kappa = h / (1 - w)`.  On the gauge wall the heavy mass
of a gauge label is pinned by the three triangle masses, so this identity leaves
the gauge WEIGHT as the only freedom in the conductance. -/
theorem kFourConductance_eq_heavyMass_div (mass weight : Fin 6 → ℝ) (label : Fin 6)
    (hweightNe : weight label ≠ 0) (hcoNe : (1 : ℝ) - weight label ≠ 0) :
    kFourConductance mass weight label
      = kFourHeavyMass mass weight label / (1 - weight label) := by
  rw [kFourConductance, kFourHeavyMass]
  field_simp

/-- The conductance is the heavy mass plus the plain mass.  Division free. -/
theorem kFourConductance_eq_heavyMass_add (mass weight : Fin 6 → ℝ) (label : Fin 6)
    (hweightNe : weight label ≠ 0) :
    kFourConductance mass weight label
      = kFourHeavyMass mass weight label + mass label := by
  rw [kFourConductance, kFourHeavyMass]
  field_simp
  ring

/-! ## 3. The exchange law, as one indicator identity -/

/-- **THE EXCHANGE LAW.**  Between ANY two selections the signed gap weight moves
by the conductance times the difference of the two indicators.  A label inside
both, or outside both, does not move at all.  No chart, no tree and no wall. -/
theorem signedGapWeight_sub_signedGapWeight {size : ℕ} (mass weight : Fin size → ℝ)
    (base other : Finset (Fin size)) (label : Fin size) (hweightNe : weight label ≠ 0) :
    signedGapWeight mass weight other label - signedGapWeight mass weight base label
      = ((if label ∈ other then (1 : ℝ) else 0) - (if label ∈ base then (1 : ℝ) else 0))
        * (mass label / weight label) := by
  by_cases hother : label ∈ other <;> by_cases hbase : label ∈ base <;>
    simp only [signedGapWeight, hother, hbase, ite_true, ite_false, sub_self, zero_mul,
      sub_zero, zero_sub, one_mul, neg_mul] <;> field_simp <;> ring

/-- **THE CHART GAP MOVES BY A SIGNED CONDUCTANCE PENCIL.**  Summing the exchange
law writes the difference of two chart gaps as one signed combination of atom
matrices, with the conductance as the only coefficient.  Stratum free. -/
theorem directionChartGap_sub_eq_pencil {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (base other : Finset (Fin size)) (hweightNe : ∀ label, weight label ≠ 0) :
    directionChartGap direction mass weight other
        - directionChartGap direction mass weight base
      = ∑ label, (((if label ∈ other then (1 : ℝ) else 0)
            - (if label ∈ base then (1 : ℝ) else 0)) * (mass label / weight label))
          • atomMatrix (direction label) := by
  classical
  rw [directionChartGap_eq_sum_signedGapWeight direction mass weight other
      (fun label _ => hweightNe label),
    directionChartGap_eq_sum_signedGapWeight direction mass weight base
      (fun label _ => hweightNe label),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [← sub_smul, signedGapWeight_sub_signedGapWeight mass weight base other label
    (hweightNe label)]

/-! ## 4. The positive factor of a one-gauge-edge tree, on the wall

A tree of the nine holds two triangle labels and one gauge label.  Write it as
`positive factor minus negative factor`.  The positive factor is the gauge-star
gap plus the two triangle conductances, and it does NOT see which gauge label the
tree keeps.  On the wall the gauge-star gap is one outer product, so the positive
factor is a positive combination of three atom matrices.
-/

/-- The wall axis together with the two kept triangle directions is independent,
for the drop of triangle label two.  The determinant reading is
`m0*m1 + m0*m2 + m1*m2`, and the same value appears at all three drops. -/
theorem independent_wallAxis_dropTwo (mass : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (probe : Fin 3 → ℝ)
    (haxis : kFourGaugeWallAxis mass ⬝ᵥ probe = 0)
    (hzero : kFourDirection 0 ⬝ᵥ probe = 0)
    (hone : kFourDirection 1 ⬝ᵥ probe = 0) : probe = 0 := by
  simp only [kFourGaugeWallAxis, kFourDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at haxis hzero hone
  have hsum : 0 < mass 0 * mass 1 + mass 0 * mass 2 + mass 1 * mass 2 := by
    have h0 := hmass 0; have h1 := hmass 1; have h2 := hmass 2; nlinarith
  have hprobeZero : probe 0 = 0 := by
    have hlin : (mass 0 * mass 1 + mass 0 * mass 2 + mass 1 * mass 2) * probe 0 = 0 := by
      linear_combination haxis + (mass 0 * mass 2) * hzero + (mass 1 * mass 2) * hone
    rcases mul_eq_zero.mp hlin with h | h
    · exact absurd h (ne_of_gt hsum)
    · exact h
  have hslotOne : probe 1 = 0 := by linarith [hzero, hprobeZero]
  have hslotTwo : probe 2 = 0 := by linarith [hone, hprobeZero]
  funext slot
  fin_cases slot
  · exact hprobeZero
  · exact hslotOne
  · exact hslotTwo

/-- Independence at the drop of triangle label one, keeping labels zero and two. -/
theorem independent_wallAxis_dropOne (mass : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (probe : Fin 3 → ℝ)
    (haxis : kFourGaugeWallAxis mass ⬝ᵥ probe = 0)
    (hzero : kFourDirection 0 ⬝ᵥ probe = 0)
    (htwo : kFourDirection 2 ⬝ᵥ probe = 0) : probe = 0 := by
  simp only [kFourGaugeWallAxis, kFourDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at haxis hzero htwo
  have hsum : 0 < mass 0 * mass 1 + mass 0 * mass 2 + mass 1 * mass 2 := by
    have h0 := hmass 0; have h1 := hmass 1; have h2 := hmass 2; nlinarith
  have hprobeZero : probe 0 = 0 := by
    have hlin : (mass 0 * mass 1 + mass 0 * mass 2 + mass 1 * mass 2) * probe 0 = 0 := by
      linear_combination haxis + (mass 0 * mass 2 + mass 1 * mass 2) * hzero
        + (mass 1 * mass 2) * htwo
    rcases mul_eq_zero.mp hlin with h | h
    · exact absurd h (ne_of_gt hsum)
    · exact h
  have hslotOne : probe 1 = 0 := by linarith [hzero, hprobeZero]
  have hslotTwo : probe 2 = 0 := by linarith [hzero, htwo, hprobeZero]
  funext slot
  fin_cases slot
  · exact hprobeZero
  · exact hslotOne
  · exact hslotTwo

/-- Independence at the drop of triangle label zero, keeping labels one and two. -/
theorem independent_wallAxis_dropZero (mass : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (probe : Fin 3 → ℝ)
    (haxis : kFourGaugeWallAxis mass ⬝ᵥ probe = 0)
    (hone : kFourDirection 1 ⬝ᵥ probe = 0)
    (htwo : kFourDirection 2 ⬝ᵥ probe = 0) : probe = 0 := by
  simp only [kFourGaugeWallAxis, kFourDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at haxis hone htwo
  have hsum : 0 < mass 0 * mass 1 + mass 0 * mass 2 + mass 1 * mass 2 := by
    have h0 := hmass 0; have h1 := hmass 1; have h2 := hmass 2; nlinarith
  have hprobeZero : probe 2 = 0 := by
    have hlin : (mass 0 * mass 1 + mass 0 * mass 2 + mass 1 * mass 2) * probe 2 = 0 := by
      linear_combination haxis - (mass 0 * mass 1) * hone - (mass 0 * mass 2) * htwo
    rcases mul_eq_zero.mp hlin with h | h
    · exact absurd h (ne_of_gt hsum)
    · exact h
  have hslotZero : probe 0 = 0 := by linarith [hone, hprobeZero]
  have hslotOne : probe 1 = 0 := by linarith [htwo, hprobeZero]
  funext slot
  fin_cases slot
  · exact hslotZero
  · exact hslotOne
  · exact hprobeZero

/-! ## 5. The positive factor is positive definite at every wall point

On the wall the gauge-star gap is the outer product of the wall axis, divided by
the mass product.  Adding the two kept triangle conductances gives a positive
combination of three atom matrices whose axes section 4 proves independent.
-/

/-- **THE POSITIVE FACTOR, DROPPING TRIANGLE LABEL TWO.**  Positive definite at
every point of the wall, with no inequality beyond positive masses and weights. -/
theorem posDef_wallPositivePart_dropTwo (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label) :
    ((mass 0 * mass 1 * mass 2)⁻¹ • atomMatrix (kFourGaugeWallAxis mass)
      + kFourConductance mass weight 0 • atomMatrix (kFourDirection 0)
      + kFourConductance mass weight 1 • atomMatrix (kFourDirection 1)).PosDef := by
  have hscale : 0 < (mass 0 * mass 1 * mass 2)⁻¹ :=
    inv_pos.mpr (mul_pos (mul_pos (hmass 0) (hmass 1)) (hmass 2))
  have hzero : 0 < kFourConductance mass weight 0 :=
    div_pos (hmass 0) (hweight 0)
  have hone : 0 < kFourConductance mass weight 1 :=
    div_pos (hmass 1) (hweight 1)
  exact posDef_sum_three_smul_atomMatrix hscale hzero hone
    (fun probe haxis hdirZero hdirOne =>
      independent_wallAxis_dropTwo mass hmass probe haxis hdirZero hdirOne)

/-- **THE POSITIVE FACTOR, DROPPING TRIANGLE LABEL ONE.** -/
theorem posDef_wallPositivePart_dropOne (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label) :
    ((mass 0 * mass 1 * mass 2)⁻¹ • atomMatrix (kFourGaugeWallAxis mass)
      + kFourConductance mass weight 0 • atomMatrix (kFourDirection 0)
      + kFourConductance mass weight 2 • atomMatrix (kFourDirection 2)).PosDef := by
  have hscale : 0 < (mass 0 * mass 1 * mass 2)⁻¹ :=
    inv_pos.mpr (mul_pos (mul_pos (hmass 0) (hmass 1)) (hmass 2))
  exact posDef_sum_three_smul_atomMatrix hscale (div_pos (hmass 0) (hweight 0))
    (div_pos (hmass 2) (hweight 2))
    (fun probe haxis hdirZero hdirTwo =>
      independent_wallAxis_dropOne mass hmass probe haxis hdirZero hdirTwo)

/-- **THE POSITIVE FACTOR, DROPPING TRIANGLE LABEL ZERO.** -/
theorem posDef_wallPositivePart_dropZero (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label) :
    ((mass 0 * mass 1 * mass 2)⁻¹ • atomMatrix (kFourGaugeWallAxis mass)
      + kFourConductance mass weight 1 • atomMatrix (kFourDirection 1)
      + kFourConductance mass weight 2 • atomMatrix (kFourDirection 2)).PosDef := by
  have hscale : 0 < (mass 0 * mass 1 * mass 2)⁻¹ :=
    inv_pos.mpr (mul_pos (mul_pos (hmass 0) (hmass 1)) (hmass 2))
  exact posDef_sum_three_smul_atomMatrix hscale (div_pos (hmass 1) (hweight 1))
    (div_pos (hmass 2) (hweight 2))
    (fun probe haxis hdirOne hdirTwo =>
      independent_wallAxis_dropZero mass hmass probe haxis hdirOne hdirTwo)

/-- On the wall the gauge-star gap IS the first summand of the positive factor. -/
theorem kFourGaugeStarGap_eq_smul_atomMatrix_of_wall (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label)
    (hwall : KFourGaugeWallEquations mass weight) :
    kFourGaugeStarGap mass weight
      = (mass 0 * mass 1 * mass 2)⁻¹ • atomMatrix (kFourGaugeWallAxis mass) := by
  have hscale : 0 < mass 0 * mass 1 * mass 2 :=
    mul_pos (mul_pos (hmass 0) (hmass 1)) (hmass 2)
  rw [← smul_kFourGaugeStarGap_of_wall mass weight hwall, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hscale), one_smul]

/-! ## 6. The negative factor is monotone

The two excluded gauge labels enter only through their conductances, and each
enters as a nonnegative multiple of a coordinate atom.  So shrinking either one
preserves strict domination.  This is the one direction of the pencil that needs
no case analysis, and it is what turns the gauge WEIGHTS into the only freedom.
-/

/-- **MONOTONICITY OF THE NEGATIVE FACTOR.**  Lowering a subtracted positive
semidefinite matrix preserves positive definiteness. -/
theorem posDef_sub_of_posSemidef_sub (positive negativeLarge negativeSmall :
    Matrix (Fin 3) (Fin 3) ℝ)
    (hposDef : (positive - negativeLarge).PosDef)
    (hbetween : (negativeLarge - negativeSmall).PosSemidef) :
    (positive - negativeSmall).PosDef := by
  have hsplit : positive - negativeSmall
      = (positive - negativeLarge) + (negativeLarge - negativeSmall) := by abel
  rw [hsplit]
  exact hposDef.add_posSemidef hbetween

/-- **SHRINKING AN EXCLUDED CONDUCTANCE PRESERVES DOMINATION.**  The negative
factor of a one-gauge-edge tree is a nonnegative combination of two coordinate
atoms, so a smaller conductance at either excluded gauge label keeps the gap
strictly dominating.  On the wall the heavy mass is pinned by the triangle
masses, so by `Gtz.kFourConductance_eq_heavyMass_div` the only freedom left in
the negative factor is the two excluded gauge WEIGHTS. -/
theorem posDef_sub_gaugeDrop_of_le (positive : Matrix (Fin 3) (Fin 3) ℝ)
    (axisOne axisTwo : Fin 3 → ℝ) (largeOne largeTwo smallOne smallTwo : ℝ)
    (hposDef : (positive - (largeOne • atomMatrix axisOne
      + largeTwo • atomMatrix axisTwo)).PosDef)
    (hsmallOne : smallOne ≤ largeOne) (hsmallTwo : smallTwo ≤ largeTwo) :
    (positive - (smallOne • atomMatrix axisOne + smallTwo • atomMatrix axisTwo)).PosDef := by
  refine posDef_sub_of_posSemidef_sub positive _ _ hposDef ?_
  have hrewrite : (largeOne • atomMatrix axisOne + largeTwo • atomMatrix axisTwo)
        - (smallOne • atomMatrix axisOne + smallTwo • atomMatrix axisTwo)
      = (largeOne - smallOne) • atomMatrix axisOne
        + (largeTwo - smallTwo) • atomMatrix axisTwo := by
    rw [sub_smul, sub_smul]; abel
  rw [hrewrite]
  exact (posSemidef_smul_atomMatrix (sub_nonneg.mpr hsmallOne) axisOne).add
    (posSemidef_smul_atomMatrix (sub_nonneg.mpr hsmallTwo) axisTwo)

end Gtz
