import Gtz.Design.ExchangeCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The cross-energy law and the master exchange formula

The exchange criterion reads a swap as a pivot at the five-edge base, and the
chart cross update reads that pivot as a drop by a squared inverse cross term.
This module puts the two together and then supplies the geometric ingredient
the pivot algebra cannot reach.

* `posDef_exchange_iff_cross_sq_gt` — **the master exchange formula**.  The
  exchange `(C \ s) ∪ {t}` is positive definite exactly when
  `cross ^ 2 > (pivot C s - 1) * (1 + pivot C t)`.  Everything about a swap is
  now one inequality between an inverse cross term and two pivots.
* `crossEnergy_gt_pivot` — **the cross-energy law**.  For every label the
  squared inverse cross terms into the selection exceed that label's own pivot.
  The pivot balance is an identity and cannot bound an inside pivot from above;
  this is the geometry, and it enters through the mass moment matrix, which is
  positive definite because the directions span.
* `excess_gt_of_no_exchange` — the two combined.  A selection refusing every
  exchange into `t` pays with total inside excess above `pivot t / (1 + pivot t)`.
* `kFourCircuit_*`, `exists_cross_ne_zero_of_card_four` — the K4 circuits and
  the non-degeneracy they carry: at any positive definite four-edge selection
  no outside label is inverse-orthogonal to all four, because four K4 edges
  always span.
-/

namespace Gtz

open Matrix

/-! ## The gap in scaled coordinates -/

/-- The chart gap written with the scaled ladder atoms of its own selection. -/
theorem directionChartGap_eq_ladderSum_sub_moment {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size)) :
    directionChartGap direction mass weight base
      = (∑ label ∈ base, atomMatrix (chartLadderVector direction mass weight label))
        - ∑ label, mass label • atomMatrix (direction label) := by
  rw [directionChartGap]
  congr 1
  exact Finset.sum_congr rfl fun label _ =>
    (atomMatrix_chartLadderVector direction mass weight hmass hweight label).symm

/-! ## The master exchange formula -/

/-- **THE MASTER EXCHANGE FORMULA.**  A swap is decided by one inequality
between the inverse cross term of its two labels and their two pivots, all read
at the original selection.

The exchange criterion turns the swap into a pivot at the base holding both
labels, and the cross update evaluates that pivot exactly. -/
theorem posDef_exchange_iff_cross_sq_gt {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (directionChartGap direction mass weight
        (insert entering (selected.erase leaving))).PosDef
      ↔ (chartLadderPivot direction mass weight selected leaving - 1)
          * (1 + chartLadderPivot direction mass weight selected entering)
        < chartLadderCross direction mass weight selected leaving entering ^ 2 := by
  have hupdate := chartLadderPivot_insert_cross_update direction mass weight
    hmass hweight selected hentering hpd leaving
  have hnn := chartLadderPivot_nonneg_of_posDef direction mass weight hmass
    hweight selected hpd entering
  rw [posDef_exchange_iff_pivot_insert_lt_one direction mass weight hmass
    hweight selected hleaving hentering hpd]
  constructor
  · intro hlt
    nlinarith
  · intro hgt
    nlinarith

/-! ## The cross-energy law -/

/-- **THE CROSS-ENERGY LAW.**  The squared inverse cross terms from one label
into a selection exceed that label's own pivot at the same selection.

The proof reads the gap at the inverse image of the label's scaled atom.  There
the selection's own atoms contribute exactly the cross squares, and what is left
over is the mass moment form, which is strictly positive because the directions
span and the moment matrix is therefore positive definite.  The pivot balance is
an identity between pivots and cannot produce this: the strict gain is
geometric. -/
theorem crossEnergy_gt_pivot {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (hmoment : (∑ label, mass label • atomMatrix (direction label)).PosDef)
    {target : Fin size} (hne : direction target ≠ 0) :
    chartLadderPivot direction mass weight base target
      < ∑ source ∈ base,
          chartLadderCross direction mass weight base source target ^ 2 := by
  set gapMat := directionChartGap direction mass weight base with hgapMat
  set scaled := chartLadderVector direction mass weight target with hscaled
  set dual := gapMat⁻¹ *ᵥ scaled with hdual
  have hunit : IsUnit gapMat.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  -- the scaled atom is nonzero, hence so is its inverse image
  have hscaledNe : scaled ≠ 0 := by
    rw [hscaled, chartLadderVector]
    intro hzero
    have hroot : Real.sqrt (mass target / weight target) ≠ 0 := by
      have : 0 < mass target / weight target :=
        div_pos (hmass target) (hweight target)
      positivity
    exact hne (by
      have := smul_eq_zero.mp hzero
      tauto)
  have hgapDual : gapMat *ᵥ dual = scaled := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hdualNe : dual ≠ 0 := by
    intro hzero
    apply hscaledNe
    rw [← hgapDual, hzero, Matrix.mulVec_zero]
  -- the gap form at the inverse image is the pivot
  have hpivot : dual ⬝ᵥ (gapMat *ᵥ dual)
      = chartLadderPivot direction mass weight base target := by
    rw [hgapDual, hdual, dotProduct_comm]
    exact chartLadderVector_inv_quad direction mass weight hmass hweight base
      target
  -- the selection's own atoms contribute exactly the cross squares
  have hcross : dual ⬝ᵥ ((∑ label ∈ base,
        atomMatrix (chartLadderVector direction mass weight label)) *ᵥ dual)
      = ∑ source ∈ base,
        chartLadderCross direction mass weight base source target ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [dotProduct_atomMatrix_mulVec]
    rw [chartLadderCross, ← hdual]
  -- the leftover is the mass moment form, strictly positive
  have hmomentPos : 0 < dual ⬝ᵥ ((∑ label, mass label
      • atomMatrix (direction label)) *ᵥ dual) :=
    (Matrix.posDef_iff_dotProduct_mulVec.mp hmoment).2 hdualNe
  have hsplit : dual ⬝ᵥ (gapMat *ᵥ dual)
      = dual ⬝ᵥ ((∑ label ∈ base,
          atomMatrix (chartLadderVector direction mass weight label)) *ᵥ dual)
        - dual ⬝ᵥ ((∑ label, mass label • atomMatrix (direction label))
          *ᵥ dual) := by
    rw [hgapMat, directionChartGap_eq_ladderSum_sub_moment direction mass weight
      hmass hweight base, Matrix.sub_mulVec, dotProduct_sub]
  rw [hpivot, hcross] at hsplit
  linarith

/-! ## The two laws combined -/

/-- **THE EXCESS PRICE OF A REFUSED EXCHANGE.**  If no exchange into `entering`
is positive definite, the selection's total pivot excess exceeds
`pivot entering / (1 + pivot entering)`.

Each refusal caps one cross square by the pivot excess of its leaving label; the
cross-energy law bounds the same sum from below by the entering pivot. -/
theorem excess_gt_of_no_exchange {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {entering : Fin size}
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hmoment : (∑ label, mass label • atomMatrix (direction label)).PosDef)
    (hne : direction entering ≠ 0)
    (hno : ∀ leaving ∈ selected, ¬ (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef) :
    chartLadderPivot direction mass weight selected entering
      < (1 + chartLadderPivot direction mass weight selected entering)
        * ∑ leaving ∈ selected,
          (chartLadderPivot direction mass weight selected leaving - 1) := by
  have hpos : 0 ≤ chartLadderPivot direction mass weight selected entering :=
    chartLadderPivot_nonneg_of_posDef direction mass weight hmass hweight
      selected hpd entering
  have hbound : ∑ leaving ∈ selected,
        chartLadderCross direction mass weight selected leaving entering ^ 2
      ≤ ∑ leaving ∈ selected,
        (1 + chartLadderPivot direction mass weight selected entering)
          * (chartLadderPivot direction mass weight selected leaving - 1) := by
    refine Finset.sum_le_sum fun leaving hmem => ?_
    have hfail := hno leaving hmem
    rw [posDef_exchange_iff_cross_sq_gt direction mass weight hmass hweight
      selected hmem hentering hpd] at hfail
    push Not at hfail
    nlinarith
  have hlaw := crossEnergy_gt_pivot direction mass weight hmass hweight selected
    hpd hmoment hne
  rw [Finset.mul_sum]
  linarith

/-! ## The K4 circuits and their non-degeneracy -/

/-- The triangle circuit at the grounded vertex: the bc edge is the difference
of the two edges to the ground. -/
theorem kFourCircuit_two : kFourDirection 2 = kFourDirection 4 - kFourDirection 5 := by
  funext index
  fin_cases index <;> simp [kFourDirection]

/-- The triangle circuit on the ground-adjacent edges: the ab edge is the
difference of the ad and bd edges. -/
theorem kFourCircuit_zero : kFourDirection 0 = kFourDirection 3 - kFourDirection 4 := by
  funext index
  fin_cases index <;> simp [kFourDirection]

/-- The remaining ground circuit: the ac edge is the difference of the ad and cd
edges. -/
theorem kFourCircuit_one : kFourDirection 1 = kFourDirection 3 - kFourDirection 5 := by
  funext index
  fin_cases index <;> simp [kFourDirection]

/-- The free triangle circuit: the three edges of the triangle on the
non-grounded vertices close. -/
theorem kFourCircuit_triangle :
    kFourDirection 0 - kFourDirection 1 + kFourDirection 2 = 0 := by
  funext index
  fin_cases index <;> simp [kFourDirection]

/-- **THE CROSS NON-DEGENERACY.**  At any positive definite selection of the K4
chart, no label is inverse-orthogonal to every selected label.

The cardinality plays no role: the cross-energy law already carries the spanning
through the mass moment matrix, whose positive definiteness is exactly the
statement that the six chart directions span. -/
theorem exists_cross_ne_zero (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (target : Fin 6)
    (hne : kFourDirection target ≠ 0) :
    ∃ source ∈ selected,
      chartLadderCross kFourDirection point.mass point.weight selected source
        target ≠ 0 := by
  by_contra hall
  push Not at hall
  have hlaw := crossEnergy_gt_pivot kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos selected hpd
    (posDef_massMoment_kFourDirection point) hne
  have hzero : ∑ source ∈ selected,
      chartLadderCross kFourDirection point.mass point.weight selected source
        target ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun source hmem => ?_
    rw [hall source hmem]
    norm_num
  have hnn := chartLadderPivot_nonneg_of_posDef kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos selected hpd target
  rw [hzero] at hlaw
  linarith

end Gtz
