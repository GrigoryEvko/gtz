import Gtz.Design.CrossEnergyLaw
import Gtz.Design.StallTypeSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The excess threshold of a four-edge stall

The small-excess exchange closes a four-edge stall whose total inside excess is
small against one outside pivot.  A stall always carries an outside pivot at
least one, so the two combine into a threshold on the excess alone.

* `cardFour_excess_eq_weightedPivotSum_sub_one` — the excess of a four-edge
  selection is the weight-weighted pivot sum of ALL labels, minus one.  The
  pivot balance carries the whole identity: the selection contributes its four
  pivots against `1 - weight`, the complement contributes against `weight`, and
  the two sides differ by exactly the rank.
* `exists_posDef_exchange_of_cardFour_stall_excess_le_half` — **the threshold**.
  A four-edge stall of excess at most one half admits a positive definite
  exchange.  The priced outside label pays `pivot / (1 + pivot) ≥ 1 / 2`, which
  is exactly the small-excess hypothesis.
* `exists_posDef_exchange_of_cardFour_stall_weightedPivotSum_le` — the same
  threshold read through the identity, as a bound on the weighted pivot sum.

The residual of the four-edge stall statement is therefore the single region
where the weighted pivot sum exceeds three halves.
-/

namespace Gtz

open Matrix

/-! ## The chart directions are nonzero -/

/-- Every K4 chart direction is a nonzero vector.  The six directions are the
reduced incidence vectors of the complete graph on four vertices, and none of
them is the zero vector. -/
theorem kFourDirection_ne_zero (label : Fin 6) : kFourDirection label ≠ 0 := by
  fin_cases label <;>
    · intro hzero
      simp only [kFourDirection] at hzero
      first
        | simpa using congrFun hzero 0
        | simpa using congrFun hzero 1
        | simpa using congrFun hzero 2

/-! ## The excess as a weighted pivot sum -/

/-- **THE EXCESS IDENTITY.**  At a positive definite four-edge selection the
total inside excess equals the weight-weighted pivot sum over all six labels,
minus one.

The pivot balance reads the selection against `1 - weight` and the complement
against `weight`, around the rank three.  Splitting the inside sum into a bare
pivot sum minus a weighted one, and using that the selection has four labels,
turns the balance into this identity. -/
theorem cardFour_excess_eq_weightedPivotSum_sub_one
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef) :
    ∑ label ∈ selected,
        (chartLadderPivot direction point.mass point.weight selected label - 1)
      = (∑ label, point.weight label
          * chartLadderPivot direction point.mass point.weight selected label)
        - 1 := by
  have hbal := pivot_balance direction point selected hpd
  have hsplit : ∀ label ∈ selected,
      (1 - point.weight label)
          * chartLadderPivot direction point.mass point.weight selected label
        = chartLadderPivot direction point.mass point.weight selected label
          - point.weight label
            * chartLadderPivot direction point.mass point.weight selected
                label := by
    intro label _
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib] at hbal
  have hexcess : ∑ label ∈ selected,
      (chartLadderPivot direction point.mass point.weight selected label - 1)
      = (∑ label ∈ selected,
          chartLadderPivot direction point.mass point.weight selected label)
        - 4 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
    norm_num
  have htotal : ∑ label, point.weight label
        * chartLadderPivot direction point.mass point.weight selected label
      = (∑ label ∈ selected, point.weight label
          * chartLadderPivot direction point.mass point.weight selected label)
        + ∑ label ∈ selectedᶜ, point.weight label
            * chartLadderPivot direction point.mass point.weight selected
                label :=
    (Finset.sum_add_sum_compl selected _).symm
  rw [hexcess, htotal]
  linarith

/-! ## The threshold -/

/-- **THE EXCESS THRESHOLD.**  A four-edge stall whose total inside excess is at
most one half admits a positive definite exchange.

A stall carries an outside label of pivot at least one, and such a label prices
a refusal at `pivot / (1 + pivot)`, which is at least one half.  An excess at
most one half therefore cannot pay the refusal, and the small-excess exchange
fires. -/
theorem exists_posDef_exchange_of_cardFour_stall_excess_le_half
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected
        label)
    (hexcess : ∑ label ∈ selected,
        (chartLadderPivot kFourDirection point.mass point.weight selected label
          - 1) ≤ 1 / 2) :
    ∃ entering ∈ selectedᶜ, ∃ leaving ∈ selected,
      (directionChartGap kFourDirection point.mass point.weight
        (insert entering (selected.erase leaving))).PosDef := by
  obtain ⟨entering, hmem, hpivot⟩ :=
    exists_outside_pivot_ge_one_of_cardFour_stall kFourDirection point selected
      hcard hpd hstall
  refine ⟨entering, hmem, ?_⟩
  refine exists_posDef_exchange_of_excess_le kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos selected
    (Finset.mem_compl.mp hmem) hpd (posDef_massMoment_kFourDirection point)
    (kFourDirection_ne_zero entering) ?_
  nlinarith [hexcess, hpivot]

/-- **THE THRESHOLD IN WEIGHTED PIVOT FORM.**  A four-edge stall whose weighted
pivot sum over all six labels is at most three halves admits a positive definite
exchange.  The excess identity turns the threshold into this bound. -/
theorem exists_posDef_exchange_of_cardFour_stall_weightedPivotSum_le
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected
        label)
    (hsum : ∑ label, point.weight label
        * chartLadderPivot kFourDirection point.mass point.weight selected label
      ≤ 3 / 2) :
    ∃ entering ∈ selectedᶜ, ∃ leaving ∈ selected,
      (directionChartGap kFourDirection point.mass point.weight
        (insert entering (selected.erase leaving))).PosDef := by
  refine exists_posDef_exchange_of_cardFour_stall_excess_le_half point selected
    hcard hpd hstall ?_
  rw [cardFour_excess_eq_weightedPivotSum_sub_one kFourDirection point selected
    hcard hpd]
  linarith

/-! ## The exact cross-energy law -/

/-- **THE EXACT CROSS-ENERGY LAW.**  The squared inverse cross terms from one
label into a selection equal that label's pivot PLUS the mass moment form at the
inverse image of its scaled atom.

The landed cross-energy law discards the moment term as merely positive.  The
identity keeps it, and needs neither positive definiteness of the moment matrix
nor a nonzero direction: it is the gap decomposition read at one vector. -/
theorem crossEnergy_eq_pivot_add_moment {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (target : Fin size) :
    ∑ source ∈ base,
        chartLadderCross direction mass weight base source target ^ 2
      = chartLadderPivot direction mass weight base target
        + ((directionChartGap direction mass weight base)⁻¹
              *ᵥ chartLadderVector direction mass weight target) ⬝ᵥ
            ((∑ label, mass label • atomMatrix (direction label))
              *ᵥ ((directionChartGap direction mass weight base)⁻¹
                *ᵥ chartLadderVector direction mass weight target)) := by
  set gapMat := directionChartGap direction mass weight base with hgapMat
  set scaled := chartLadderVector direction mass weight target with hscaled
  set dual := gapMat⁻¹ *ᵥ scaled with hdual
  have hunit : IsUnit gapMat.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hgapDual : gapMat *ᵥ dual = scaled := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hpivot : dual ⬝ᵥ (gapMat *ᵥ dual)
      = chartLadderPivot direction mass weight base target := by
    rw [hgapDual, hdual, dotProduct_comm]
    exact chartLadderVector_inv_quad direction mass weight hmass hweight base
      target
  have hcross : dual ⬝ᵥ ((∑ label ∈ base,
        atomMatrix (chartLadderVector direction mass weight label)) *ᵥ dual)
      = ∑ source ∈ base,
        chartLadderCross direction mass weight base source target ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [dotProduct_atomMatrix_mulVec]
    rw [chartLadderCross, ← hdual]
  have hsplit : dual ⬝ᵥ (gapMat *ᵥ dual)
      = dual ⬝ᵥ ((∑ label ∈ base,
          atomMatrix (chartLadderVector direction mass weight label)) *ᵥ dual)
        - dual ⬝ᵥ ((∑ label, mass label • atomMatrix (direction label))
          *ᵥ dual) := by
    rw [hgapMat, directionChartGap_eq_ladderSum_sub_moment direction mass weight
      hmass hweight base, Matrix.sub_mulVec, dotProduct_sub]
  rw [hpivot, hcross] at hsplit
  linarith

/-- **THE SHARPENED PRICE OF A REFUSED EXCHANGE.**  A selection refusing every
exchange into `entering` pays with its pivot AND the moment form together,
against the excess.

The landed price drops the moment term.  Keeping it is what separates a criterion
that fires on a few percent of four-edge stalls from one that fires on almost all
of them, because the moment form is the dominant term. -/
theorem pivot_add_moment_le_excess_of_no_exchange {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {entering : Fin size}
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hno : ∀ leaving ∈ selected, ¬ (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef) :
    chartLadderPivot direction mass weight selected entering
        + ((directionChartGap direction mass weight selected)⁻¹
              *ᵥ chartLadderVector direction mass weight entering) ⬝ᵥ
            ((∑ label, mass label • atomMatrix (direction label))
              *ᵥ ((directionChartGap direction mass weight selected)⁻¹
                *ᵥ chartLadderVector direction mass weight entering))
      ≤ (1 + chartLadderPivot direction mass weight selected entering)
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
  have hexact := crossEnergy_eq_pivot_add_moment direction mass weight hmass
    hweight selected hpd entering
  rw [Finset.mul_sum]
  linarith

/-- **THE SHARPENED EXCHANGE.**  If the entering pivot together with its moment
form beats the excess price, some exchange into that label is positive definite.

This is the consumable contrapositive, and it is the form that fires on almost
every four-edge stall, where the pivot-only form fires on a few percent. -/
theorem exists_posDef_exchange_of_pivot_add_moment_gt {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {entering : Fin size}
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hbig : (1 + chartLadderPivot direction mass weight selected entering)
        * ∑ leaving ∈ selected,
          (chartLadderPivot direction mass weight selected leaving - 1)
      < chartLadderPivot direction mass weight selected entering
        + ((directionChartGap direction mass weight selected)⁻¹
              *ᵥ chartLadderVector direction mass weight entering) ⬝ᵥ
            ((∑ label, mass label • atomMatrix (direction label))
              *ᵥ ((directionChartGap direction mass weight selected)⁻¹
                *ᵥ chartLadderVector direction mass weight entering))) :
    ∃ leaving ∈ selected, (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef := by
  by_contra hno
  push Not at hno
  have hprice := pivot_add_moment_le_excess_of_no_exchange direction mass weight
    hmass hweight selected hentering hpd hno
  linarith

/-! ## The residual -/

/-- **THE RESIDUAL OF THE FOUR-EDGE STALL STATEMENT.**  A four-edge stall that
refuses every exchange has weighted pivot sum strictly above three halves.

This is the contrapositive of the threshold, and it names the single region the
four-edge stall statement still has to reach. -/
theorem cardFour_stall_weightedPivotSum_gt_of_no_exchange
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight selected
        label)
    (hno : ∀ entering ∈ selectedᶜ, ∀ leaving ∈ selected,
      ¬ (directionChartGap kFourDirection point.mass point.weight
        (insert entering (selected.erase leaving))).PosDef) :
    3 / 2 < ∑ label, point.weight label
      * chartLadderPivot kFourDirection point.mass point.weight selected
        label := by
  by_contra hle
  push Not at hle
  obtain ⟨entering, hmemEntering, leaving, hmemLeaving, hposDef⟩ :=
    exists_posDef_exchange_of_cardFour_stall_weightedPivotSum_le point selected
      hcard hpd hstall hle
  exact hno entering hmemEntering leaving hmemLeaving hposDef

end Gtz
