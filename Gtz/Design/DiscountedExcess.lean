import Gtz.Design.ExcessThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The weight-discounted excess of a refused exchange

The landed price of a refused exchange sums the per-label refusal bounds with
coefficient one.  That sum is not the only one available.  Every label of the
selection may be given its own nonnegative coefficient, and the resulting price
is exact whenever the coefficient family admits a closed cross identity.

One such family is `1 - weight`.  Splitting the exact cross-energy law over the
selection and its complement moves the selected part of the weighted moment to
the left and leaves only the complement behind:

  `sum_{c in C} (1 - w_c) * cross(c,t)^2 = pivot t + sum_{c not in C} w_c * cross(c,t)^2`.

The right side reads in pivot and cross data of the complement alone.  At a
card-four selection of a six-label chart the complement holds two labels, so the
right side is `pivot t * (1 + w_t * pivot t) + w_t' * cross(t',t)^2`.

Pricing that identity against the per-label refusal bounds replaces the excess
`sum (pivot - 1)` by the strictly smaller **discounted excess**
`sum (1 - w) * (pivot - 1)`.  The criterion therefore fires on designs the
landed one misses, and the two are incomparable: neither implies the other.

Everything here is generic in the direction family and in the size.  The only
chart input is positivity of mass and weight, so the three-lines chart inherits
the statements verbatim.
-/

namespace Gtz

open Finset Matrix

/-- **THE DISCOUNTED CROSS-ENERGY IDENTITY.**  Discounting each selected cross
square by one minus its own weight leaves exactly the target pivot together with
the weighted cross squares of the labels outside the selection.

The exact cross-energy law carries a weighted moment over *every* label.  The
selected part of that moment is the same shape as the cross energy it is
subtracted from, so it can be absorbed into the left side.  What remains on the
right involves no selected label at all. -/
theorem selected_discounted_crossEnergy_eq_pivot_add_outside {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (base : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight base).PosDef)
    (target : Fin size) :
    ∑ source ∈ base, (1 - weight source)
        * chartLadderCross direction mass weight base source target ^ 2
      = chartLadderPivot direction mass weight base target
        + ∑ source ∈ baseᶜ, weight source
          * chartLadderCross direction mass weight base source target ^ 2 := by
  have hexact := crossEnergy_eq_pivot_add_weighted_cross_sq direction mass weight
    hmass hweight base hpd target
  have hsplit : ∑ label ∈ base, weight label
        * chartLadderCross direction mass weight base label target ^ 2
      + ∑ label ∈ baseᶜ, weight label
        * chartLadderCross direction mass weight base label target ^ 2
      = ∑ label, weight label
        * chartLadderCross direction mass weight base label target ^ 2 :=
    Finset.sum_add_sum_compl base _
  have hleft : ∑ source ∈ base, (1 - weight source)
        * chartLadderCross direction mass weight base source target ^ 2
      = (∑ source ∈ base,
          chartLadderCross direction mass weight base source target ^ 2)
        - ∑ source ∈ base, weight source
          * chartLadderCross direction mass weight base source target ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun source _ => ?_
    ring
  rw [hleft, hexact, ← hsplit]
  ring

/-- **THE WEIGHT-DISCOUNTED PRICE OF A REFUSED EXCHANGE.**  A selection refusing
every exchange into `entering` pays its pivot and the weighted cross squares of
the labels outside the selection, against the **discounted** excess.

The landed price weights every refusal bound by one.  Here each is weighted by
one minus the weight of its own label, which is nonnegative for a probability
weight.  The discounted excess is strictly smaller than the plain excess, so the
price is harder to meet. -/
theorem pivot_add_outside_le_discountedExcess_of_no_exchange {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hle : ∀ label, weight label ≤ 1)
    (selected : Finset (Fin size)) {entering : Fin size}
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hno : ∀ leaving ∈ selected, ¬ (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef) :
    chartLadderPivot direction mass weight selected entering
        + ∑ source ∈ selectedᶜ, weight source
          * chartLadderCross direction mass weight selected source entering ^ 2
      ≤ (1 + chartLadderPivot direction mass weight selected entering)
        * ∑ leaving ∈ selected, (1 - weight leaving)
          * (chartLadderPivot direction mass weight selected leaving - 1) := by
  have hbound : ∑ leaving ∈ selected, (1 - weight leaving)
        * chartLadderCross direction mass weight selected leaving entering ^ 2
      ≤ ∑ leaving ∈ selected, (1 + chartLadderPivot direction mass weight
            selected entering)
          * ((1 - weight leaving)
            * (chartLadderPivot direction mass weight selected leaving - 1)) := by
    refine Finset.sum_le_sum fun leaving hmem => ?_
    have hfail := hno leaving hmem
    rw [posDef_exchange_iff_cross_sq_gt direction mass weight hmass hweight
      selected hmem hentering hpd] at hfail
    push Not at hfail
    have hcoeff : 0 ≤ 1 - weight leaving := by linarith [hle leaving]
    nlinarith [hfail, hcoeff]
  have hident := selected_discounted_crossEnergy_eq_pivot_add_outside direction
    mass weight hmass hweight selected hpd entering
  rw [Finset.mul_sum]
  linarith

/-- **THE DISCOUNTED EXCHANGE.**  If the entering pivot together with the
weighted cross squares outside the selection beats the discounted excess price,
some exchange into that label is positive definite.

This is the consumable contrapositive.  It is incomparable to the landed
moment-form criterion: its left side is smaller, because it keeps only the
complement's share of the moment, and its right side is smaller too, because the
excess is discounted.  Neither implies the other, so a consumer should try both. -/
theorem exists_posDef_exchange_of_pivot_add_outside_gt {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hle : ∀ label, weight label ≤ 1)
    (selected : Finset (Fin size)) {entering : Fin size}
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hbig : (1 + chartLadderPivot direction mass weight selected entering)
        * ∑ leaving ∈ selected, (1 - weight leaving)
          * (chartLadderPivot direction mass weight selected leaving - 1)
      < chartLadderPivot direction mass weight selected entering
        + ∑ source ∈ selectedᶜ, weight source
          * chartLadderCross direction mass weight selected source entering ^ 2) :
    ∃ leaving ∈ selected, (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef := by
  by_contra hno
  push Not at hno
  have hprice := pivot_add_outside_le_discountedExcess_of_no_exchange direction
    mass weight hmass hweight hle selected hentering hpd hno
  linarith

/-! ## The two-label complement -/

/-- With a two-label complement the outside sum is explicit: the entering
label's own weight times its pivot squared, plus the other outside label's
weight times the squared cross term between the two. -/
theorem outside_crossEnergy_pair {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {entering other : Fin size}
    (hcompl : selectedᶜ = {entering, other}) (hne : entering ≠ other) :
    ∑ source ∈ selectedᶜ, weight source
        * chartLadderCross direction mass weight selected source entering ^ 2
      = weight entering
          * chartLadderPivot direction mass weight selected entering ^ 2
        + weight other
          * chartLadderCross direction mass weight selected other entering ^ 2 := by
  rw [hcompl, Finset.sum_pair hne,
    chartLadderCross_self direction mass weight hmass hweight selected entering]

/-- **THE DISCOUNTED EXCHANGE AT A TWO-LABEL COMPLEMENT.**  Every quantity is a
pivot, a weight, or the single cross term between the two outside labels.

This is the form a card-four selection of a six-label chart consumes.  It reads
entirely inside the ladder: no moment matrix and no inverse gap appear. -/
theorem exists_posDef_exchange_of_pair_outside_gt {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (hle : ∀ label, weight label ≤ 1)
    (selected : Finset (Fin size)) {entering other : Fin size}
    (hcompl : selectedᶜ = {entering, other}) (hne : entering ≠ other)
    (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hbig : (1 + chartLadderPivot direction mass weight selected entering)
        * ∑ leaving ∈ selected, (1 - weight leaving)
          * (chartLadderPivot direction mass weight selected leaving - 1)
      < chartLadderPivot direction mass weight selected entering
        + weight entering
          * chartLadderPivot direction mass weight selected entering ^ 2
        + weight other
          * chartLadderCross direction mass weight selected other entering ^ 2) :
    ∃ leaving ∈ selected, (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef := by
  refine exists_posDef_exchange_of_pivot_add_outside_gt direction mass weight
    hmass hweight hle selected hentering hpd ?_
  rw [outside_crossEnergy_pair direction mass weight hmass hweight selected
    hcompl hne]
  linarith

end Gtz
