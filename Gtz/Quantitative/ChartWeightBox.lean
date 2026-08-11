/-
# The WEIGHT BOX at a chart stationary datum, and the sandwiched trace

Two small, general, unconditional additions to `Gtz.Quantitative.ChartStationary`,
both consequences of the shipped weight floor by simplex arithmetic alone.

## What was already there

`Gtz.weight_ge_neg_value_of_isChartStationaryData` — **the floor** `-value <= t_c`,
pointwise, at every atom.  `Gtz.value_le_one_sub_weight_of_isChartStationaryData` —
**the Naimark dual** `value <= 1 - t_c`, again pointwise.  Summing the floor against
`sum_c t_c = 1` gives `Gtz.neg_inv_size_le_value_of_isChartStationaryData`, and at
the floor value `Gtz.weight_eq_inv_size_of_value_eq_neg_inv_size` pins every weight
to `1/size`.

## What is added here

* **THE CAP** is `Gtz.weight_le_one_add_pred_size_mul_value_of_isChartStationaryData`,
  `t_c <= 1 + (size - 1) * value`, and it lands in
  `Gtz/Quantitative/ChartStationaryDesignFreeWindow.lean` rather than here: it was
  proved twice independently, the two statements are identical, and only one copy
  survives.  ** IT IS CONSUMED BELOW AND NOT RESTATED. **  The floor holds at the
  OTHER `size - 1` atoms and the weights sum to one, so the remaining atom cannot
  exceed what is left; at a NEGATIVE value that is strictly sharper than both
  shipped upper bounds, than the simplex bound `t_c <= 1` and than the Naimark dual
  `t_c <= 1 - value`, by `-size * value` and `-(size - 1) * value` respectively.
  Everything below is what the cap BUYS, and that is what this file is.
* **THE BOX AND ITS DIAMETER** `weight_sub_weight_le_one_add_size_mul_value_...`:
  every two weights differ by at most `1 + size * value`.  The box
  `[-value, 1 + (size-1) * value]` is nonempty exactly when
  `-1/size <= value`, which is the shipped summed bound — so the cap and the floor
  are the two faces of one statement and neither is a strengthening of the summed
  form.  What the cap adds is that the bound is POINTWISE.
* **THE DEFORMATION OF THE FLOOR RIGIDITY**
  `abs_weight_sub_inv_size_le_of_isChartStationaryData`: every weight lies within
  `(size - 1) * (value + 1/size)` of uniform.  The shipped
  `Gtz.weight_eq_inv_size_of_value_eq_neg_inv_size` is exactly its `value = -1/size`
  endpoint, where the radius vanishes; this is that rigidity made quantitative and
  linear in the distance of the value from its floor.
* **THE STRICT SHIFTED EIGENVALUE BOUND**
  `Gtz.value_add_weight_lt_one_of_isChartStationaryData_of_neg` — the second
  declaration that landed with the cap, and consumed here for the same reason: at a
  negative value
  the shifted quantity `r_c = value + t_c` — the eigenvalue the forced diagonal
  `Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData` tracks — is
  STRICTLY below one, with the explicit margin `-size * value`.  Together with the
  floor this puts `r_c` in `[0, 1)`, closed at the left and open at the right.
  `Gtz.sq_value_add_weight_of_saturatedAtom` then reads `r_c = 0` at a saturated
  atom without needing the separate simplex bound its shipped consumer uses.
* **THE EQUALITY CASE** `weight_eq_cap_iff_forall_other_eq_neg_value_...`: the cap
  is attained at an atom exactly when every OTHER atom sits exactly on the floor.
* **THE SANDWICHED TRACE** `trace_sandwich_projection_multiplier_...`:
  `tr(P Xi P) = value + 1/size`.  Two shipped theorems composed — the trace form of
  the forced diagonal and the congruence `P Xi = P Xi P` — recorded because the
  sandwiched shape is the one a positivity argument consumes and no shipped
  declaration states it.

## Scope, stated so it is not overread

Every theorem here is an implication FROM `Gtz.IsChartStationaryData`.  That bundle
is inhabited — `Gtz.chartTetraProjection_isChartStationaryData` at `(4,3)` and
`Gtz.chartOctaProjection_isChartStationaryData` at `(6,3)` — and at a `(6,3)`
counterexample it is DERIVED, not assumed, by
`Gtz.SixThreeCrux.exists_multiplier_isChartStationaryData` off interiority and
global chart minimality.  So the crux corollaries below are not vacuous for want of
a bundle; they are vacuous only if no crux exists, which is the conjecture.

None of this closes a cell.  The cap is the simplex mirror of the floor and its
summed consequence is the shipped one, so it excludes nothing that was not already
excluded.  What it supplies is a pointwise upper bound on a single weight where the
tree previously had only `t_c <= 1`.
-/
import Mathlib
import Gtz.Quantitative.ChartStationary
import Gtz.Quantitative.ChartStationaryDesignFreeWindow
import Gtz.Quantitative.SixThreeExclusionFrontier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {rank : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
  {value : ℝ} {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The sandwiched trace -/

/-- **`tr(P Xi P) = value + 1/size`.**  The shipped
`Gtz.trace_projection_mul_multiplier_of_isChartStationaryData` states the ONE-SIDED
trace and the shipped
`Gtz.projection_mul_multiplier_eq_sandwich_of_isChartStationaryData` says the
one-sided product already IS the sandwich; this is the two composed, in the shape a
positivity argument on the congruence `P Xi P` consumes. -/
theorem trace_sandwich_projection_multiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace (projection * chartMultiplierAssembly activeSet activeWeight tightDir
        * projection) = value + ((size : ℝ))⁻¹ := by
  rw [← projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata]
  exact trace_projection_mul_multiplier_of_isChartStationaryData hdata

/-! ## The cap -/

/-- The complementary weights are bounded below by `(size - 1) * (-value)`: the
shipped floor holds at each of them and there are `size - 1` of them. -/
theorem pred_size_mul_neg_value_le_sum_erase_weight_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    ((size : ℝ) - 1) * (-value)
      ≤ ∑ otherIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex, weight otherIndex := by
  classical
  have hsizePos : 0 < size := size_pos_of_isChartStationaryData hdata
  have hcardErase : ((Finset.univ : Finset (Fin size)).erase atomIndex).card = size - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ atomIndex), Finset.card_univ, Fintype.card_fin]
  have hcastErase : (((size - 1 : ℕ)) : ℝ) = (size : ℝ) - 1 := by
    rw [Nat.cast_sub hsizePos, Nat.cast_one]
  have htermwise : ∑ _otherIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex, (-value)
      ≤ ∑ otherIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex, weight otherIndex :=
    Finset.sum_le_sum fun otherIndex _ =>
      weight_ge_neg_value_of_isChartStationaryData hdata otherIndex
  rwa [Finset.sum_const, hcardErase, nsmul_eq_mul, hcastErase] at htermwise

/-- The single atom and its complement partition the weight sum. -/
theorem weight_add_sum_erase_weight_eq_one_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    weight atomIndex
        + ∑ otherIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex, weight otherIndex
      = 1 := by
  classical
  rw [Finset.add_sum_erase _ _ (Finset.mem_univ atomIndex)]
  exact hdata.weight_sum_one

/-- **THE BOX.**  Both faces at once: `-value <= t_c <= 1 + (size - 1) * value`. -/
theorem weight_mem_box_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    -value ≤ weight atomIndex ∧ weight atomIndex ≤ 1 + ((size : ℝ) - 1) * value :=
  ⟨weight_ge_neg_value_of_isChartStationaryData hdata atomIndex,
    weight_le_one_add_pred_size_mul_value_of_isChartStationaryData hdata atomIndex⟩

/-- **THE DIAMETER OF THE BOX.**  Any two weights differ by at most
`1 + size * value`.  At the floor value `-1/size` the diameter vanishes, which is
the shipped `Gtz.weight_eq_inv_size_of_value_eq_neg_inv_size`. -/
theorem weight_sub_weight_le_one_add_size_mul_value_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (firstAtom secondAtom : Fin size) :
    weight firstAtom - weight secondAtom ≤ 1 + (size : ℝ) * value := by
  have hcap := weight_le_one_add_pred_size_mul_value_of_isChartStationaryData hdata firstAtom
  have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata secondAtom
  nlinarith [hcap, hfloor]

/-! ## The shifted eigenvalue lies in `[0, 1)` -/

/-- **`r_c = value + t_c <= 1 + size * value`**, with the cap's margin carried
through.  `r_c` is the shifted eigenvalue the forced diagonal
`Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData` tracks:
`(P Xi)_cc = r_c / size`. -/
theorem value_add_weight_le_one_add_size_mul_value_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    value + weight atomIndex ≤ 1 + (size : ℝ) * value := by
  have hcap := weight_le_one_add_pred_size_mul_value_of_isChartStationaryData hdata atomIndex
  nlinarith [hcap]

/-! ## The equality case of the cap -/

/-- **THE CAP IS ATTAINED EXACTLY WHEN EVERY OTHER ATOM SITS ON THE FLOOR.**  The
slack in the cap at one atom is the total slack of the floor at all the others, so
it vanishes exactly when each of those is tight. -/
theorem weight_eq_cap_iff_forall_other_eq_neg_value_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    weight atomIndex = 1 + ((size : ℝ) - 1) * value
      ↔ ∀ otherIndex : Fin size, otherIndex ≠ atomIndex → weight otherIndex = -value := by
  classical
  have hsizePos : 0 < size := size_pos_of_isChartStationaryData hdata
  have hcardErase : ((Finset.univ : Finset (Fin size)).erase atomIndex).card = size - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ atomIndex), Finset.card_univ, Fintype.card_fin]
  have hcastErase : (((size - 1 : ℕ)) : ℝ) = (size : ℝ) - 1 := by
    rw [Nat.cast_sub hsizePos, Nat.cast_one]
  have hpartition := weight_add_sum_erase_weight_eq_one_of_isChartStationaryData hdata atomIndex
  have hslackSum : ∑ otherIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex,
      (weight otherIndex - -value)
      = (1 - weight atomIndex) - ((size : ℝ) - 1) * (-value) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcardErase, nsmul_eq_mul, hcastErase]
    linarith [hpartition]
  constructor
  · intro hattained otherIndex hdistinct
    have hslackZero : ∑ otherIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex,
        (weight otherIndex - -value) = 0 := by
      rw [hslackSum, hattained]; ring
    have hnonneg : ∀ probeIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex,
        0 ≤ weight probeIndex - -value := fun probeIndex _ => by
      linarith [weight_ge_neg_value_of_isChartStationaryData hdata probeIndex]
    have hvanish := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hslackZero otherIndex
      (Finset.mem_erase.mpr ⟨hdistinct, Finset.mem_univ otherIndex⟩)
    linarith [hvanish]
  · intro hallFloor
    have hslackZero : ∑ otherIndex ∈ (Finset.univ : Finset (Fin size)).erase atomIndex,
        (weight otherIndex - -value) = 0 := by
      refine Finset.sum_eq_zero fun probeIndex hmember => ?_
      rw [hallFloor probeIndex (Finset.mem_erase.mp hmember).1]
      ring
    rw [hslackSum] at hslackZero
    linarith [hslackZero]

/-! ## The quantitative deformation of the floor rigidity -/

/-- The one-sided upper deviation from uniform: `t_c - 1/size <= (size - 1) * (value + 1/size)`.
This is the cap rewritten around the uniform point. -/
theorem weight_sub_inv_size_le_pred_size_mul_value_add_inv_size_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    weight atomIndex - ((size : ℝ))⁻¹ ≤ ((size : ℝ) - 1) * (value + ((size : ℝ))⁻¹) := by
  have hsizePos : (0 : ℝ) < (size : ℝ) := size_cast_pos_of_isChartStationaryData hdata
  have hcap := weight_le_one_add_pred_size_mul_value_of_isChartStationaryData hdata atomIndex
  have hinvIdentity : ((size : ℝ) - 1) * ((size : ℝ))⁻¹ = 1 - ((size : ℝ))⁻¹ := by
    field_simp
  nlinarith [hcap, hinvIdentity]

/-- The one-sided lower deviation from uniform: `1/size - t_c <= value + 1/size`.
This is the shipped floor rewritten around the uniform point. -/
theorem inv_size_sub_weight_le_value_add_inv_size_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    ((size : ℝ))⁻¹ - weight atomIndex ≤ value + ((size : ℝ))⁻¹ := by
  linarith [weight_ge_neg_value_of_isChartStationaryData hdata atomIndex]

/-- **THE FLOOR RIGIDITY, MADE QUANTITATIVE.**  Every weight lies within
`(size - 1) * (value + 1/size)` of the uniform weight `1/size`.

The radius is nonnegative by the shipped `-1/size <= value` and VANISHES exactly at
`value = -1/size`, where this becomes the shipped
`Gtz.weight_eq_inv_size_of_value_eq_neg_inv_size`.  So the shipped rigidity is the
endpoint of a bound that is LINEAR in the distance of the value from its floor:
a datum near the floor has near-uniform weights, at rate `size - 1`. -/
theorem abs_weight_sub_inv_size_le_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hsizeTwo : 2 ≤ size) (atomIndex : Fin size) :
    |weight atomIndex - ((size : ℝ))⁻¹| ≤ ((size : ℝ) - 1) * (value + ((size : ℝ))⁻¹) := by
  have hsizeTwoCast : (2 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsizeTwo
  have hradiusNonneg : (0 : ℝ) ≤ value + ((size : ℝ))⁻¹ := by
    linarith [neg_inv_size_le_value_of_isChartStationaryData hdata]
  have hupper :=
    weight_sub_inv_size_le_pred_size_mul_value_add_inv_size_of_isChartStationaryData hdata atomIndex
  have hlower := inv_size_sub_weight_le_value_add_inv_size_of_isChartStationaryData hdata atomIndex
  rw [abs_le]
  constructor
  · nlinarith [hlower, hradiusNonneg, hsizeTwoCast]
  · exact hupper

/-! ## The `(6,3)` counterexample -/

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **THE WEIGHT BOX AT A `(6,3)` CRUX.**  Every weight lies in
`[-value, 1 + 5 * value]`, where `value` is the crux's own chart objective.  The
bundle is DERIVED here, not assumed: `exists_multiplier_isChartStationaryData`
produces it from interiority plus global chart minimality. -/
theorem weight_mem_box (atomIndex : Fin 6) :
    -chartObjective (chartPointOfDesign crux.design)
        ≤ (chartPointOfDesign crux.design).weight atomIndex
      ∧ (chartPointOfDesign crux.design).weight atomIndex
        ≤ 1 + 5 * chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  have hbox := weight_mem_box_of_isChartStationaryData hdata atomIndex
  norm_num at hbox
  exact hbox

/-- **EVERY WEIGHT AT A CRUX IS STRICTLY BELOW ONE, WITH AN EXPLICIT MARGIN.**  The
chart value is strictly negative, so the cap `1 + 5 * value` is itself below one.
Sharper than the simplex bound by `-5 * value`. -/
theorem weight_lt_one_of_cap (atomIndex : Fin 6) :
    (chartPointOfDesign crux.design).weight atomIndex < 1 := by
  have hbox := crux.weight_mem_box atomIndex
  have hnegative := crux.hasNegativeChartValue
  linarith [hbox.2, hnegative]

/-- **THE WEIGHT SPREAD AT A CRUX** is at most `1 + 6 * value`, hence strictly below
one.  With the shipped window `-4/27 <= value` this is a genuine two-sided
localisation of the weight vector: the spread lies in `[1/9, 1)`. -/
theorem weight_sub_weight_le (firstAtom secondAtom : Fin 6) :
    (chartPointOfDesign crux.design).weight firstAtom
        - (chartPointOfDesign crux.design).weight secondAtom
      ≤ 1 + 6 * chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  have hspread :=
    weight_sub_weight_le_one_add_size_mul_value_of_isChartStationaryData hdata firstAtom secondAtom
  norm_num at hspread
  linarith [hspread]

/-- **THE SHIFTED EIGENVALUE AT A CRUX LIES IN `[0, 1)`.**  Left endpoint from the
shipped floor, right endpoint strict from the cap and the crux's negative value. -/
theorem value_add_weight_mem_unit_interval (atomIndex : Fin 6) :
    0 ≤ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex
      ∧ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex < 1 := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  refine ⟨?_, value_add_weight_lt_one_of_isChartStationaryData_of_neg hdata
    crux.hasNegativeChartValue atomIndex⟩
  linarith [weight_ge_neg_value_of_isChartStationaryData hdata atomIndex]

/-- **THE CRUX WEIGHTS ARE WITHIN `5 * (value + 1/6)` OF UNIFORM.**  With the shipped
window `-4/27 <= value < 0` the radius lies in `[5/54, 5/6)`, and it contracts to
zero as the value approaches the shipped floor `-1/6`. -/
theorem abs_weight_sub_inv_six_le (atomIndex : Fin 6) :
    |(chartPointOfDesign crux.design).weight atomIndex - 1 / 6|
      ≤ 5 * (chartObjective (chartPointOfDesign crux.design) + 1 / 6) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  have hlocalised := abs_weight_sub_inv_size_le_of_isChartStationaryData hdata (by norm_num) atomIndex
  norm_num at hlocalised
  exact hlocalised

end SixThreeCrux

end Gtz
