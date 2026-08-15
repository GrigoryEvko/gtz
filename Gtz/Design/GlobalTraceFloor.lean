import Gtz.Design.RigidityBridge

/-!
# The global trace floor of the chart gap

Every landed reading of the chart gap is LOCAL: it fixes one selection and
argues about that selection alone.  This module reads the whole chart at once.

The lever is `DirectionChartPoint.weight_sum_one`.  The weights are a
probability vector over ALL labels, so a weighted average of any family of
numbers is at most the maximum of that family.  Applied to the trace ratios
`m_c |v_c|^2 / w_c` this gives a label whose ratio alone dominates the entire
mass sum, and every selection that holds that label reads a positive gap trace.

The trace is the first of the three invariants that decide domination at a
triple, and it is the only one that is LINEAR in the selection.  That linearity
is exactly what lets the global average act, and it is why the same argument
does not reach the second elementary symmetric function or the determinant.

Nothing here is specific to one chart: the pigeonhole is stated for an
arbitrary index type, and the trace floor for an arbitrary direction family
whose directions are nonzero.
-/

namespace Gtz

open Finset

/-! ## 1. The global pigeonhole

A probability vector cannot push a weighted average above the maximum.  This is
the whole global content, and it is stated once, generically. -/

/-- **THE GLOBAL PIGEONHOLE.**  Weights that sum to at most one send a weighted
sum of nonnegative numbers below the largest of them.  Every statement in this
module is an instance of this one line. -/
theorem exists_weighted_sum_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (weightFn ratio : ι → ℝ) (hweight : ∀ index, 0 ≤ weightFn index)
    (hsum : ∑ index, weightFn index ≤ 1) (hratio : ∀ index, 0 ≤ ratio index) :
    ∃ star, ∑ index, weightFn index * ratio index ≤ ratio star := by
  obtain ⟨star, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) ratio Finset.univ_nonempty
  refine ⟨star, ?_⟩
  have hstep : ∑ index, weightFn index * ratio index
      ≤ ∑ index, weightFn index * ratio star := by
    refine Finset.sum_le_sum fun index _ => ?_
    exact mul_le_mul_of_nonneg_left (hmax index (Finset.mem_univ index)) (hweight index)
  have hfactor : ∑ index, weightFn index * ratio star
      = (∑ index, weightFn index) * ratio star := by
    rw [← Finset.sum_mul]
  have hlast : (∑ index, weightFn index) * ratio star ≤ ratio star := by
    have := mul_le_mul_of_nonneg_right hsum (hratio star)
    simpa using this
  linarith [hstep, hfactor ▸ hlast]

/-! ## 2. The trace of the chart gap -/

/-- The trace of the chart gap is the selected ratio sum minus the total mass
reading.  Trace is linear, so the selection enters as a plain sum. -/
theorem trace_directionChartGap {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    Matrix.trace (directionChartGap direction mass weight selected)
      = (∑ label ∈ selected, mass label / weight label * leverageOf (direction label))
        - ∑ label, mass label * leverageOf (direction label) := by
  unfold directionChartGap
  rw [Matrix.trace_sub, Matrix.trace_sum, Matrix.trace_sum]
  congr 1
  · refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
  · refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]

/-! ## 3. The global trace floor -/

/-- **THE GLOBAL TRACE FLOOR.**  At every chart point there is a label whose
trace ratio alone dominates the entire mass reading, so EVERY selection of two
or more labels that holds it reads a strictly positive gap trace.

The label is chosen by a single global average over all labels at once.  No
selection is examined, and no local move is made. -/
theorem exists_star_trace_pos {size : ℕ} [NeZero size]
    (direction : Fin size → (Fin 3 → ℝ))
    (hlev : ∀ label, 0 < leverageOf (direction label))
    (point : DirectionChartPoint size) :
    ∃ star : Fin size, ∀ selected : Finset (Fin size),
      star ∈ selected → 2 ≤ selected.card →
      0 < Matrix.trace (directionChartGap direction point.mass point.weight selected) := by
  haveI : Nonempty (Fin size) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne size)⟩⟩
  set ratio : Fin size → ℝ :=
    fun label => point.mass label / point.weight label * leverageOf (direction label) with hratio_def
  have hratio_pos : ∀ label, 0 < ratio label := by
    intro label
    exact mul_pos (div_pos (point.mass_pos label) (point.weight_pos label)) (hlev label)
  have hrewrite : ∀ label,
      point.weight label * ratio label = point.mass label * leverageOf (direction label) := by
    intro label
    have hweight : point.weight label ≠ 0 := (point.weight_pos label).ne'
    rw [hratio_def]
    field_simp
  obtain ⟨star, hstar⟩ :=
    exists_weighted_sum_le point.weight ratio
      (fun label => (point.weight_pos label).le)
      (le_of_eq point.weight_sum_one) (fun label => (hratio_pos label).le)
  refine ⟨star, fun selected hmem hcard => ?_⟩
  rw [trace_directionChartGap, sub_pos]
  have htotal : ∑ label, point.mass label * leverageOf (direction label) ≤ ratio star := by
    calc ∑ label, point.mass label * leverageOf (direction label)
        = ∑ label, point.weight label * ratio label :=
          (Finset.sum_congr rfl fun label _ => (hrewrite label).symm)
      _ ≤ ratio star := hstar
  have hsplit : ∑ label ∈ selected, ratio label
      = ratio star + ∑ label ∈ selected.erase star, ratio label :=
    (Finset.add_sum_erase _ _ hmem).symm
  have hrest : 0 < ∑ label ∈ selected.erase star, ratio label := by
    refine Finset.sum_pos (fun label _ => hratio_pos label) ?_
    rw [← Finset.card_pos, Finset.card_erase_of_mem hmem]
    omega
  have : ratio star < ∑ label ∈ selected, ratio label := by rw [hsplit]; linarith
  linarith

/-! ## 4. The K4 instance -/

/-- Every K4 chart direction has positive leverage. -/
theorem leverageOf_kFourDirection_pos (label : Fin 6) :
    0 < leverageOf (kFourDirection label) := by
  fin_cases label <;>
    simp [leverageOf, kFourDirection, Fin.sum_univ_succ]

/-- The global trace floor at the K4 chart: some label sits in a positive-trace
selection, at every chart point and with no antecedent. -/
theorem exists_star_trace_pos_kFour (point : DirectionChartPoint 6) :
    ∃ star : Fin 6, ∀ selected : Finset (Fin 6),
      star ∈ selected → 2 ≤ selected.card →
      0 < Matrix.trace
        (directionChartGap kFourDirection point.mass point.weight selected) :=
  exists_star_trace_pos kFourDirection leverageOf_kFourDirection_pos point

end Gtz
