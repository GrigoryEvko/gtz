/-
# The outside atom that carries the probe, and the four-set it produces

`Gtz.fourSet_posDef_of_reading_ne_zero` turns a corank-one weak dominator into a
strictly dominating four-set as soon as SOME label reads its null probe, and
`Gtz.exists_reading_ne_zero_of_unit_probe` supplies a label.  That label may sit
INSIDE the dominator, where inserting it changes nothing.  This module supplies
an OUTSIDE one, and it supplies a quantitative reading rather than a nonzero
one.

## Two totals, one pointwise conclusion

The landed `Gtz.nullProbe_inside_total` says the dominator's own squared
readings total the probe's square, UNWEIGHTED:

  `Σ_{c ∈ C} (a_c ⬝ᵥ w)² = w ⬝ᵥ w = 1` .

Every term is a square, so every INSIDE reading is at most one.  Parseval says
the same total over the whole design is one when WEIGHTED.  Subtracting, the
outside atoms carry

  `Σ_{d ∉ C} t_d · ((a_d ⬝ᵥ w)² - 1) ≥ 0` ,

and the weights are strictly positive, so some outside atom has

  **`Gtz.exists_outside_reading_sq_one_le`: `1 ≤ (a_d ⬝ᵥ w)²` for some `d ∉ C`.**

The inside atoms are capped at one and the outside atoms must clear it: the
complement of a weak dominator is never blind to its null direction, and it is
not merely visible there — it is heavier than the dominator's own members.

## What it produces

Chained against the producer, this is unconditional:

  **`Gtz.exists_outside_fourSet_posDef`: every corank-one weak dominator of a
  design on more than three labels extends, by an atom OUTSIDE it, to a
  four-set whose gap is positive definite.**

No selector, no chart, no probe constant.  A corner is exactly the excluded
case, and `Gtz.fourSet_not_posDef_of_secondInvariant_eq_zero` shows it excludes
itself.
-/
import Gtz.Wave.FourSetProducer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. Every inside reading is capped at one -/

/-- **THE INSIDE READINGS ARE CAPPED.**  The dominator's squared readings total
the probe's square, so no single one of them passes it. -/
theorem inside_reading_sq_le_of_unit_null (D : WeightedDesign m 3)
    {T : Finset (Fin m)} {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D T - 1) *ᵥ w) = 0) (hunit : w ⬝ᵥ w = 1)
    {c : Fin m} (hc : c ∈ T) :
    (D.atom c ⬝ᵥ w) ^ 2 ≤ 1 := by
  have htotal := nullProbe_inside_total D T hnull
  rw [hunit] at htotal
  have hsingle := Finset.single_le_sum
    (f := fun e => (D.atom e ⬝ᵥ w) ^ 2) (fun e _ => sq_nonneg _) hc
  linarith

/-! ## 2. The outside atoms clear the cap -/

/-- **THE OUTSIDE READING FLOOR, POINTWISE.**  Some atom outside a weak
dominator reads its null probe at least as strongly as the probe's own length.
The inside readings are capped at one by their own total, Parseval fixes the
weighted total over the whole design at one, and the weights are positive. -/
theorem exists_outside_reading_sq_one_le (D : WeightedDesign m 3)
    {T : Finset (Fin m)} {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D T - 1) *ᵥ w) = 0) (hunit : w ⬝ᵥ w = 1)
    (hne : (Tᶜ : Finset (Fin m)).Nonempty) :
    ∃ d ∈ (Tᶜ : Finset (Fin m)), 1 ≤ (D.atom d ⬝ᵥ w) ^ 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- Outside, the weighted readings fall strictly below the weights.
  have houtside : ∑ d ∈ (Tᶜ : Finset (Fin m)), D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      < ∑ d ∈ (Tᶜ : Finset (Fin m)), D.weight d := by
    refine Finset.sum_lt_sum_of_nonempty hne fun d hd => ?_
    calc D.weight d * (D.atom d ⬝ᵥ w) ^ 2
        < D.weight d * 1 := mul_lt_mul_of_pos_left (hcon d hd) (D.weight_pos d)
      _ = D.weight d := mul_one _
  -- Inside, every squared reading is capped at one by the dominator's own total.
  have hinside : ∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ w) ^ 2 ≤ ∑ c ∈ T, D.weight c := by
    refine Finset.sum_le_sum fun c hc => ?_
    calc D.weight c * (D.atom c ⬝ᵥ w) ^ 2
        ≤ D.weight c * 1 :=
          mul_le_mul_of_nonneg_left
            (inside_reading_sq_le_of_unit_null D hnull hunit hc) (D.weight_pos c).le
      _ = D.weight c := mul_one _
  -- Parseval and the weight total split the same way.
  have hp : (∑ c ∈ T, D.weight c * (D.atom c ⬝ᵥ w) ^ 2)
      + ∑ d ∈ (Tᶜ : Finset (Fin m)), D.weight d * (D.atom d ⬝ᵥ w) ^ 2 = 1 := by
    rw [Finset.sum_add_sum_compl, parseval_probe_form D w, hunit]
  have hw : (∑ c ∈ T, D.weight c) + ∑ d ∈ (Tᶜ : Finset (Fin m)), D.weight d = 1 := by
    rw [Finset.sum_add_sum_compl, D.weight_sum_one]
  linarith

/-! ## 3. The unconditional producer -/

/-- **EVERY CORANK-ONE WEAK DOMINATOR EXTENDS OUTWARD.**  An atom outside the
dominator reads the probe at least one, hence nonzero, hence the four-set it
builds has a positive definite gap.  No selector and no chart. -/
theorem exists_outside_fourSet_posDef (D : WeightedDesign m 3)
    {T : Finset (Fin m)} (hdom : Dominates D T) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D T - 1) *ᵥ w = 0) (hunit : w ⬝ᵥ w = 1)
    (he : secondInvariantOfThree (subsetSum D T - 1) ≠ 0)
    (hne : (Tᶜ : Finset (Fin m)).Nonempty) :
    ∃ d : Fin m, d ∉ T ∧ (subsetSum D (insert d T) - 1).PosDef := by
  classical
  have hform : w ⬝ᵥ ((subsetSum D T - 1) *ᵥ w) = 0 := by
    rw [hnull, dotProduct_zero]
  obtain ⟨d, hd, hread⟩ := exists_outside_reading_sq_one_le D hform hunit hne
  have hdT : d ∉ T := Finset.mem_compl.mp hd
  refine ⟨d, hdT, fourSet_posDef_of_reading_ne_zero D hdom hnull hunit he hdT ?_⟩
  intro hzero
  rw [hzero] at hread
  norm_num at hread

/-- **THE READING THAT BINDS THE TIE PAYMENT.**  The outside atom the floor
supplies reads the probe at least one, so the payment
`Gtz.tie_fourSet_reading_bound` is not vacuous at it: the left side is at least
the second invariant itself. -/
theorem secondInvariant_le_reading_term {form : Matrix (Fin 3) (Fin 3) ℝ}
    (he : 0 ≤ secondInvariantOfThree form) {w v : Fin 3 → ℝ}
    (hread : 1 ≤ (v ⬝ᵥ w) ^ 2) :
    secondInvariantOfThree form
      ≤ secondInvariantOfThree form * (v ⬝ᵥ w) ^ 2 := by
  nlinarith [he, hread]

end Gtz
