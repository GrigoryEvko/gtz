/-
# Charge-budget pivot selection

The directional Parseval identity `parseval_weighted_sum_sq` (`Gtz.RayleighCertificate`,
`∑ t_c ⟨g_c,u⟩² = ⟨u,u⟩`) says the `t`-weighted average of the squared atom-charges along
any direction `u` equals `|u|²`. Two selection consequences:

  * `exists_charge_ge` — a directional pigeonhole: some atom carries squared charge
    `≥ |u|²` along `u` (the directional analogue of the trace bound
    `exists_leverage_ge_rank`);
  * `exists_nonneg_margin_of_weighted_average` — the averaging-selection principle: any
    per-atom margin whose `t`-weighted (Parseval) average is `≥ 0` is `≥ 0` on some atom.
    This is the selection step for a pivot chosen by averaging over Parseval; supplying the
    average bound itself is separate.
-/
import Gtz.RayleighCertificate

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **Directional pigeonhole from the charge budget.** Since the `t`-weighted average of
the squared charges equals `⟨u,u⟩` and the weights sum to `1`, some atom carries squared
charge at least `⟨u,u⟩` along `u` (for a unit `u`: at least `1`). Directional analogue of
`exists_leverage_ge_rank` (take `u` over an orthonormal basis and sum to recover the trace
bound). Rides the existing `parseval_weighted_sum_sq`. -/
theorem exists_charge_ge (D : WeightedDesign m k) (u : Fin k → ℝ) :
    ∃ c, u ⬝ᵥ u ≤ (D.atom c ⬝ᵥ u) ^ 2 := by
  by_contra hall
  push_neg at hall
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra hempty
    have hzero := D.weight_sum_one
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hzero
    exact one_ne_zero hzero.symm
  have hstrict : ∑ c, D.weight c * (D.atom c ⬝ᵥ u) ^ 2
      < ∑ c, D.weight c * (u ⬝ᵥ u) := by
    refine Finset.sum_lt_sum_of_nonempty hnonempty fun c _ => ?_
    exact mul_lt_mul_of_pos_left (hall c) (D.weight_pos c)
  rw [parseval_weighted_sum_sq, ← Finset.sum_mul, D.weight_sum_one, one_mul] at hstrict
  exact lt_irrefl _ hstrict

/-- **The Parseval averaging-selection principle.** For any per-atom margin, if its
`t`-weighted (Parseval) average is nonnegative then some atom has nonnegative margin — the
weighted mean never exceeds the max when the weights are positive and sum to one.
Instantiating `margin c` with the pivot's structured lift-slack turns any averaging bound
`∑ t_c·margin_c ≥ 0` into an existence-of-good-pivot; supplying such a bound is separate. -/
theorem exists_nonneg_margin_of_weighted_average
    (D : WeightedDesign m k) (margin : Fin m → ℝ)
    (havg : 0 ≤ ∑ c, D.weight c * margin c) :
    ∃ c, 0 ≤ margin c := by
  by_contra hall
  push_neg at hall
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra hempty
    have hzero := D.weight_sum_one
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hzero
    exact one_ne_zero hzero.symm
  have hneg : ∑ c, D.weight c * margin c < ∑ c, D.weight c * (0 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hnonempty fun c _ => ?_
    exact mul_lt_mul_of_pos_left (hall c) (D.weight_pos c)
  simp only [mul_zero, Finset.sum_const_zero] at hneg
  exact absurd havg (not_le.mpr hneg)

end Gtz
