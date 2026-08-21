/-
# The second Sylvester sign of the resolvent chart, and where its margin goes

`Gtz/Wave/ResolventBudgetLadder.lean` proves the FIRST sign of the resolvent
chart by counting: at most `k` labels have pivot above one, so at least `m - k`
clear `1 - rho_a ≥ 0`.  This module does the SECOND sign, and the argument is
again a budget rather than a search.

## The statement

  **`Gtz.exists_offDiag_resolventPairMinor_pos_six_three`: every design of six
  labels and rank three carries two distinct labels whose resolvent pair minor
  is strictly positive.**

Nothing is assumed: no tie, no primitivity, no chart.  The pair minor
`Gtz.resolventPairMinor` is the second principal minor of `1 - Pi`, so this says
the second Sylvester sign is cleared somewhere, exactly as the first is.

## Where it comes from, and why six

The landed budget `Gtz.sum_coWeight_resolventPairMinor` totals the co-weighted
pair minors at `(m - 1 - k)² - k`.  Subtracting the diagonal, whose term at `a`
is `(1 - t_a)²·(1 - 2·rho_a)`, leaves the off-diagonal mass, and two cheap
estimates bound the diagonal:

* `Gtz.coWeight_mul_pivot_le_one` -- `(1 - t_a)·rho_a ≤ 1`, one term of the
  projection law against the whole of it;
* `Gtz.sum_coWeightSq_pivot_ge` -- hence `Σ_a (1 - t_a)²·rho_a ≥ k - 1`.

Together (`Gtz.offDiag_resolventPairMinor_ge`):

  **`Σ_{a ≠ b} (1 - t_a)(1 - t_b)·pairMinor a b ≥ (m - 1 - k)² + k - m - Σ_c t_c²`**

and `Σ_c t_c² < 1` on the open simplex.  So the off-diagonal mass is strictly
positive as soon as `(m - 1 - k)² + k - m ≥ 1`.  At `(6,3)` that number is
`(5 - 3)² + 3 - 6 = 1`: **exactly on the boundary, and it is the third
independent place where six is the first size that works.**  At `(5,3)` it is
`1 + 3 - 5 = -1` and at `(6,4)` it is `1 + 4 - 6 = -1`, so the argument declines
to fire precisely where the collinear-pair statement is itself false.

## The margin is `1 - Σ_c t_c²`, and that is the campaign's obstruction, named

At `(6,3)` the bound reads

  **`Σ_{a ≠ b} (1 - t_a)(1 - t_b)·pairMinor a b ≥ 1 - Σ_c t_c²`** .

The right side is positive on the open simplex and vanishes exactly at a VERTEX,
where one weight carries everything.  Four separate lanes of this campaign have
independently reported that their certificates have margin proportional to the
smallest weight and cannot be strict.  This is that obstruction in closed form:
the second sign's whole surplus is `1 - Σ_c t_c²`, so any argument riding on it
degenerates exactly as `t` collapses to a vertex, and no absolute constant
survives.

[MEASURED as a check, never as a premise.  The budget identity
`Σ_{a,b}(1-t_a)(1-t_b)·pairMinor = (m-1-k)² - k` was verified to `1e-7` at every
sampled design of `(6,3)`, `(7,3)`, `(5,3)`, `(6,4)` and `(10,4)`; the bound
above held at every one, with slack `+0.47` at `(6,3)`; and a strictly positive
off-diagonal pair minor was present at every design of every size sampled,
including the two where the bound declines to fire.  The harness reproduces the
`(5,3)` diamond exactly first.]
-/
import Gtz.Wave.ResolventBudgetLadder
import Gtz.Wave.StressFreeCapRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. One term of the projection law against the whole of it -/

/-- **THE CO-WEIGHTED PIVOT IS AT MOST ONE.**  The projection law read at a
single label totals the co-weighted squared readings of that label at its own
pivot.  Every term is a square against a positive co-weight, so the diagonal
term alone is already bounded by the total.

This is the resolvent chart's counterpart of the landed weight-leverage cap, and
it says exactly that the co-Parseval projection has diagonal at most one. -/
theorem coWeight_mul_pivot_le_one (D : WeightedDesign m k) (hm : 2 ≤ m) (a : Fin m) :
    (1 - D.weight a) * pivot D Finset.univ a ≤ 1 := by
  classical
  have hlaw := sum_coWeight_mul_resolventReading_mul D hm a a
  have hsq : ∀ c : Fin m,
      (1 - D.weight c) * resolventReading D a c * resolventReading D c a
        = (1 - D.weight c) * (resolventReading D a c) ^ 2 := by
    intro c; rw [resolventReading_symm D hm c a]; ring
  rw [Finset.sum_congr rfl fun c _ => hsq c] at hlaw
  have hnn : ∀ c ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ (1 - D.weight c) * (resolventReading D a c) ^ 2 := by
    intro c _
    have hw := weight_lt_one D hm c
    have hs : (0:ℝ) ≤ 1 - D.weight c := by linarith
    exact mul_nonneg hs (sq_nonneg _)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ a)
  rw [hlaw, resolventReading_diag] at hsingle
  rcases eq_or_lt_of_le (pivot_univ_nonneg D hm a) with hzero | hpos
  · rw [← hzero]; norm_num
  · nlinarith [hsingle, hpos]

/-- **THE CO-WEIGHTED SQUARED PIVOT TOTAL.**  Since each co-weighted pivot is at
most one and they total the rank, weighting them once more by the co-weights
loses at most the total weight, which is one. -/
theorem sum_coWeightSq_pivot_ge (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (k : ℝ) - 1 ≤ ∑ a, (1 - D.weight a) ^ 2 * pivot D Finset.univ a := by
  have hsplit : ∀ a : Fin m, (1 - D.weight a) ^ 2 * pivot D Finset.univ a
      = (1 - D.weight a) * pivot D Finset.univ a
        - D.weight a * ((1 - D.weight a) * pivot D Finset.univ a) := fun a => by ring
  have hcap : ∑ a, D.weight a * ((1 - D.weight a) * pivot D Finset.univ a)
      ≤ ∑ a, D.weight a * 1 := by
    refine Finset.sum_le_sum fun a _ => ?_
    exact mul_le_mul_of_nonneg_left (coWeight_mul_pivot_le_one D hm a) (D.weight_pos a).le
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sub_distrib,
    descent_identity D hm]
  simp only [mul_one] at hcap
  rw [D.weight_sum_one] at hcap
  linarith

/-! ## 3. The off-diagonal pair minor mass -/

/-- The resolvent pair minor at a repeated label is one less twice the pivot. -/
theorem resolventPairMinor_self (D : WeightedDesign m k) (a : Fin m) :
    resolventPairMinor D a a = 1 - 2 * pivot D Finset.univ a := by
  rw [resolventPairMinor, resolventReading_diag]; ring

/-- The co-weights square to the size less two plus the squared weights. -/
theorem sum_sq_coWeight (D : WeightedDesign m k) :
    ∑ a, (1 - D.weight a) ^ 2 = (m : ℝ) - 2 + ∑ a, (D.weight a) ^ 2 := by
  have hterm : ∀ a : Fin m, (1 - D.weight a) ^ 2
      = 1 - 2 * D.weight a + (D.weight a) ^ 2 := fun a => by ring
  rw [Finset.sum_congr rfl fun a _ => hterm a]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum, D.weight_sum_one]
  ring

/-- **THE OFF-DIAGONAL PAIR MINOR MASS.**  The landed budget less its diagonal,
with the diagonal bounded by the two estimates above.  Every step is an
identity or one of those two bounds. -/
theorem offDiag_resolventPairMinor_ge (D : WeightedDesign m k) (hm : 2 ≤ m)
    (level : ℝ) (hlevel : level ≤ ((m : ℝ) - 1 - k) ^ 2 + k - m) :
    level - ∑ c, (D.weight c) ^ 2
      ≤ ∑ a, ∑ b ∈ Finset.univ.erase a,
          (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b := by
  classical
  -- split each row at its diagonal term
  have hrow : ∀ a : Fin m,
      (∑ b ∈ Finset.univ.erase a,
          (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b)
        = (∑ b, (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b)
          - (1 - D.weight a) ^ 2 * resolventPairMinor D a a := by
    intro a
    have := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
      (fun b => (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b)
      (Finset.mem_univ a)
    have hdiag : (1 - D.weight a) * (1 - D.weight a) * resolventPairMinor D a a
        = (1 - D.weight a) ^ 2 * resolventPairMinor D a a := by ring
    rw [hdiag] at this
    linarith
  rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_sub_distrib,
    sum_coWeight_resolventPairMinor D hm]
  -- the diagonal, in closed form
  have hdiagsum : ∑ a, (1 - D.weight a) ^ 2 * resolventPairMinor D a a
      = (∑ a, (1 - D.weight a) ^ 2)
        - 2 * ∑ a, (1 - D.weight a) ^ 2 * pivot D Finset.univ a := by
    have hterm : ∀ a : Fin m, (1 - D.weight a) ^ 2 * resolventPairMinor D a a
        = (1 - D.weight a) ^ 2
          - 2 * ((1 - D.weight a) ^ 2 * pivot D Finset.univ a) := by
      intro a; rw [resolventPairMinor_self]; ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hdiagsum, sum_sq_coWeight D]
  have hpiv := sum_coWeightSq_pivot_ge D hm
  linarith

/-! ## 4. At six labels and rank three the mass is positive -/

/-- **THE SECOND SIGN IS CLEARED SOMEWHERE.**  At six labels and rank three the
off-diagonal pair minor mass is at least `1 - Σ_c t_c²`, which is strictly
positive on the open simplex.  The constant `1` is `(6 - 1 - 3)² + 3 - 6`, and it
is exactly the threshold: the same number is `-1` at `(5,3)` and at `(6,4)`. -/
theorem offDiag_resolventPairMinor_pos_six_three (D : WeightedDesign 6 3) :
    0 < ∑ a, ∑ b ∈ Finset.univ.erase a,
      (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b := by
  have hbound := offDiag_resolventPairMinor_ge D (by norm_num : 2 ≤ 6) 1 (by norm_num)
  have hsq := sum_sq_weight_lt_one (by norm_num : 2 ≤ 6) D
  linarith

/-- **SOME PAIR OF DISTINCT LABELS CLEARS THE SECOND SYLVESTER SIGN.**  A strictly
positive total over the off-diagonal cannot have every term nonpositive, and each
term is a positive multiple of its own pair minor.

This is the resolvent chart's counterpart of the landed
`Gtz.exists_offDiag_pairMinor_pos`, and it holds at every design of six labels
and rank three with no hypothesis whatever. -/
theorem exists_offDiag_resolventPairMinor_pos_six_three (D : WeightedDesign 6 3) :
    ∃ a b : Fin 6, a ≠ b ∧ 0 < resolventPairMinor D a b := by
  classical
  by_contra hcon
  push_neg at hcon
  have hnonpos : ∑ a, ∑ b ∈ Finset.univ.erase a,
      (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b hb => ?_
    have hne : a ≠ b := fun h => (Finset.ne_of_mem_erase hb) h.symm
    have hminor := hcon a b hne
    have hwa := weight_lt_one D (by norm_num : 2 ≤ 6) a
    have hwb := weight_lt_one D (by norm_num : 2 ≤ 6) b
    have hprod : 0 ≤ (1 - D.weight a) * (1 - D.weight b) := by nlinarith
    nlinarith [hprod, hminor]
  exact absurd (offDiag_resolventPairMinor_pos_six_three D) (not_lt.mpr hnonpos)

end Gtz
