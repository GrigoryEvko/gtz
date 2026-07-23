/-
# Bernstein certificate core: coefficient floors are function floors

The kernel mathematics behind the subgapv-completion positivity certificates
(`CO_bernstein`/`CO_floors`): a polynomial written in the Bernstein basis on
`[0,1]` inherits every uniform bound of its coefficient list, because the
basis is a nonnegative partition of unity —

* each `b_{n,ν}(x) = C(n,ν)·xᵛ(1−x)^{n−ν}` is nonnegative on `[0,1]`;
* `Σ_ν b_{n,ν} = 1` (Mathlib's `bernsteinPolynomial.sum`);
* hence `min c_ν ≤ Σ c_ν·b_{n,ν}(x) ≤ max c_ν` — coefficient floors and
  ceilings ARE function floors and ceilings.

A certificate "these rationals are all `≥ 49/50`" therefore proves
`λ(x) ≥ 49/50` on the whole box, kernel-checked by `norm_num` on the list.
Stated univariate; the 4-variable certificates iterate one variable at a
time (a tensor coefficient slab is a coefficient list whose entries are
themselves certified polynomials).
-/
import Mathlib

namespace Gtz

open Polynomial

/-- Each Bernstein basis polynomial is nonnegative on `[0,1]`. -/
theorem bernstein_eval_nonneg (n k : ℕ) {x : ℝ} (hzero : 0 ≤ x)
    (hone : x ≤ 1) : 0 ≤ (bernsteinPolynomial ℝ n k).eval x := by
  rw [bernsteinPolynomial]
  simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_natCast]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hzero k))
    (pow_nonneg (by linarith) (n - k))

/-- The Bernstein basis evaluates to a partition of unity. -/
theorem bernstein_sum_eval (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n k).eval x = 1 := by
  have hsum := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
  rwa [eval_finset_sum, eval_one] at hsum

/-- **Coefficient floors are function floors**: if every Bernstein
coefficient is at least `floor`, the polynomial is at least `floor` on
`[0,1]`. The one-line mathematics of every positivity certificate. -/
theorem bernstein_coeff_floor (n : ℕ) (coeff : ℕ → ℝ) {floor : ℝ}
    (hfloor : ∀ k ∈ Finset.range (n + 1), floor ≤ coeff k)
    {x : ℝ} (hzero : 0 ≤ x) (hone : x ≤ 1) :
    floor ≤ ∑ k ∈ Finset.range (n + 1),
      coeff k * (bernsteinPolynomial ℝ n k).eval x := by
  calc floor
      = ∑ k ∈ Finset.range (n + 1),
          floor * (bernsteinPolynomial ℝ n k).eval x := by
        rw [← Finset.mul_sum, bernstein_sum_eval, mul_one]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          coeff k * (bernsteinPolynomial ℝ n k).eval x := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact mul_le_mul_of_nonneg_right (hfloor k hk)
          (bernstein_eval_nonneg n k hzero hone)

/-- **Coefficient ceilings are function ceilings** — the two-sided bracket's
other half. -/
theorem bernstein_coeff_ceiling (n : ℕ) (coeff : ℕ → ℝ) {ceiling : ℝ}
    (hceiling : ∀ k ∈ Finset.range (n + 1), coeff k ≤ ceiling)
    {x : ℝ} (hzero : 0 ≤ x) (hone : x ≤ 1) :
    ∑ k ∈ Finset.range (n + 1),
        coeff k * (bernsteinPolynomial ℝ n k).eval x ≤ ceiling := by
  calc ∑ k ∈ Finset.range (n + 1),
        coeff k * (bernsteinPolynomial ℝ n k).eval x
      ≤ ∑ k ∈ Finset.range (n + 1),
          ceiling * (bernsteinPolynomial ℝ n k).eval x := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact mul_le_mul_of_nonneg_right (hceiling k hk)
          (bernstein_eval_nonneg n k hzero hone)
    _ = ceiling := by rw [← Finset.mul_sum, bernstein_sum_eval, mul_one]

/-- **Uniform-sign certificates prove strict positivity**: strictly positive
coefficients give a strictly positive polynomial on `[0,1]` — via the floor
at the minimum over the (nonempty) coefficient list. -/
theorem bernstein_coeff_pos (n : ℕ) (coeff : ℕ → ℝ)
    (hpos : ∀ k ∈ Finset.range (n + 1), 0 < coeff k)
    {x : ℝ} (hzero : 0 ≤ x) (hone : x ≤ 1) :
    0 < ∑ k ∈ Finset.range (n + 1),
      coeff k * (bernsteinPolynomial ℝ n k).eval x := by
  obtain ⟨floor, hfloorPos, hfloorLe⟩ :
      ∃ floor : ℝ, 0 < floor ∧ ∀ k ∈ Finset.range (n + 1), floor ≤ coeff k := by
    obtain ⟨minWitness, hminMem, hminLe⟩ :=
      Finset.exists_min_image (Finset.range (n + 1)) coeff
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    exact ⟨coeff minWitness, hpos minWitness hminMem, hminLe⟩
  exact lt_of_lt_of_le hfloorPos
    (bernstein_coeff_floor n coeff hfloorLe hzero hone)

end Gtz
