/-
# Lemma F_k, combinatorial core: the Bhatia–Davis covering inequality at mean zero

The covering functional of the rank-k corner (the (k+1)-cycle of the weighted GTZ
program) reduces, in simplex coordinates x_i = ⟨h_i, u⟩, to:

  on { x ∈ ℝ^(k+1) : Σ x_i = 0, Σ x_i² = k+1 },  min_{i<j} x_i x_j ≤ −1,

with equality exactly at the two-valued configurations = the 2ᵏ − 1
fundamental-weight axes of A_k. The inequality is one line: every factor of
Σ_i (M − x_i)(x_i − m) is nonnegative, and the sum telescopes to −n(Mm + 1)
where n = k+1, M = max x, m = min x.

This file proves the inequality (`exists_pair_mul_le_neg_one`) sorry-free.
The equality classification (`two-valued ⟺ tie`) is a stated follow-up target.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

/-- The Bhatia–Davis telescope: for any x and any two reals M, m,
Σ (M − x_i)(x_i − m) = (M + m)·Σx − Σx² − n·M·m. Stated with the design
normalization Σx = 0, Σx² = n plugged in. -/
theorem bhatiaDavis_telescope {n : ℕ} (x : Fin n → ℝ) (bigM smallM : ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = n) :
    ∑ i, (bigM - x i) * (x i - smallM) = -(n : ℝ) * (bigM * smallM) - n := by
  calc ∑ i, (bigM - x i) * (x i - smallM)
      = ∑ i, ((bigM + smallM) * x i - x i ^ 2 - bigM * smallM) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = (bigM + smallM) * (∑ i, x i) - (∑ i, x i ^ 2)
          - (Finset.univ.card : ℝ) * (bigM * smallM) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
    _ = -(n : ℝ) * (bigM * smallM) - n := by
        rw [hsum, hsq, Finset.card_univ, Fintype.card_fin]; ring

/-- **Lemma F_k, combinatorial core (Bhatia–Davis at mean zero).**
On the zero-sum sphere Σx = 0, Σx² = n (n ≥ 2), some pair has product ≤ −1.
The witness pair is (argmax, argmin); the same argument is natively weighted.
This is the rank-uniform covering inequality behind the corner caps of the
weighted GTZ program (diary §52 / `gtz_proof_gtz_allk_lift.md` §2.2). -/
theorem exists_pair_mul_le_neg_one {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = n) :
    ∃ i j : Fin n, i ≠ j ∧ x i * x j ≤ -1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn
  have hzero : (⟨0, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  obtain ⟨iMax, -, hMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) x ⟨_, hzero⟩
  obtain ⟨iMin, -, hMin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin n)) x ⟨_, hzero⟩
  have hMax' : ∀ i, x i ≤ x iMax := fun i => hMax i (Finset.mem_univ i)
  have hMin' : ∀ i, x iMin ≤ x i := fun i => hMin i (Finset.mem_univ i)
  -- every Bhatia–Davis factor is nonnegative
  have hnonneg : 0 ≤ ∑ i, (x iMax - x i) * (x i - x iMin) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (sub_nonneg.mpr (hMax' i)) (sub_nonneg.mpr (hMin' i))
  have hkey : 0 ≤ -(n : ℝ) * (x iMax * x iMin) - n :=
    (bhatiaDavis_telescope x (x iMax) (x iMin) hsum hsq) ▸ hnonneg
  -- hence max · min ≤ −1
  have hprod : x iMax * x iMin ≤ -1 := by nlinarith [hkey, hnpos]
  -- the argmax and argmin are distinct (else x is constant 0, contradicting Σx² = n)
  have hne : iMax ≠ iMin := by
    rintro rfl
    have hconst : ∀ i, x i = x iMax := fun i => le_antisymm (hMax' i) (hMin' i)
    have hx0 : x iMax = 0 := by
      have hs : (n : ℝ) * x iMax = 0 := by
        calc (n : ℝ) * x iMax
            = ∑ _i : Fin n, x iMax := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          _ = ∑ i, x i := Finset.sum_congr rfl fun i _ => (hconst i).symm
          _ = 0 := hsum
      exact (mul_eq_zero.mp hs).resolve_left (ne_of_gt hnpos)
    have : (n : ℝ) = 0 := by
      rw [← hsq]
      exact Finset.sum_eq_zero fun i _ => by rw [hconst i, hx0]; ring
    exact absurd this (ne_of_gt hnpos)
  exact ⟨iMax, iMin, hne, hprod⟩

/-- ROADMAP (equality classification, diary §52): the tie min-pair = −1 holds
iff x is two-valued — p coordinates at q·c and q = n−p at −p·c with c = 1/√(pq) —
i.e. x lies on one of the 2^(n−1) − 1 fundamental-weight axes of A_(n−1). -/
theorem tie_iff_two_valued {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = n)
    (htie : ∀ i j : Fin n, i ≠ j → -1 ≤ x i * x j) :
    ∃ M m' : ℝ, M * m' = -1 ∧ ∀ i, x i = M ∨ x i = m' := by
  sorry

end Gtz
