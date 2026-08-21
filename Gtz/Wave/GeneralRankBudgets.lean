/-
# The budgets at general rank, and the constants the brief gets wrong

The rank-three arm rests on five exact totals: the weighted leverage is three, the weighted
squared pairing is three, the weighted wedge is six, the weighted pair minor is one, and the
weighted squared bracket is one.  The survey says they transfer "with three replaced by
`k`".  **Two of the five constants are not linear in `k`,** and this module proves what they
are.

  weighted leverage      `Σ t_c ℓ_c = k`                    (landed, rank generic)
  weighted squared pairing `Σ t_a t_b ⟨g_a,g_b⟩² = k`       (`Gtz.pairingSq_budget`)
  weighted wedge         `Σ t_a t_b w_ab = k² − k`          (`Gtz.wedge_budget_rank`)
  weighted pair minor    `Σ t_a t_b q_ab = k² − 3k + 1`     (`Gtz.pairMinor_budget_rank`)

At `k = 3` these read `3`, `3`, `6`, `1`, reproducing the landed rank-three values
(`Gtz.wedge_mass_budget`, `Gtz.pairMinor_budget`).  At `k = 4` they read `4`, `4`, `12`,
`5`.  So "three replaced by `k`" is right for the first two and wrong for the last two.

## What the pair-minor constant buys, and where it stops

The rank-three consequence of the pair-minor budget is that every design carries a pair of
distinct atoms with positive pair minor, because the total is positive while the diagonal
contributes `Σ t_a² (1 − 2ℓ_a)`.  The same argument runs at every rank with `k² − 3k + 1`
in place of `1`, and that number is positive exactly when `k ≥ 3` — it is `−1` at `k = 2`
and `1`, `5`, `11`, `19` at `k = 3, 4, 5, 6`.  So the admissible-pair consequence is a
rank-three-and-up phenomenon, and its margin GROWS with the rank rather than staying at one.

## The proofs

All three are the trace of a product of two copies of the Parseval identity.  The only
input beyond it is `Gtz.atomMatrix_mul_atomMatrix`, which is already rank generic, and the
trace of an outer product.  No rank three anywhere.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Corner.CornerFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The trace of an outer product -/

/-- The trace of `a bᵀ` is `⟨a, b⟩`. -/
theorem trace_vecMulVec (a b : Fin k → ℝ) : (Matrix.vecMulVec a b).trace = a ⬝ᵥ b := by
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct]

/-- The squared pairing of two atoms is the trace of the product of their matrices. -/
theorem sq_dotProduct_eq_trace_mul (a b : Fin k → ℝ) :
    (a ⬝ᵥ b) ^ 2 = (atomMatrix a * atomMatrix b).trace := by
  rw [atomMatrix_mul_atomMatrix, Matrix.trace_smul, trace_vecMulVec, smul_eq_mul]
  ring

/-! ## 2. The squared pairing budget -/

/-- **THE WEIGHTED SQUARED PAIRING TOTALS THE RANK.**  Parseval squared, read by its trace.
At rank three this is the landed value three. -/
theorem pairingSq_budget (D : WeightedDesign m k) :
    ∑ a, ∑ b, D.weight a * (D.weight b * (D.atom a ⬝ᵥ D.atom b) ^ 2) = (k : ℝ) := by
  have hterm : ∀ a b : Fin m,
      D.weight a * (D.weight b * (D.atom a ⬝ᵥ D.atom b) ^ 2)
        = ((D.weight a • atomMatrix (D.atom a)) * (D.weight b • atomMatrix (D.atom b))).trace := by
    intro a b
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
      ← sq_dotProduct_eq_trace_mul, smul_eq_mul, smul_eq_mul]
  have hsum : ∑ a, ∑ b, D.weight a * (D.weight b * (D.atom a ⬝ᵥ D.atom b) ^ 2)
      = ((∑ a, D.weight a • atomMatrix (D.atom a))
          * (∑ b, D.weight b • atomMatrix (D.atom b))).trace := by
    rw [Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun b _ => hterm a b
  rw [hsum, D.isParseval, Matrix.one_mul, Matrix.trace_one, Fintype.card_fin]

/-! ## 3. The wedge budget -/

/-- **THE WEIGHTED WEDGE TOTALS `k² − k`.**  The squared leverage total less the squared
pairing total.  At rank three this is six, the landed `Gtz.wedge_mass_budget`; at rank four
it is twelve. -/
theorem wedge_budget_rank (D : WeightedDesign m k) :
    ∑ a, ∑ b, D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b) - (D.atom a ⬝ᵥ D.atom b) ^ 2))
      = (k : ℝ) ^ 2 - (k : ℝ) := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = (k : ℝ) := sum_weighted_leverage D
  have hpair := pairingSq_budget D
  have hsplit : ∑ a, ∑ b, D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b) - (D.atom a ⬝ᵥ D.atom b) ^ 2))
      = (∑ a, ∑ b, (D.weight a * leverageOf (D.atom a))
            * (D.weight b * leverageOf (D.atom b)))
        - ∑ a, ∑ b, D.weight a * (D.weight b * (D.atom a ⬝ᵥ D.atom b) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hsquare : ∑ a, ∑ b, (D.weight a * leverageOf (D.atom a))
      * (D.weight b * leverageOf (D.atom b)) = (k : ℝ) ^ 2 := by
    rw [← Finset.sum_mul_sum, hlev]; ring
  rw [hsplit, hsquare, hpair]

/-! ## 4. The pair-minor budget -/

/-- **THE WEIGHTED PAIR MINOR TOTALS `k² − 3k + 1`.**  The wedge total less twice the
leverage total plus the weight total: `(k² − k) − k − k + 1`.  At rank three this is one,
the landed `Gtz.pairMinor_budget`; at rank four it is five.  So the survey's "three replaced
by `k`" is wrong here — the constant is quadratic. -/
theorem pairMinor_budget_rank (D : WeightedDesign m k) :
    ∑ a, ∑ b, D.weight a * (D.weight b
        * ((leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1)
          - (D.atom a ⬝ᵥ D.atom b) ^ 2))
      = (k : ℝ) ^ 2 - 3 * (k : ℝ) + 1 := by
  have hlev : ∑ c, D.weight c * leverageOf (D.atom c) = (k : ℝ) := sum_weighted_leverage D
  have hone : ∑ c, D.weight c = 1 := D.weight_sum_one
  have hwedge := wedge_budget_rank D
  have hsplit : ∑ a, ∑ b, D.weight a * (D.weight b
        * ((leverageOf (D.atom a) - 1) * (leverageOf (D.atom b) - 1)
          - (D.atom a ⬝ᵥ D.atom b) ^ 2))
      = (∑ a, ∑ b, D.weight a * (D.weight b
            * (leverageOf (D.atom a) * leverageOf (D.atom b) - (D.atom a ⬝ᵥ D.atom b) ^ 2)))
        - (∑ a, ∑ b, (D.weight a * leverageOf (D.atom a)) * D.weight b)
        - (∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b)))
        + ∑ a, ∑ b, D.weight a * D.weight b := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hmixFirst : ∑ a, ∑ b, (D.weight a * leverageOf (D.atom a)) * D.weight b = (k : ℝ) := by
    rw [← Finset.sum_mul_sum, hlev, hone]; ring
  have hmixSecond : ∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b))
      = (k : ℝ) := by
    rw [show (∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b)))
        = ∑ a, ∑ b, D.weight a * (D.weight b * leverageOf (D.atom b)) from rfl,
      ← Finset.sum_mul_sum, hone, hlev]
    ring
  have hweights : ∑ a, ∑ b, D.weight a * D.weight b = (1 : ℝ) := by
    rw [← Finset.sum_mul_sum, hone]; ring
  rw [hsplit, hwedge, hmixFirst, hmixSecond, hweights]
  ring

/-! ## 5. The constant is positive exactly from rank three -/

/-- The pair-minor constant is negative at rank two, one at rank three, and grows after. -/
theorem pairMinor_constant_pos_iff (k : ℕ) :
    0 < (k : ℝ) ^ 2 - 3 * (k : ℝ) + 1 ↔ k = 0 ∨ 3 ≤ k := by
  constructor
  · intro hpos
    rcases Nat.lt_or_ge k 3 with hsmall | hbig
    · interval_cases k
      · exact Or.inl rfl
      · exfalso; norm_num at hpos
      · exfalso; norm_num at hpos
    · exact Or.inr hbig
  · rintro (rfl | hbig)
    · norm_num
    · have hk : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hbig
      nlinarith

theorem pairMinor_constant_three : (3 : ℝ) ^ 2 - 3 * 3 + 1 = 1 := by norm_num

theorem pairMinor_constant_four : (4 : ℝ) ^ 2 - 3 * 4 + 1 = 5 := by norm_num

theorem wedge_constant_three : (3 : ℝ) ^ 2 - 3 = 6 := by norm_num

theorem wedge_constant_four : (4 : ℝ) ^ 2 - 4 = 12 := by norm_num

end Gtz
