/-
# The rational certificate layer, stage C1: ℚ-designs and the cast bridge

The endgame for the open cases (6,3) and (7,3) is certificate-based: concrete
rational designs and subset certificates, verified by DECIDABLE rational
arithmetic, consumed by the proven ℝ-theory. This file is the foundation:

* `RatDesign` — a weighted design with rational data, Parseval stated
  ENTRYWISE over ℚ (no matrix order, no PSD in the data; every field is
  checkable by `decide`-grade rational arithmetic on concrete instances);
* `RatDesign.toReal` — the cast into the proven `WeightedDesign` theory;
* the transfer lemmas: subset sums, leverages, and domination goals cast
  entrywise, so a rational computation certifies the real statement.

Stage C2 (next): the branch-(a) checker — Sylvester positivity of the 3×3
gate, rational pivots via the adjugate, soundness against `pigeonhole`.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- A weighted design with rational data; Parseval is entrywise ℚ-arithmetic. -/
structure RatDesign (m k : ℕ) where
  atom : Fin m → (Fin k → ℚ)
  weight : Fin m → ℚ
  weight_pos : ∀ c, 0 < weight c
  weight_sum_one : ∑ c, weight c = 1
  isParseval : ∀ i j : Fin k,
    (∑ c, weight c * (atom c i * atom c j)) = if i = j then 1 else 0

/-- The cast of a rational design into the real theory. -/
noncomputable def RatDesign.toReal (R : RatDesign m k) : WeightedDesign m k where
  atom c i := (R.atom c i : ℝ)
  weight c := (R.weight c : ℝ)
  weight_pos c := by exact_mod_cast R.weight_pos c
  weight_sum_one := by exact_mod_cast R.weight_sum_one
  isParseval := by
    ext i j
    have hcast : (∑ c, (R.weight c : ℝ) * ((R.atom c i : ℝ) * (R.atom c j : ℝ)))
        = ((if i = j then (1 : ℚ) else 0 : ℚ) : ℝ) := by
      exact_mod_cast R.isParseval i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul, Matrix.one_apply]
    rw [hcast]
    split_ifs <;> norm_num

/-- Subset sums cast entrywise. -/
theorem RatDesign.subsetSum_apply (R : RatDesign m k) (C : Finset (Fin m))
    (i j : Fin k) :
    subsetSum R.toReal C i j = ((∑ c ∈ C, R.atom c i * R.atom c j : ℚ) : ℝ) := by
  push_cast
  simp only [subsetSum, Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]
  rfl

/-- Leverages cast. -/
theorem RatDesign.leverage_cast (R : RatDesign m k) (c : Fin m) :
    leverageOf (R.toReal.atom c) = ((∑ i, R.atom c i ^ 2 : ℚ) : ℝ) := by
  push_cast
  simp only [leverageOf]
  rfl

/-- **The certification principle**: to dominate over ℝ it suffices that the
rational Gram shift is entrywise the cast of a rational matrix which is PSD
over ℝ — the domination GOAL is closed under the cast, so any rational
sufficient condition (Sylvester minors, diagonal dominance, an explicit
factorization) transfers. Stated as the entrywise rewrite of the goal. -/
theorem RatDesign.dominates_iff_cast (R : RatDesign m k) (C : Finset (Fin m)) :
    Dominates R.toReal C ↔
      (Matrix.of fun i j =>
        ((((∑ c ∈ C, R.atom c i * R.atom c j : ℚ))
          - if i = j then 1 else 0 : ℚ) : ℝ)).PosSemidef := by
  have hentry : subsetSum R.toReal C - 1
      = Matrix.of fun i j =>
        ((((∑ c ∈ C, R.atom c i * R.atom c j : ℚ))
          - if i = j then 1 else 0 : ℚ) : ℝ) := by
    ext i j
    rw [Matrix.sub_apply, R.subsetSum_apply C i j, Matrix.of_apply]
    push_cast
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  rw [Dominates, hentry]

end Gtz
