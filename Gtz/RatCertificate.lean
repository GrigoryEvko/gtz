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
import Gtz.PsdKit
import Gtz.TraceIdentity
import Gtz.Deflation

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

/-- **The branch-(a) certificate consumer** (stage C2): an LDL congruence
certificate for the gate — L invertible and a positive diagonal d with
Lᵀ(S_Q − 1)L = diagonal d — plus outsider pivots ≤ 1, produce a dominating
k-subset through the proven `pigeonhole`. This is the exact shape in which a
rational (6,3)/(7,3) closure will arrive: every hypothesis is a finite
identity or comparison of rationals after casting. (Sylvester's criterion is
NOT in Mathlib — R-MECH-3 — so the gate is certified by explicit congruence,
which is also the stronger, prover-friendly artifact.) -/
theorem certificate_dominates (D : WeightedDesign m k) (hk : 1 ≤ k)
    (Q : Finset (Fin m)) (hcard : Q.card = k + 1)
    (L : Matrix (Fin k) (Fin k) ℝ) (d : Fin k → ℝ)
    (hLdet : IsUnit L.det) (hdpos : ∀ i, 0 < d i)
    (hLDL : Lᵀ * (subsetSum D Q - 1) * L = Matrix.diagonal d)
    (hpivots : ∀ e ∈ Qᶜ, pivot D Q e ≤ 1) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C := by
  have hXT : (subsetSum D Q - 1)ᵀ = subsetSum D Q - 1 := by
    rw [Matrix.transpose_sub, subsetSum_transpose, Matrix.transpose_one]
  have hgate : (subsetSum D Q - 1).PosDef := by
    rw [posDef_congr_right hXT hLdet, hLDL]
    exact Matrix.PosDef.diagonal hdpos
  have houtside : ∑ e ∈ Qᶜ, D.weight e * (pivot D Q e - 1) ≤ 0 :=
    Finset.sum_nonpos fun e he => by
      nlinarith [D.weight_pos e, hpivots e he]
  obtain ⟨dd, hdd, hdom⟩ := pigeonhole D hk Q hgate hcard houtside
  refine ⟨Q.erase dd, ?_, hdom⟩
  rw [Finset.card_erase_of_mem hdd, hcard]
  omega

end Gtz
