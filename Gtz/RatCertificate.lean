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

/-- The rational Gram shift of a subset: the ℚ-side of S_Q − 1. -/
def ratGram (R : RatDesign m k) (Q : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun i j =>
    (∑ c ∈ Q, R.atom c i * R.atom c j) - if i = j then 1 else 0

/-- Entrywise cast commutes with matrix products. -/
theorem map_mul_cast (M N : Matrix (Fin k) (Fin k) ℚ) :
    (M * N).map (fun q : ℚ => (q : ℝ))
      = M.map (fun q : ℚ => (q : ℝ)) * N.map (fun q : ℚ => (q : ℝ)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  push_cast
  rfl

/-- Entrywise cast commutes with determinants. -/
theorem det_cast (M : Matrix (Fin k) (Fin k) ℚ) :
    (M.map (fun q : ℚ => (q : ℝ))).det = ((M.det : ℚ) : ℝ) := by
  simpa using (RingHom.map_det (Rat.castHom ℝ) M).symm

/-- The Gram shift casts entrywise. -/
theorem RatDesign.gram_cast (R : RatDesign m k) (Q : Finset (Fin m)) :
    subsetSum R.toReal Q - 1
      = (ratGram R Q).map (fun q : ℚ => (q : ℝ)) := by
  ext i j
  rw [Matrix.sub_apply, R.subsetSum_apply Q i j, Matrix.map_apply, ratGram,
    Matrix.of_apply]
  push_cast
  rw [Matrix.one_apply]
  split_ifs <;> norm_num

/-- Matrix inverses cast along the field embedding ℚ → ℝ. -/
theorem ratInv_cast {M : Matrix (Fin k) (Fin k) ℚ} (hdet : M.det ≠ 0) :
    (M.map (fun q : ℚ => (q : ℝ)))⁻¹ = M⁻¹.map (fun q : ℚ => (q : ℝ)) := by
  apply Matrix.inv_eq_left_inv
  rw [← map_mul_cast, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.map_one _ (by norm_num) (by norm_num)]

/-- **The pivot casts**: over an invertible rational Gram shift, the real
pivot is the cast of the rational pivot. -/
theorem RatDesign.pivot_cast (R : RatDesign m k) (Q : Finset (Fin m))
    (e : Fin m) (hdet : (ratGram R Q).det ≠ 0) :
    pivot R.toReal Q e
      = ((R.atom e ⬝ᵥ ((ratGram R Q)⁻¹ *ᵥ R.atom e) : ℚ) : ℝ) := by
  rw [pivot_eq_dot, R.gram_cast Q, ratInv_cast hdet]
  push_cast
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
  push_cast
  rfl

/-- **The fully rational branch-(a) certificate** (stage C3): every hypothesis
is a finite ℚ-identity or ℚ-comparison on the certificate data — checkable by
exact rational arithmetic on concrete instances — and the conclusion is real
domination. This is the consumption theorem for the open cases. -/
theorem ratCertificate_dominates (R : RatDesign m k) (hk : 1 ≤ k)
    (Q : Finset (Fin m)) (hcard : Q.card = k + 1)
    (Lq : Matrix (Fin k) (Fin k) ℚ) (dq : Fin k → ℚ)
    (hLdet : Lq.det ≠ 0) (hdpos : ∀ i, 0 < dq i)
    (hLDL : Lqᵀ * ratGram R Q * Lq = Matrix.diagonal dq)
    (hpiv : ∀ e ∈ Qᶜ, R.atom e ⬝ᵥ ((ratGram R Q)⁻¹ *ᵥ R.atom e) ≤ 1) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates R.toReal C := by
  have hgramdet : (ratGram R Q).det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hLDL
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0,
      Matrix.det_diagonal] at hd
    have hpos : 0 < ∏ i, dq i := Finset.prod_pos fun i _ => hdpos i
    rw [← hd] at hpos
    simp at hpos
  refine certificate_dominates R.toReal hk Q hcard
    (Lq.map (fun q : ℚ => (q : ℝ))) (fun i => (dq i : ℝ)) ?_ ?_ ?_ ?_
  · rw [det_cast]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hLdet)
  · intro i
    exact_mod_cast hdpos i
  · rw [R.gram_cast Q, ← Matrix.transpose_map, ← map_mul_cast, ← map_mul_cast,
      hLDL]
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.map_apply, Matrix.diagonal_apply]
    · simp [Matrix.map_apply, Matrix.diagonal_apply, hij]
  · intro e he
    rw [R.pivot_cast Q e hgramdet]
    exact_mod_cast hpiv e he

end Gtz
