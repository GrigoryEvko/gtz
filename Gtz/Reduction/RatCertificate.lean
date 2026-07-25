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

Stage C2 (shipped, below): the branch-(a) checker — the gate certified by an
explicit LDL congruence, rational pivots, soundness against `pigeonhole`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Design.TraceIdentity
import Gtz.Reduction.Deflation

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

/-- **The branch-(a) certificate consumer** (stage C2), in the shape `pigeonhole`
actually needs: an LDL congruence certificate for the gate — L invertible and a
positive diagonal d with Lᵀ(S_Q − 1)L = diagonal d — plus a NONPOSITIVE WEIGHTED
OUTSIDER EXCESS, produce a dominating k-subset. Every hypothesis is a finite
identity or comparison of rationals after casting. (The gate is certified by an
explicit congruence rather than by leading minors: the congruence carries its own
witness `(L, d)`, so nothing has to be re-derived at the use site.)

The excess hypothesis is ONE scalar comparison, and it is strictly weaker than
requiring every outsider pivot `q_e ≤ 1` — outsiders above the line are paid for by
outsiders below it. The gap is real and not marginal: sampling 16·10⁶ all-heavy
weighted (6,3) designs from a Stiefel-Haar × Dirichlet chart, this form fires on 96.8%
of the sample against 87.0% for the pointwise one. (Rates are properties of that
sampler, not of the family — the all-heavy family is non-compact and carries no
canonical measure. The RELATIVE fact is what matters, and it is exact: the pointwise
hypothesis implies this one and not conversely, with a rational witness at leverage 3.)
`certificate_dominates` below is the pointwise corollary. -/
theorem certificate_dominates_of_excess (D : WeightedDesign m k) (hk : 1 ≤ k)
    (Q : Finset (Fin m)) (hcard : Q.card = k + 1)
    (L : Matrix (Fin k) (Fin k) ℝ) (d : Fin k → ℝ)
    (hLdet : IsUnit L.det) (hdpos : ∀ i, 0 < d i)
    (hLDL : Lᵀ * (subsetSum D Q - 1) * L = Matrix.diagonal d)
    (hexcess : ∑ e ∈ Qᶜ, D.weight e * (pivot D Q e - 1) ≤ 0) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C := by
  have hXT : (subsetSum D Q - 1)ᵀ = subsetSum D Q - 1 := by
    rw [Matrix.transpose_sub, subsetSum_transpose, Matrix.transpose_one]
  have hgate : (subsetSum D Q - 1).PosDef := by
    rw [posDef_congr_right hXT hLdet, hLDL]
    exact Matrix.PosDef.diagonal hdpos
  obtain ⟨dd, hdd, hdom⟩ := pigeonhole D hk Q hgate hcard hexcess
  refine ⟨Q.erase dd, ?_, hdom⟩
  rw [Finset.card_erase_of_mem hdd, hcard]
  omega

/-- The pointwise reading of the branch-(a) consumer: every outsider pivot at most
`1`. Weaker than `certificate_dominates_of_excess` — positive weights turn the
pointwise bound into a nonpositive weighted sum termwise. -/
theorem certificate_dominates (D : WeightedDesign m k) (hk : 1 ≤ k)
    (Q : Finset (Fin m)) (hcard : Q.card = k + 1)
    (L : Matrix (Fin k) (Fin k) ℝ) (d : Fin k → ℝ)
    (hLdet : IsUnit L.det) (hdpos : ∀ i, 0 < d i)
    (hLDL : Lᵀ * (subsetSum D Q - 1) * L = Matrix.diagonal d)
    (hpivots : ∀ e ∈ Qᶜ, pivot D Q e ≤ 1) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C :=
  certificate_dominates_of_excess D hk Q hcard L d hLdet hdpos hLDL
    (Finset.sum_nonpos fun e he => by nlinarith [D.weight_pos e, hpivots e he])

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

/-- The rational Gram shift is invertible whenever it carries an LDL congruence with
positive diagonal — no separate determinant hypothesis is ever needed. -/
theorem ratGram_det_ne_zero {R : RatDesign m k} {Q : Finset (Fin m)}
    {Lq : Matrix (Fin k) (Fin k) ℚ} {dq : Fin k → ℚ} (hdpos : ∀ i, 0 < dq i)
    (hLDL : Lqᵀ * ratGram R Q * Lq = Matrix.diagonal dq) :
    (ratGram R Q).det ≠ 0 := by
  intro h0
  have hd := congrArg Matrix.det hLDL
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0,
    Matrix.det_diagonal] at hd
  have hpos : 0 < ∏ i, dq i := Finset.prod_pos fun i _ => hdpos i
  rw [← hd] at hpos
  simp at hpos

/-- **The fully rational branch-(a) certificate** (stage C3), in the weighted-sum
shape: every hypothesis is a finite ℚ-identity or ℚ-comparison on the certificate
data — checkable by exact rational arithmetic on concrete instances — and the
conclusion is real domination. This is the consumption theorem for the open cases.

The outsider hypothesis is a SINGLE rational comparison, not one per outsider. -/
theorem ratCertificate_dominates_of_excess (R : RatDesign m k) (hk : 1 ≤ k)
    (Q : Finset (Fin m)) (hcard : Q.card = k + 1)
    (Lq : Matrix (Fin k) (Fin k) ℚ) (dq : Fin k → ℚ)
    (hLdet : Lq.det ≠ 0) (hdpos : ∀ i, 0 < dq i)
    (hLDL : Lqᵀ * ratGram R Q * Lq = Matrix.diagonal dq)
    (hexcess : ∑ e ∈ Qᶜ,
      R.weight e * (R.atom e ⬝ᵥ ((ratGram R Q)⁻¹ *ᵥ R.atom e) - 1) ≤ 0) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates R.toReal C := by
  have hgramdet : (ratGram R Q).det ≠ 0 := ratGram_det_ne_zero hdpos hLDL
  refine certificate_dominates_of_excess R.toReal hk Q hcard
    (Lq.map (fun q : ℚ => (q : ℝ))) (fun i => (dq i : ℝ)) ?_ ?_ ?_ ?_
  · rw [det_cast]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hLdet)
  · intro i
    exact_mod_cast hdpos i
  · rw [R.gram_cast Q, ← Matrix.transpose_map, ← map_mul_cast, ← map_mul_cast,
      hLDL]
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.map_apply]
    · simp [Matrix.map_apply, hij]
  · have hterm : ∀ e ∈ Qᶜ, R.toReal.weight e * (pivot R.toReal Q e - 1)
        = ((R.weight e * (R.atom e ⬝ᵥ ((ratGram R Q)⁻¹ *ᵥ R.atom e) - 1) : ℚ) : ℝ) := by
      intro e _
      rw [R.pivot_cast Q e hgramdet]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hterm, ← Rat.cast_sum]
    exact_mod_cast hexcess

/-- The pointwise reading of the rational branch-(a) certificate. -/
theorem ratCertificate_dominates (R : RatDesign m k) (hk : 1 ≤ k)
    (Q : Finset (Fin m)) (hcard : Q.card = k + 1)
    (Lq : Matrix (Fin k) (Fin k) ℚ) (dq : Fin k → ℚ)
    (hLdet : Lq.det ≠ 0) (hdpos : ∀ i, 0 < dq i)
    (hLDL : Lqᵀ * ratGram R Q * Lq = Matrix.diagonal dq)
    (hpiv : ∀ e ∈ Qᶜ, R.atom e ⬝ᵥ ((ratGram R Q)⁻¹ *ᵥ R.atom e) ≤ 1) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates R.toReal C :=
  ratCertificate_dominates_of_excess R hk Q hcard Lq dq hLdet hdpos hLDL
    (Finset.sum_nonpos fun e he => by nlinarith [R.weight_pos e, hpiv e he])

end Gtz
