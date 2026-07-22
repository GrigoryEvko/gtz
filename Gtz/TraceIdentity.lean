/-
# The rational Schur-pigeonhole layer: trace identity, excess balance, pigeonhole

The certificate class of the campaign (diary §46; k=3 in
`gtz_proof_gtz3_ratpigeon.md` §2, general (m,k) in `gtz_proof_gtz_allk_lift.md`
§4.1): for a base set Q with S_Q ≻ I and pivots q_c = tr((S_Q − I)⁻¹ g_c g_cᵀ),

  Σ_{d∈Q} (1 − t_d) q_d = k + Σ_{e∉Q} t_e q_e            (trace identity)
  Σ_{d∈Q} (1 − t_d)(q_d − 1) = Σ_{e∉Q} t_e (q_e − 1)     (excess balance, |Q| = k+1)

with the pigeonhole: nonpositive outsider excess forces an insider drop to
dominate (rank-one Schur, `Gtz.posSemidef_sub_vecMulVec_iff`).

Every statement carries `(subsetSum D Q − 1).PosDef` — Mathlib's inverse of a
singular matrix is the zero matrix (junk value), so `pivot` is only meaningful
under PosDef. ALL PROOFS in this file are complete (sorry-free).
-/
import Mathlib
import Gtz.Basic
import Gtz.SchurRankOne

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- M · (a bᵀ) = (M a) bᵀ. -/
theorem mul_vecMulVec_eq (M : Matrix (Fin k) (Fin k) ℝ) (a b : Fin k → ℝ) :
    M * Matrix.vecMulVec a b = Matrix.vecMulVec (M *ᵥ a) b := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The pivot in inner-product form: tr((S_Q−1)⁻¹ g gᵀ) = g ⬝ᵥ (S_Q−1)⁻¹ g. -/
theorem pivot_eq_dot (D : WeightedDesign m k) (Q : Finset (Fin m)) (c : Fin m) :
    pivot D Q c = (D.atom c) ⬝ᵥ ((subsetSum D Q - 1)⁻¹ *ᵥ (D.atom c)) := by
  rw [pivot, atomMatrix, mul_vecMulVec_eq, Matrix.trace_vecMulVec, dotProduct_comm]

/-- **The trace identity** (general (m,k), any base set): multiply Parseval's
S_Q − 1 = Σ_{d∈Q}(1−t_d)A_d − Σ_{e∉Q}t_e A_e by (S_Q−1)⁻¹ and take traces. -/
theorem trace_identity (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) :
    ∑ d ∈ Q, (1 - D.weight d) * pivot D Q d
      = k + ∑ e ∈ Qᶜ, D.weight e * pivot D Q e := by
  have hdet : IsUnit (subsetSum D Q - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hQ.det_pos)
  -- Parseval split across Q and its complement
  have hsplit : subsetSum D Q - 1
      = (∑ d ∈ Q, (1 - D.weight d) • atomMatrix (D.atom d))
        - ∑ e ∈ Qᶜ, D.weight e • atomMatrix (D.atom e) := by
    have hp := D.isParseval
    rw [← Finset.sum_add_sum_compl Q (fun c => D.weight c • atomMatrix (D.atom c))] at hp
    have h1 : ∑ d ∈ Q, (1 - D.weight d) • atomMatrix (D.atom d)
        = (∑ d ∈ Q, atomMatrix (D.atom d)) - ∑ d ∈ Q, D.weight d • atomMatrix (D.atom d) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d _ => by rw [sub_smul, one_smul]
    rw [subsetSum, ← hp, h1]
    abel
  -- trace both sides against (S_Q − 1)⁻¹
  have htr := congrArg (fun M => Matrix.trace ((subsetSum D Q - 1)⁻¹ * M)) hsplit
  simp only [Matrix.nonsing_inv_mul _ hdet, Matrix.trace_one, Matrix.mul_sub,
    Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Fintype.card_fin] at htr
  -- htr : (k : ℝ) = Σ_Q (1−t)·tr((S−1)⁻¹A_d) − Σ_Qᶜ t·tr((S−1)⁻¹A_e)
  simp only [pivot]
  linarith [htr]

/-- **Excess balance** at |Q| = k+1. -/
theorem excess_balance (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (hcard : Q.card = k + 1) :
    ∑ d ∈ Q, (1 - D.weight d) * (pivot D Q d - 1)
      = ∑ e ∈ Qᶜ, D.weight e * (pivot D Q e - 1) := by
  have e1 := trace_identity D Q hQ
  have e2 : ∑ d ∈ Q, (1 - D.weight d) = (k + 1 : ℝ) - ∑ d ∈ Q, D.weight d := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    push_cast
    ring
  have e3 : ∑ d ∈ Q, D.weight d + ∑ e ∈ Qᶜ, D.weight e = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact D.weight_sum_one
  have h4 : ∑ d ∈ Q, (1 - D.weight d) * (pivot D Q d - 1)
      = (∑ d ∈ Q, (1 - D.weight d) * pivot D Q d) - ∑ d ∈ Q, (1 - D.weight d) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  have h5 : ∑ e ∈ Qᶜ, D.weight e * (pivot D Q e - 1)
      = (∑ e ∈ Qᶜ, D.weight e * pivot D Q e) - ∑ e ∈ Qᶜ, D.weight e := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [h4, h5, e2]
  linarith [e1, e3]

/-- **Rank-one Schur step**: for d ∈ Q with S_Q ≻ 1, dropping d dominates iff
the pivot of d is ≤ 1. -/
theorem erase_dominates_iff_pivot_le_one (D : WeightedDesign m k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m} (hd : d ∈ Q) :
    Dominates D (Q.erase d) ↔ pivot D Q d ≤ 1 := by
  have hsub : subsetSum D (Q.erase d) - 1
      = (subsetSum D Q - 1) - Matrix.vecMulVec (D.atom d) (D.atom d) := by
    have h := Finset.sum_erase_add Q (fun c => atomMatrix (D.atom c)) hd
    rw [subsetSum, subsetSum, ← h, atomMatrix]
    abel
  rw [Dominates, hsub, posSemidef_sub_vecMulVec_iff _ hQ, pivot_eq_dot]

/-- **Branch (a), the pigeonhole**: |Q| = k+1, S_Q ≻ 1, outsiders' weighted
excess ≤ 0 ⟹ some insider drop dominates. The m = k+1 case (no outsiders) is
the exact tie — the (k+1)-cycle pigeonhole at every rank. -/
theorem pigeonhole (D : WeightedDesign m k) (hk : 1 ≤ k) (Q : Finset (Fin m))
    (hQ : (subsetSum D Q - 1).PosDef) (hcard : Q.card = k + 1)
    (houtside : ∑ e ∈ Qᶜ, D.weight e * (pivot D Q e - 1) ≤ 0) :
    ∃ d ∈ Q, Dominates D (Q.erase d) := by
  -- every weight is < 1 (at least two atoms since m ≥ |Q| = k+1 ≥ 2)
  have hm2 : 2 ≤ m := by
    have h1 : Q.card ≤ m := by simpa using Finset.card_le_univ Q
    omega
  have hwlt : ∀ c, D.weight c < 1 := by
    intro c
    obtain ⟨c', hc'⟩ := Fintype.exists_ne_of_one_lt_card (by simp only [Fintype.card_fin]; omega) c
    have hsum := Finset.sum_erase_add Finset.univ D.weight (Finset.mem_univ c)
    rw [D.weight_sum_one] at hsum
    have hpos : 0 < ∑ x ∈ Finset.univ.erase c, D.weight x :=
      Finset.sum_pos' (fun x _ => (D.weight_pos x).le)
        ⟨c', Finset.mem_erase.mpr ⟨hc', Finset.mem_univ c'⟩, D.weight_pos c'⟩
    linarith
  -- the insiders' excess is ≤ 0; positivity of the weights forces a pivot ≤ 1
  have hbal := excess_balance D Q hQ hcard
  have hins : ∑ d ∈ Q, (1 - D.weight d) * (pivot D Q d - 1) ≤ 0 := hbal ▸ houtside
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  by_contra hno
  push Not at hno
  have hall : ∀ d ∈ Q, 0 < (1 - D.weight d) * (pivot D Q d - 1) := by
    intro d hd
    have h1 : ¬ pivot D Q d ≤ 1 := fun hle =>
      hno d hd ((erase_dominates_iff_pivot_le_one D Q hQ hd).mpr hle)
    rw [not_le] at h1
    exact mul_pos (by linarith [hwlt d]) (by linarith)
  exact absurd hins (not_le.mpr (Finset.sum_pos hall hQne))

end Gtz
