/-
# The reduction architecture: base ranks, the canonical list, and the endgame

The campaign's theorem-grade skeleton (diary §§42–52):

* rank 1 = pigeonhole; rank 2 = Sengupta–Pautov (arXiv:2604.05944), weighted form
  via atom replication + density;
* Theorem L (canonical list, `gtz_proof_gtz_allk_lift.md` §3.4): via crystallization
  M(s) = s(s+1)/2 + 1 and Naimark duality, GTZ for ALL n and ALL k is equivalent to
  the finite-per-rank list { weighted (m,s) : s ≥ 2, 2s ≤ m ≤ s(s+1)/2 + 1 };
* the binding residue: closing weighted (6,3) and (7,3) closes rank 3 for all n and
  co-rank ≤ 3 for every k. Weighted (6,3) is the single binding object of the
  hierarchy (diary §45, §52).

STATUS: statements (roadmap targets); proofs pending. `gtz_rank_one` is the
recommended first full end-to-end exercise of the definitions.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

/-- Rank 1 is the pigeonhole: Σ t_c g_c² = 1 with Σ t_c = 1 forces some g_c² ≥ 1. -/
theorem gtz_rank_one : GtzWeightedAll 1 := by
  intro m D
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- no atoms cannot resolve the identity: Parseval is contradictory
    subst hm
    have hp := D.isParseval
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hp
    have h00 : (0 : ℝ) = 1 := by
      have h := congrArg (fun M => M 0 0) hp
      simpa using h
    norm_num at h00
  · -- scalar Parseval at the (0,0) entry
    have hscalar : ∑ c, D.weight c * (D.atom c 0 * D.atom c 0) = 1 := by
      have h := congrArg (fun M => M 0 0) D.isParseval
      simpa [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply,
        Matrix.smul_apply, smul_eq_mul] using h
    -- pigeonhole: some atom has squared length ≥ 1
    have hex : ∃ c, 1 ≤ D.atom c 0 * D.atom c 0 := by
      by_contra hno
      push Not at hno
      have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
        Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
      have hlt : ∑ c, D.weight c * (D.atom c 0 * D.atom c 0) < ∑ c, D.weight c := by
        refine Finset.sum_lt_sum_of_nonempty hne fun c _ => ?_
        nlinarith [hno c, D.weight_pos c]
      rw [hscalar, D.weight_sum_one] at hlt
      exact lt_irrefl 1 hlt
    obtain ⟨c, hc⟩ := hex
    refine ⟨{c}, Finset.card_singleton c, ?_⟩
    -- the 1×1 block g² − 1 is a nonnegative multiple of the identity
    have hmat : subsetSum D {c} - 1
        = (D.atom c 0 * D.atom c 0 - 1) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      have hi : i = 0 := Subsingleton.elim i 0
      have hj : j = 0 := Subsingleton.elim j 0
      subst hi; subst hj
      simp [subsetSum, atomMatrix, Matrix.vecMulVec_apply,
        Matrix.smul_apply, smul_eq_mul]
    rw [Dominates, hmat]
    exact Matrix.PosSemidef.one.smul (by linarith)

/-- Rank 2 is the Sengupta–Pautov theorem (weighted form; the de-spectralized
Case-B pairing of diary §0 is the intended proof skeleton — finite sums and
squares, no spectral theorem, no Perron–Frobenius). -/
theorem gtz_rank_two : GtzWeightedAll 2 := by
  sorry

/-- The two binding cases close rank 3 (crystallization at k=3: M(3) = 7, and the
proven m ≤ 5 ledger — trivial m ≤ 3, pigeonhole m = 4, Naimark→rank-2 m = 5). -/
theorem rank_three_of_the_two_residuals
    (h63 : GtzWeighted 6 3) (h73 : GtzWeighted 7 3) :
    GtzWeightedAll 3 := by
  sorry

/-- **Theorem L (the canonical list).** GTZ at every rank and size follows from
the finite-per-rank canonical list — the master reduction of the program. -/
theorem gtz_of_canonical_list
    (hlist : ∀ s m', 2 ≤ s → 2 * s ≤ m' → m' ≤ s * (s + 1) / 2 + 1 →
      GtzWeighted m' s) :
    ∀ k, 1 ≤ k → GtzWeightedAll k := by
  sorry

/-- The weighted ⟹ original bridge (t = 1/n specialization plus the standard
frame dictionary): weighted GTZ at rank k gives the 1997 statement for all n. -/
theorem original_of_weighted (k : ℕ) (hk : 1 ≤ k) (h : GtzWeightedAll k) :
    ∀ n, k < n → GtzOriginal n k := by
  sorry

end Gtz
