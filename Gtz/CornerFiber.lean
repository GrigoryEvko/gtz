/-
# Theorem B_k: the exact (k+1)-cycle corner fiber closes at every rank

The zero-margin extremal of the entire problem is the (k+1)-cycle: k+1 vectors
h_i ∈ ℝᵏ with |h_i|² = k, ⟨h_i, h_j⟩ = −1 (the regular simplex at leverage k;
Σ h_i h_iᵀ = (k+1)·I, weight-free). Every design containing these exact heavies —
any weights, any extras — has a dominating k-subset, found by the certificate:

* the trace forces Σ_e t_e(ℓ_e − k) = 0 identically (audit F1, diary §52) —
  PROVEN below (`corner_balance_forced`) — so the Q₀-pigeonhole always fires at
  the tie: dropping any heavy d leaves S = (k+1)I − h_d h_dᵀ ⪰ I;
* separately (the lemma the deformed-corner program consumes): any extra with
  ℓ_e > k is caught strictly by its best cap in every direction, including the
  2ᵏ − 1 hole axes — via Lemma F_k (`Gtz.exists_pair_mul_le_neg_one`) and the
  corner resolvent B⁻¹ = (I + h_i h_jᵀ + h_j h_iᵀ)/k.

Proven informally: k=3 `gtz_proof_gtz3_ratpigeon.md` §5 (3/3 audits), general k
`gtz_proof_gtz_allk_lift.md` §2.4 (2/2 audits, with the F1 case-split correction).
-/
import Mathlib
import Gtz.Basic
import Gtz.BhatiaDavis
import Gtz.TraceIdentity

namespace Gtz

variable {m k : ℕ}

/-- The exact-corner hypothesis: an injective embedding of k+1 simplex heavies
at leverage k (Gram: diagonal k, off-diagonal −1) into the design. -/
def HasExactCorner (D : WeightedDesign m k) (emb : Fin (k + 1) → Fin m) : Prop :=
  Function.Injective emb ∧
    (∀ i, leverageOf (D.atom (emb i)) = k) ∧
    (∀ i j, i ≠ j → ∑ t, D.atom (emb i) t * D.atom (emb j) t = -1)

/-- **The forced balance** (audit F1, diary §52): at the exact corner fiber the
extras' weighted leverage-excess vanishes identically — pure trace algebra.
Consequently the Q₀-pigeonhole always fires at the tie. -/
theorem corner_balance_forced (D : WeightedDesign m k)
    (emb : Fin (k + 1) → Fin m) (hc : HasExactCorner D emb) :
    ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e * (leverageOf (D.atom e) - k) = 0 := by
  obtain ⟨hinj, hlev, -⟩ := hc
  -- trace of Parseval: Σ_c t_c ℓ_c = k
  have htrace : ∑ c, D.weight c * leverageOf (D.atom c) = (k : ℝ) := by
    have h := congrArg Matrix.trace D.isParseval
    simpa [Matrix.trace_sum, Matrix.trace_smul, trace_atomMatrix, smul_eq_mul,
      Matrix.trace_one, Fintype.card_fin] using h
  have hsplitL : ∑ c ∈ Finset.univ.image emb, D.weight c * leverageOf (D.atom c)
      + ∑ c ∈ (Finset.univ.image emb)ᶜ, D.weight c * leverageOf (D.atom c) = (k : ℝ) := by
    rw [Finset.sum_add_sum_compl]; exact htrace
  have hsplitW : ∑ c ∈ Finset.univ.image emb, D.weight c
      + ∑ c ∈ (Finset.univ.image emb)ᶜ, D.weight c = 1 := by
    rw [Finset.sum_add_sum_compl]; exact D.weight_sum_one
  -- the corner heavies have leverage exactly k
  have hins : ∑ c ∈ Finset.univ.image emb, D.weight c * leverageOf (D.atom c)
      = (k : ℝ) * ∑ c ∈ Finset.univ.image emb, D.weight c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hcS => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcS
    rw [hlev i]; ring
  have hgoal : ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e * (leverageOf (D.atom e) - k)
      = (∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e * leverageOf (D.atom e))
        - (k : ℝ) * ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hgoal,
    show ∑ e ∈ (Finset.univ.image emb)ᶜ, D.weight e
        = 1 - ∑ c ∈ Finset.univ.image emb, D.weight c by linarith [hsplitW]]
  ring_nf
  ring_nf at hins hsplitL
  linarith [hsplitL, hins]

/-- **Theorem B_k.** The exact (k+1)-cycle corner fiber of weighted (m,k) closes:
every design containing the exact simplex heavies has a dominating k-subset —
ρ = 1 exactly on the wall, at every rank and every size.
ROADMAP: reduces to the tie-pigeonhole via `corner_balance_forced` +
`pigeonhole` + the exact spectrum of (k+1)I − h_dh_dᵀ. -/
theorem corner_fiber_dominates (D : WeightedDesign m k) (hk : 2 ≤ k)
    (emb : Fin (k + 1) → Fin m) (hc : HasExactCorner D emb) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C := by
  sorry

end Gtz
