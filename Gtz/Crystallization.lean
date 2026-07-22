/-
# Crystallization: M(k) = k(k+1)/2 + 1 — bounded support at the sharp constant

Three elementary steps (proven informally at k=3 in `gtz_proof_gtz3_crystallization.md`,
general k in `gtz_proof_gtz_allk_lift.md` §3.3; verified at scale):

1. Feasibility of a weighted design ⟺ I_k ∈ conv{g_c g_cᵀ} in Sym(k) ≅ ℝ^(k(k+1)/2).
2. Carathéodory selects a subset of ≤ dim Sym(k) + 1 = k(k+1)/2 + 1 of the ORIGINAL
   atoms whose hull still contains I_k — a valid subdesign on a sub-support.
3. Φ = max_C λ_min(S_C) is monotone NON-INCREASING under dropping atoms (a max over
   a shrinking family of k-subsets; S_C is weight-free) — so the drop cannot raise Φ,
   and the infimum lives on m ≤ M(k). (DROP, never merge: merging raises Φ.)

Mathlib has Carathéodory (`Mathlib.Analysis.Convex.Caratheodory`). The formal
statement below is the payoff form: GTZ at all sizes follows from GTZ at the
canonically bounded sizes.

STATUS: statement (roadmap target); proof pending.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

/-- **Crystallization.** If weighted GTZ(k) holds for every size
m ≤ M(k) = k(k+1)/2 + 1, it holds for every size. -/
theorem crystallization (k : ℕ) (hk : 1 ≤ k)
    (hsmall : ∀ m, m ≤ k * (k + 1) / 2 + 1 → GtzWeighted m k) :
    GtzWeightedAll k := by
  sorry

end Gtz
