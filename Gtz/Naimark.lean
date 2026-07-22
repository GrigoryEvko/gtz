/-
# Theorem N: the general-m weighted Naimark duality

For every weighted (m,k) design there is a dual weighted (m, m−k) design with the
SAME weights such that a k-subset C dominates in the primal iff its complement Cᶜ
dominates in the dual. Proven (informally) in four reversible congruence steps via
the CO-DESIGN completion — `gtz_proof_gtz_allk_lift.md` §3.2, audited twice, and
verified by the orchestrator's independent implementation (0/129,900 subset
instances).

Construction (for the eventual proof): h_c = W^{−1/2} g_c with W = T − I ≻ 0,
A = [√(1−t_c)·h_cᵀ] has orthonormal columns; complete [A | B] to an orthogonal
m×m matrix; the dual atoms are G_c = (row c of B)/√t_c with the SAME weights.
WARNING (recorded refutation, do not "simplify"): completing the primal Parseval
matrix V = [√t_c g_cᵀ] instead of the co-design A is WRONG — it fails already at
(m,k) = (2,1); the two coincide only at uniform weights.

STATUS: statement (roadmap target); proof pending.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

/-- **Theorem N (weighted Naimark duality).** Every weighted (m,k) design has a
dual (m, m−k) design with the same weights, flipping domination of complementary
subsets. -/
theorem weighted_naimark_duality {m k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (D : WeightedDesign m k) :
    ∃ D' : WeightedDesign m (m - k),
      (∀ c, D'.weight c = D.weight c) ∧
      ∀ C : Finset (Fin m), C.card = k →
        (Dominates D C ↔ Dominates D' Cᶜ) := by
  sorry

end Gtz
