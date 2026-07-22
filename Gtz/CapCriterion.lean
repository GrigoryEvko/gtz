/-
# Branch (b): the cap criterion (signature-(k−1,1) rank-one completion)

For a (k−1)-set gate C′ with N = S_{C′} − I of signature (k−1, 1) — i.e. the gate
λ_{k−1}(S_{C′}) > 1 passes — a triple/k-set {e} ∪ C′ dominates iff the extra's cap
value satisfies g_eᵀ N⁻¹ g_e ≤ −1 (equivalently tr(N⁻¹ g_e g_eᵀ) ≤ −1).

Informal proof: det(N + ggᵀ) = det N · (1 + gᵀN⁻¹g) with det N < 0, and the
rank-one update preserves k−1 positive eigenvalues (Weyl interlacing), so PSD ⟺
det ≥ 0. Proven at k=3 in `gtz_proof_gtz3_ratpigeon.md` §4, general k in
`gtz_proof_gtz_allk_lift.md` §4.3.

Footgun notes: the negative-eigenvalue count is stated via `Nat.card` of the
subtype (no Fintype/decidability juggling); `IsUnit N.det` excludes the singular
boundary, where `N⁻¹` is Mathlib's junk zero matrix.

STATUS: statement (roadmap target); proof pending.
-/
import Mathlib
import Gtz.Basic

namespace Gtz

open Matrix

/-- **The cap criterion.** N real symmetric, invertible, with exactly one negative
eigenvalue: the rank-one completion N + ggᵀ is PSD iff gᵀN⁻¹g ≤ −1. -/
theorem cap_criterion {k : ℕ} (N : Matrix (Fin k) (Fin k) ℝ)
    (hN : N.IsHermitian) (hdet : IsUnit N.det)
    (hone : Nat.card {i // hN.eigenvalues i < 0} = 1)
    (g : Fin k → ℝ) :
    (N + Matrix.vecMulVec g g).PosSemidef ↔
      Matrix.trace (N⁻¹ * Matrix.vecMulVec g g) ≤ -1 := by
  sorry

end Gtz
