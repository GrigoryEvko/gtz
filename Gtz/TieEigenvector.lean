/-
# The geometric characterization of a tie (residual 10 entry point)

A single named composite chaining `Gtz.ResidueDissolution.isTie_yields_tightDirection`
(a tie's gap matrix is PSD-but-singular, so it has a nonzero null direction) with
`Gtz.RayleighCertificate.tightDirection_isEigenvector` (that null direction is a
unit eigenvector of the dominating subset). The result is the crisp geometric
reading of the `Φ = 1` boundary:

    IsTie D  ⟹  ∃ dominating C and a NONZERO w with  S_C · w = w.

This is the entry point the frame-existence approach (`Gtz.FrameBridge`,
`Gtz.RayleighCertificate`) builds on — every tie is a dominating subset carrying an
eigenvalue-1 eigenvector, and the whole per-direction KKT certificate follows. The
remaining wall is the assembly of the stress multiplier across the family of such
eigenvectors (the eigenvalue-subdifferential / Danskin content absent from Mathlib).
-/
import Mathlib
import Gtz.ResidueDissolution
import Gtz.RayleighCertificate

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **A tie carries a unit eigenvector** (the geometric reading of `Φ = 1`). Every
tie has a dominating `k`-subset `C` and a NONZERO direction `eigenDir` fixed by the
subset sum, `S_C · eigenDir = eigenDir`. So the `Φ = 1` boundary is exactly "some
dominating subset has an eigenvalue-1 eigenvector": weak domination
(`λ_min(S_C) ≥ 1`) meets non-strict domination (`λ_min(S_C) = 1` achieved). Chains
`isTie_yields_tightDirection` (PSD-but-singular ⟹ nonzero null direction of the gap)
with `tightDirection_isEigenvector` (null direction of the gap ⟹ unit eigenvector of
the subset sum). The single entry point the frame-existence / multiplier-assembly
approach consumes. -/
theorem isTie_yields_unitEigenvector {D : WeightedDesign m k} (htie : IsTie D) :
    ∃ (C : Finset (Fin m)) (eigenDir : Fin k → ℝ),
      C.card = k ∧ Dominates D C ∧ eigenDir ≠ 0 ∧
      subsetSum D C *ᵥ eigenDir = eigenDir := by
  obtain ⟨C, eigenDir, hcard, hdom, hne, htight⟩ := isTie_yields_tightDirection htie
  exact ⟨C, eigenDir, hcard, hdom, hne,
    tightDirection_isEigenvector D hdom htight⟩

end Gtz
