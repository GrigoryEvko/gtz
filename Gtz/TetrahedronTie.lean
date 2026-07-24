/-
# The twice-split tetrahedron tie is a concrete object (residuals 2/5, tie non-vacuity)

The whole off-tube / in-tube architecture of the A9 seam (residual 2) and the
tie-residue analysis (`Gtz.ResidueDissolution`, `Gtz.TieEigenvector`) rest on the
domination margin `phi = Phi - 1` actually REACHING `0` somewhere — the tie must be
a real, inhabited locus, not merely the abstract hypothesis `IsTie D -> margin D = 0`
that `ResidueDissolution` consumes.

This file supplies the explicit witness for weighted `(6,3)`. The twice-split
tetrahedron's best 3-subset uses the three scaled tetrahedron vectors

  gA = (1, 1, 1),  gB = (1, -1, -1),  gC = (-1, 1, -1),

whose subset moment `S_C = gA gAᵀ + gB gBᵀ + gC gCᵀ` gives the domination form
`vᵀ(S_C - I)v = ⟨gA,v⟩² + ⟨gB,v⟩² + ⟨gC,v⟩² - |v|²`. Two elementary, field-blind
kernel facts pin the tie:

  * `tetra_domination_form_sos` / `tetra_domination_form_nonneg`: the form is an
    explicit sum of three squares, so `S_C - I` is PSD — WEAK domination `Phi >= 1`;
  * `tetra_tie_direction_vanishes`: the same form VANISHES at the nonzero direction
    `(1, 1, -1)` (the dropped fourth tetrahedron vertex) — so domination is NOT
    strict; `Phi = 1`, `phi = 0` is attained. A genuine TIE.

Together they witness the `{0, 3, 3}` excess spectrum in coordinate-free form (a
one-dimensional zero locus of a PSD form) and make the abstract tie machinery
non-vacuous: a design on which `IsTie` holds exists. Pure `ring` / `positivity` /
`norm_num`; nothing about the hard cap mathematics is used or claimed here.
-/
import Mathlib

namespace Gtz

/-- **The tetra best-subset domination form is a sum of squares.** For the best
3-subset of the twice-split tetrahedron (atoms `(1,1,1)`, `(1,-1,-1)`, `(-1,1,-1)`),
the domination form `⟨gA,v⟩² + ⟨gB,v⟩² + ⟨gC,v⟩² - |v|²` equals the explicit
3-square SOS `(v0-v1)² + (v0+v2)² + (v1+v2)²`. Hence `S_C - I` is PSD: the subset
weakly dominates (`Phi >= 1`). -/
theorem tetra_domination_form_sos (v0 v1 v2 : ℝ) :
    ((v0 + v1 + v2) ^ 2 + (v0 - v1 - v2) ^ 2 + (-v0 + v1 - v2) ^ 2)
        - (v0 ^ 2 + v1 ^ 2 + v2 ^ 2)
      = (v0 - v1) ^ 2 + (v0 + v2) ^ 2 + (v1 + v2) ^ 2 := by
  ring

/-- **The domination form is nonnegative everywhere** (`S_C - I` PSD, weak
domination). Immediate from the SOS decomposition. -/
theorem tetra_domination_form_nonneg (v0 v1 v2 : ℝ) :
    0 ≤ ((v0 + v1 + v2) ^ 2 + (v0 - v1 - v2) ^ 2 + (-v0 + v1 - v2) ^ 2)
          - (v0 ^ 2 + v1 ^ 2 + v2 ^ 2) := by
  rw [tetra_domination_form_sos]
  positivity

/-- **The tie is real: the domination form vanishes at `(1, 1, -1)`.** At the
nonzero direction `(1, 1, -1)` — the dropped fourth tetrahedron vertex — the form
is `0`, so weak domination is TIGHT: `Phi = 1`, the margin `phi = 0` is attained.
Combined with `tetra_domination_form_nonneg` (PSD) this is weak-but-not-strict
domination, a genuine tie — the concrete inhabitant that makes the abstract tie
machinery (`Gtz.isTie_yields_tightDirection`, `Gtz.isTie_yields_unitEigenvector`)
non-vacuous. -/
theorem tetra_tie_direction_vanishes :
    (((1 : ℝ) + 1 + (-1)) ^ 2 + (1 - 1 - (-1)) ^ 2 + (-1 + 1 - (-1)) ^ 2)
        - ((1 : ℝ) ^ 2 + 1 ^ 2 + (-1) ^ 2) = 0 := by
  norm_num

end Gtz
