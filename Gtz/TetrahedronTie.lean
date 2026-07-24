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

open Matrix

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

/-! ### The same tie at the concrete gap-matrix level

The scalar facts above are exactly `vᵀ(S_C − I)v` for the twice-split tetrahedron's
best 3-subset, spelled out over the actual rank-one atom matrices `g gᵀ`. Here that
correspondence is a theorem, not a docstring: the gap matrix is built from the three
atoms as `∑ vecMulVec g_c g_c − I`, and its quadratic form is the SOS — so these lemmas
genuinely reference the GTZ moment object, not an abstract polynomial. -/

/-- Tetrahedron atom `gA = (1, 1, 1)` of the best 3-subset. -/
def tetraAtomA : Fin 3 → ℝ := ![1, 1, 1]

/-- Tetrahedron atom `gB = (1, −1, −1)`. -/
def tetraAtomB : Fin 3 → ℝ := ![1, -1, -1]

/-- Tetrahedron atom `gC = (−1, 1, −1)`. -/
def tetraAtomC : Fin 3 → ℝ := ![-1, 1, -1]

/-- The subset moment `S_C = gA gAᵀ + gB gBᵀ + gC gCᵀ` — the sum of the three rank-one
atom matrices, the GTZ moment object for this subset. -/
noncomputable def tetraSubsetMoment : Matrix (Fin 3) (Fin 3) ℝ :=
  vecMulVec tetraAtomA tetraAtomA + vecMulVec tetraAtomB tetraAtomB
    + vecMulVec tetraAtomC tetraAtomC

/-- The domination gap `S_C − I`. -/
noncomputable def tetraGapMatrix : Matrix (Fin 3) (Fin 3) ℝ := tetraSubsetMoment - 1

/-- **The gap matrix's quadratic form is the SOS.** `vᵀ(S_C − I)v = (v0−v1)² +
(v0+v2)² + (v1+v2)²`, the same three-square decomposition as `tetra_domination_form_sos`
but over the ACTUAL atom-built gap matrix — so `S_C − I` really is this PSD form. -/
theorem tetraGapMatrix_quadForm (v0 v1 v2 : ℝ) :
    (![v0, v1, v2] : Fin 3 → ℝ) ⬝ᵥ tetraGapMatrix.mulVec ![v0, v1, v2]
      = (v0 - v1) ^ 2 + (v0 + v2) ^ 2 + (v1 + v2) ^ 2 := by
  simp [tetraGapMatrix, tetraSubsetMoment, tetraAtomA, tetraAtomB, tetraAtomC,
    Matrix.vecMulVec, Matrix.mulVec, Matrix.sub_apply, Matrix.add_apply, dotProduct,
    Fin.sum_univ_three, Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

/-- **The gap matrix is positive semidefinite** on its quadratic form (`S_C − I ⪰ 0`,
weak domination `Phi ≥ 1`). Immediate from the SOS. -/
theorem tetraGapMatrix_quadForm_nonneg (v0 v1 v2 : ℝ) :
    0 ≤ (![v0, v1, v2] : Fin 3 → ℝ) ⬝ᵥ tetraGapMatrix.mulVec ![v0, v1, v2] := by
  rw [tetraGapMatrix_quadForm]; positivity

/-- **The tie at the matrix level**: the gap matrix's quadratic form VANISHES at the
nonzero direction `(1, 1, −1)`. With `tetraGapMatrix_quadForm_nonneg` (PSD) this is a
genuine tie — `Phi = 1`, margin `0`, attained on the actual `∑ atom moment − I`. -/
theorem tetraGapMatrix_quadForm_at_null :
    (![1, 1, -1] : Fin 3 → ℝ) ⬝ᵥ tetraGapMatrix.mulVec ![1, 1, -1] = 0 := by
  rw [tetraGapMatrix_quadForm]; norm_num

end Gtz
