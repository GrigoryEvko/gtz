/-
# The corner sum law: three gap determinants over one pair base

Every one-inside triple of a corner is the SAME base plus one inside atom: fix
an outside pair `{d,d'}` and let `P := S_{d,d'} - 1`.  Then the three triples
`{e,d,d'}` for `e` in the corner have gaps `P + G_e`, so the rank-one
determinant update applies to all three at once, and the corner equation
`sum_{e in C} G_e = 1 + lam*uu'` collapses their total:

  `sum_{e in C} det(P + G_e) = 3*det P + e2(P) + lam*<u, adj(P) u>` .

`Gtz.corner_sum_det_pairBase`.  The right side names only the OUTSIDE pair and
the corner scalars -- every inside coordinate is gone.  Since the three outside
pairs exhaust the nine one-inside triples, three instances of this law see the
whole family.

The consumer is `Gtz.exists_inside_det_pos_of_corner_sum_pos`: a positive right
side forces one of the three determinants positive, with no selection rule, no
eigenvector and no frame.

Two supporting laws, both general:

* `Gtz.quadForm_sum_of_corner` -- a corner reads any form at its three inside
  atoms with total `tr A + lam*<u, A u>`.  The matrix identity is linear, so this
  is nine scalar equations against the nine entries of `A`.
* `Gtz.trace_adjugate_fin_three` -- `tr(adj A) = e2(A)`, the second invariant.

MEASURED (scratchpad/f30/coh20.jl, 672429 failing-branch points, 2017287 outside
pairs; identity max rel err 4.3e-6, cancellation-limited):
THE SUM LAW DOES NOT CLOSE THE BRANCH.  The right side is positive at only
22.46% of pairs and 58.75% of branch points, so 41.25% of the branch has no pair
with a positive total.  The law is exact and general; it is the AGGREGATION that
is lossy, exactly as the campaign's doctrine predicts for a sum.  It is landed as
an instrument, not as a closure.
-/
import Gtz.Wave.CoherentHornDualFrame
import Gtz.Design.PlaneBranchComplementSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. A corner reads any form at total `tr A + lam*<u, A u>` -/

/-- **THE CORNER QUADRATIC TOTAL.**  If the three inside atoms of a corner sum to
`1 + lam*uu'`, then for EVERY form `A` their `A`-readings total
`tr A + lam*<u, A u>`.  The corner equation is a matrix identity, hence nine
scalar equations, and the total is their combination against the entries of
`A`. -/
theorem quadForm_sum_of_corner (A : Matrix (Fin 3) (Fin 3) ℝ)
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u) :
    gx ⬝ᵥ (A *ᵥ gx) + gy ⬝ᵥ (A *ᵥ gy) + gz ⬝ᵥ (A *ᵥ gz)
      = Matrix.trace A + lam * (u ⬝ᵥ (A *ᵥ u)) := by
  have h : ∀ i j : Fin 3,
      gx i * gx j + gy i * gy j + gz i * gz j
        = (if i = j then (1 : ℝ) else 0) + lam * (u i * u j) := by
    intro i j
    have hij := congrFun (congrFun hcorner i) j
    simpa [Matrix.add_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.one_apply] using hij
  have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2
  have h10 := h 1 0; have h11 := h 1 1; have h12 := h 1 2
  have h20 := h 2 0; have h21 := h 2 1; have h22 := h 2 2
  -- `norm_num` reduces `if 0 = 1` but NOT `if 0 = 2` at `Fin` literals
  simp at h00 h01 h02 h10 h11 h12 h20 h21 h22
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.trace_fin_three]
  linear_combination (A 0 0) * h00 + (A 0 1) * h01 + (A 0 2) * h02
    + (A 1 0) * h10 + (A 1 1) * h11 + (A 1 2) * h12
    + (A 2 0) * h20 + (A 2 1) * h21 + (A 2 2) * h22

/-! ## 2. The trace of the adjugate is the second invariant -/

set_option linter.unusedSimpArgs false in
/-- **`tr(adj A) = e2(A)`.**  The diagonal of the adjugate is the three principal
`2x2` minors, and their sum is the second invariant. -/
theorem trace_adjugate_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace A.adjugate
      = ((Matrix.trace A) ^ 2 - Matrix.trace (A * A)) / 2 := by
  simp [Matrix.trace_fin_three, Matrix.adjugate_fin_three, Matrix.mul_apply,
    Fin.sum_univ_three]
  ring

/-! ## 3. The corner sum law -/

/-- **THE CORNER SUM LAW.**  Over a fixed base the three inside atoms of a corner
total their gap determinants to pure base-and-corner data:

  `det(P + G_x) + det(P + G_y) + det(P + G_z)
     = 3*det P + e2(P) + lam*<u, adj(P) u>` .

Every inside coordinate cancels.  Taking `P` to be an outside pair's gap, the
three outside pairs exhaust the nine one-inside triples. -/
theorem corner_sum_det_pairBase (base : Matrix (Fin 3) (Fin 3) ℝ)
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u) :
    (base + atomMatrix gx).det + (base + atomMatrix gy).det
        + (base + atomMatrix gz).det
      = 3 * base.det
        + ((Matrix.trace base) ^ 2 - Matrix.trace (base * base)) / 2
        + lam * (u ⬝ᵥ (base.adjugate *ᵥ u)) := by
  rw [det_add_atomMatrix_fin_three, det_add_atomMatrix_fin_three,
    det_add_atomMatrix_fin_three]
  have hsum := quadForm_sum_of_corner base.adjugate gx gy gz u hcorner
  rw [trace_adjugate_fin_three] at hsum
  linarith [hsum]

/-- **THE CONSUMER.**  A positive total forces one of the three gap determinants
positive.  No selection rule, no eigenvector, no frame: whichever inside atom
carries it is named by the disjunction itself. -/
theorem exists_inside_det_pos_of_corner_sum_pos (base : Matrix (Fin 3) (Fin 3) ℝ)
    (gx gy gz u : Fin 3 → ℝ) {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hpos : 0 < 3 * base.det
        + ((Matrix.trace base) ^ 2 - Matrix.trace (base * base)) / 2
        + lam * (u ⬝ᵥ (base.adjugate *ᵥ u))) :
    0 < (base + atomMatrix gx).det ∨ 0 < (base + atomMatrix gy).det
      ∨ 0 < (base + atomMatrix gz).det := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy, hz⟩ := hcon
  rw [← corner_sum_det_pairBase base gx gy gz u hcorner] at hpos
  linarith

/-! ## 4. The corner form of the hypothesis -/

/-- The corner equation as an atom-sum identity: a corner's inside triple sums to
the identity plus its scaled axis. -/
theorem corner_atomSum_eq (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z)
      = 1 + lam • atomMatrix u := by
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  rw [hsum] at hgap
  rw [← hgap]
  abel

/-- **THE CORNER IS A WEAK DOMINATOR.**  Its gap is a nonnegative multiple of an
atom, hence positive semidefinite. -/
theorem corner_dominates (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    Dominates D C := by
  rw [Dominates, hgap]
  exact (posSemidef_atomMatrix u).smul hlam

/-- **THE INSIDE ATOMS OF A CORNER ARE HEAVY.**  A corner weakly dominates, so
each of its atoms carries leverage at least one — free, with no branch and no
measurement.  [MEASURED: strict at 100.0000% of the failing branch,
scratchpad/f30/coh21.jl.] -/
theorem corner_inside_one_le_leverage (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u) :
    1 ≤ leverageOf (D.atom x) :=
  one_le_leverage_of_mem_dominating_triple D hxy hxz hyz
    (corner_dominates D _ hlam hgap)

/-- **THE CORNER SUM LAW AT A DESIGN.**  The three one-inside triples over a
fixed outside pair total their gap determinants to the pair's own invariants
plus the corner's axis reading. -/
theorem corner_sum_det_over_pair (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (base : Matrix (Fin 3) (Fin 3) ℝ) :
    (base + atomMatrix (D.atom x)).det + (base + atomMatrix (D.atom y)).det
        + (base + atomMatrix (D.atom z)).det
      = 3 * base.det
        + ((Matrix.trace base) ^ 2 - Matrix.trace (base * base)) / 2
        + lam * (u ⬝ᵥ (base.adjugate *ᵥ u)) :=
  corner_sum_det_pairBase base _ _ _ u (corner_atomSum_eq D hxy hxz hyz hgap)

end Gtz
