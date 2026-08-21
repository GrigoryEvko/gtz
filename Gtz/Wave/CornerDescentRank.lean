/-
# A corner resolves the identity on its own kernel

The tie locus is a minimum locus, not a level set: with `Φ = max_T λmin(S_T - 1)`
a tie is `{Φ = 0}` and weighted GTZ asserts `Φ ≥ 0` everywhere, so a real tie is
a first-order local minimum with no strict descent.  The question for a corner
is therefore how many independent descent directions it has to block.

## The projected atoms resolve the identity

Let `C` be a corner: `S_C - 1 = lam * u u^T` with `u` a unit vector, so the gap
has corank two and its kernel is the plane `u^perp`.  Let `B` carry an
orthonormal basis of that plane.  Then, because `B` is orthogonal to the axis,
the axis term dies under the congruence and

  **`Σ_{c ∈ C} (B^T g_c)(B^T g_c)^T = B^T S_C B = 1_2`**

(`Gtz.corner_projectedAtoms_resolve`).  The three inside atoms, projected to the
gap's own kernel, form a Parseval frame for that plane — always, at every
corner, with no genericity and no hypothesis beyond the corner equation.

## What that buys

A frame cannot be degenerate: the projected atoms span the plane
(`Gtz.corner_projectedAtom_ne_zero_of_probe`), because a probe they all miss
would be missed by the identity.  Every symmetric perturbation of the gap on its
kernel is reachable by moving the inside atoms, since the reachable set contains
`w h^T + h w^T` for every projected atom `h` and every `w`, and those span the
whole of `Sym(2)` as soon as the `h` span the plane.

So a corner has a **three-dimensional** family of descents to block, one for each
dimension of `Sym(2)`, where a corank-one tie has only **one**.  That asymmetry
is exactly the structural reason corner emptiness should be reachable, and it is
not a measurement: the resolution above is an identity.

[MEASURED first, then proved: over 400 random real corank-two corners the
descent map into `Sym(2)` had rank three in every one, with third singular value
exactly `sqrt 2` — a constant, which is what a resolution of the identity
produces, rather than the generic bound a rank count alone would give.]
-/
import Gtz.Wave.BranchTwoDeterminantSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The corner equation read against a kernel probe -/

/-- **A CORNER READS ITS OWN KERNEL AS THE IDENTITY.**  A probe orthogonal to
the axis sees the corner's atom sum exactly as it sees the identity: the axis
term carries the whole excess and dies against such a probe. -/
theorem corner_kernel_probe_form {gx gy gz u v : Fin 3 → ℝ} {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hperp : u ⬝ᵥ v = 0) :
    (gx ⬝ᵥ v) ^ 2 + (gy ⬝ᵥ v) ^ 2 + (gz ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => v ⬝ᵥ (M *ᵥ v)) hcorner
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.one_mulVec, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_comm v gx, dotProduct_comm v gy, dotProduct_comm v gz,
    dotProduct_comm v u, hperp] at h
  nlinarith [h]

/-- **THE PROJECTED ATOMS RESOLVE THE IDENTITY ON THE KERNEL.**  Stated at a
pair of kernel probes: the corner's atoms reproduce the inner product of any two
directions orthogonal to the axis. -/
theorem corner_projectedAtoms_resolve {gx gy gz u v w : Fin 3 → ℝ} {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hv : u ⬝ᵥ v = 0) (hw : u ⬝ᵥ w = 0) :
    (gx ⬝ᵥ v) * (gx ⬝ᵥ w) + (gy ⬝ᵥ v) * (gy ⬝ᵥ w) + (gz ⬝ᵥ v) * (gz ⬝ᵥ w)
      = v ⬝ᵥ w := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => v ⬝ᵥ (M *ᵥ w)) hcorner
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.one_mulVec, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul] at h
  rw [dotProduct_comm v gx, dotProduct_comm v gy, dotProduct_comm v gz,
    dotProduct_comm v u, hv] at h
  nlinarith [h]

/-! ## 2. No kernel probe is missed -/

/-- **THE PROJECTED ATOMS SPAN THE KERNEL.**  A nonzero probe orthogonal to the
axis is read by some inside atom: if all three missed it, the resolution would
make its own square length vanish. -/
theorem corner_projectedAtom_ne_zero_of_probe {gx gy gz u v : Fin 3 → ℝ}
    {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hperp : u ⬝ᵥ v = 0) (hv : v ≠ 0) :
    gx ⬝ᵥ v ≠ 0 ∨ gy ⬝ᵥ v ≠ 0 ∨ gz ⬝ᵥ v ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hform := corner_kernel_probe_form hcorner hperp
  rw [h1, h2, h3] at hform
  have hvv : v ⬝ᵥ v = 0 := by linarith [hform]
  exact hv (dotProduct_self_eq_zero.mp hvv)

/-- The squared readings of a kernel probe by the three inside atoms total the
probe's own square length — the diagonal case, isolated for reuse. -/
theorem corner_kernel_reading_total {gx gy gz u v : Fin 3 → ℝ} {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hperp : u ⬝ᵥ v = 0) (hunit : v ⬝ᵥ v = 1) :
    (gx ⬝ᵥ v) ^ 2 + (gy ⬝ᵥ v) ^ 2 + (gz ⬝ᵥ v) ^ 2 = 1 := by
  rw [corner_kernel_probe_form hcorner hperp, hunit]

/-- **TWO KERNEL PROBES ARE READ ORTHOGONALLY.**  Orthonormal directions in the
kernel stay orthonormal under the projected atoms — the off-diagonal half of the
resolution. -/
theorem corner_kernel_reading_cross {gx gy gz u v w : Fin 3 → ℝ} {lam : ℝ}
    (hcorner : atomMatrix gx + atomMatrix gy + atomMatrix gz
      = 1 + lam • atomMatrix u)
    (hv : u ⬝ᵥ v = 0) (hw : u ⬝ᵥ w = 0) (hcross : v ⬝ᵥ w = 0) :
    (gx ⬝ᵥ v) * (gx ⬝ᵥ w) + (gy ⬝ᵥ v) * (gy ⬝ᵥ w)
      + (gz ⬝ᵥ v) * (gz ⬝ᵥ w) = 0 := by
  rw [corner_projectedAtoms_resolve hcorner hv hw, hcross]

end Gtz
