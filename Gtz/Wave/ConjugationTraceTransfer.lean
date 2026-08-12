import Gtz.Wave.OffBlockColumnIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The conjugation trace transfer — a kernel-free intertwiner moves the trace

If `Q * A = D * Q` and `Q` has a trivial kernel, then `A` and `D` have the
same trace: `Q` is invertible, thus `A` is the conjugate of `D`.  The
fully-private-block kill uses this with `Q` the off-block column matrix,
`A` the off-block coefficient corner, and `D` the shifted-weight diagonal.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.trace_eq_of_kernel_free_conjugation` — **THE TRACE TRANSFER.**

## Vacuity

The statement is unconditional.
-/

namespace Gtz

open Matrix

/-- **THE TRACE TRANSFER.**  A kernel-free intertwiner `Q * A = D * Q`
forces `trace A = trace D`. -/
theorem trace_eq_of_kernel_free_conjugation {sideCount : ℕ}
    {Q A D : Matrix (Fin sideCount) (Fin sideCount) ℝ}
    (hconj : Q * A = D * Q)
    (hker : ∀ coeffVec : Fin sideCount → ℝ, Q *ᵥ coeffVec = 0 → coeffVec = 0) :
    Matrix.trace A = Matrix.trace D := by
  classical
  have hdet : Q.det ≠ 0 := by
    intro hzero
    obtain ⟨coeffVec, hne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    exact hne (hker coeffVec hmul)
  have hunit : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  have hA : A = Q⁻¹ * (D * Q) := by
    rw [← hconj, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hunit, Matrix.one_mul]
  rw [hA, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hunit,
    Matrix.mul_one]

end Gtz
