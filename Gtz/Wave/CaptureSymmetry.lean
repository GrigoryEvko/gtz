import Gtz.Wave.PrivateSupportSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The capture symmetry — the captured core is symmetric

The exchange law `M H = H Mᵀ` and the symmetry of `H` make the captured
core `M H` symmetric.  The two-carrier capture law then loses one degree
of freedom: the two mixed entries agree.  The (B2) closure and the dense
branch consume this reduction.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.capture_transpose_eq` — **THE SYMMETRY.**
* `Gtz.capture_entry_symm` — the entry form.

## Vacuity

The statements are unconditional.
-/

namespace Gtz

open Matrix

variable {basisCount : ℕ}

/-- **THE CAPTURE SYMMETRY.**  The exchange law and the symmetry of the
Gram core make the captured core symmetric. -/
theorem capture_transpose_eq
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsymm : Hᵀ = H) (hexchange : M * H = H * Mᵀ) :
    (M * H)ᵀ = M * H := by
  rw [Matrix.transpose_mul, hsymm, ← hexchange]

/-- The entry form of the capture symmetry: the two mixed entries agree. -/
theorem capture_entry_symm
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hsymm : Hᵀ = H) (hexchange : M * H = H * Mᵀ)
    (firstSlot secondSlot : Fin basisCount) :
    (M * H) firstSlot secondSlot = (M * H) secondSlot firstSlot := by
  have hentry := congrFun (congrFun (capture_transpose_eq hsymm hexchange) firstSlot)
    secondSlot
  rw [Matrix.transpose_apply] at hentry
  exact hentry.symm

end Gtz
