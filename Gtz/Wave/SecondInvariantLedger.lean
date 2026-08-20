import Gtz.Wave.BothLightCoreBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-!
# The second invariant ledger

The coweighted member sum `C = Σ_{a∈F}(1−t_a)·g_ag_aᵀ = A + t_xG_x + t_zG_z`
has three invariants.  The first is the trace — the coweight ledger.  The
third is the determinant ledger (`Gtz.coweighted_member_det_reading_ledger`).
This module lands the SECOND:

  `tr(adj(C)·A) = 3·det A + 2t_x·g_xᵀ(adjA)g_x + 2t_z·g_zᵀ(adjA)g_z
     + t_xt_z·(g_x×g_z)ᵀA(g_x×g_z)`

(`Gtz.trace_adj_mul_two_excluded`), a polynomial identity of `3×3` matrices,
and its reading form at a positive definite gap
(`Gtz.corner_second_invariant_ledger`):

  `tr(adj(C)·A) / det A = 3 + 2τ + π` ,

with `τ = t_xr_x + t_zr_z` the excluded reading total and
`π = t_xt_z(r_xr_z − p_xz²)` the excluded reading Gram.  Together with the
first and third ledgers this pins the whole characteristic polynomial of the
coweighted member reading matrix: its eigenvalues are
`{0, 1, 1+ν₁, 1+ν₂}` with `ν₁+ν₂ = τ` and `ν₁ν₂ = π` — the complete spectral
description of the member arena in the two excluded scalars.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **THE SECOND INVARIANT, MATRIX FORM.**  For every `3×3` matrix and every
pair of weighted atoms:

  `tr(adj(A + aG_u + bG_v)·A) = 3·det A + 2a·uᵀ(adjA)u + 2b·vᵀ(adjA)v
     + ab·(u×v)ᵀA(u×v)` . -/
theorem trace_adj_mul_two_excluded (A : Matrix (Fin 3) (Fin 3) ℝ)
    (a b : ℝ) (u v : Fin 3 → ℝ) :
    Matrix.trace ((A + a • atomMatrix u + b • atomMatrix v).adjugate * A)
      = 3 * A.det + 2 * a * (u ⬝ᵥ (A.adjugate *ᵥ u))
        + 2 * b * (v ⬝ᵥ (A.adjugate *ᵥ v))
        + a * b * (crossProduct u v ⬝ᵥ (A *ᵥ crossProduct u v)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.adjugate_fin_three, Matrix.det_fin_three, atomMatrix,
    Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE SECOND INVARIANT LEDGER, READINGS.**  At a subset with two excluded
atoms and a positive definite gap:

  `tr(adj(Σ_{a∈F}(1−t_a)G_a)·A) = det A·(3 + 2τ + π)` ,

with `τ` the excluded reading total and `π` the excluded reading Gram. -/
theorem corner_second_invariant_ledger (D : WeightedDesign m 3)
    (F : Finset (Fin m)) {x z : Fin m} (hxz : x ≠ z)
    (hcompl : (Fᶜ : Finset (Fin m)) = {x, z})
    (hpd : (subsetSum D F - 1).PosDef) :
    Matrix.trace
        ((∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)).adjugate
          * (subsetSum D F - 1))
      = (subsetSum D F - 1).det
        * (3
            + 2 * (D.weight x
                * (D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom x))
              + D.weight z
                * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)))
            + D.weight x * D.weight z
              * ((D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom x))
                    * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z))
                  - (D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z)) ^ 2)) := by
  classical
  have hsum : ∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)
      = (subsetSum D F - 1) + D.weight x • atomMatrix (D.atom x)
        + D.weight z • atomMatrix (D.atom z) := by
    have h := coweighted_member_sum_eq D F
    rw [hcompl] at h
    have hxs : x ∉ ({z} : Finset (Fin m)) := by simp [hxz]
    rw [Finset.sum_insert hxs, Finset.sum_singleton] at h
    rw [h]; abel
  rw [hsum, trace_adj_mul_two_excluded,
    adjugate_reading D F hpd (D.atom x), adjugate_reading D F hpd (D.atom z),
    cross_quadForm_eq_readingGram D F hpd (D.atom x) (D.atom z)]
  ring

end Gtz
