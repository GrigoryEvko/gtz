import Gtz.Wave.AdjugateDowndateReadings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-!
# The compound probes

The moment probe family (`Gtz.fourSet_inverse_moment_probe`) reads the FIRST
compound of Parseval — every law it yields is linear in the reading matrix.
This module opens the SECOND compound: the adjugate of the coweighted member
sum, probed at the excluded atoms.

The primitives are three polynomial identities of `3×3` matrices:

* `Gtz.adj_add_atomMatrix_probe` — adding one atom moves an adjugate reading
  by a cross energy:

    `wᵀ·adj(M + vvᵀ)·w = wᵀ·(adj M)·w + (w×v)ᵀM(w×v)` .

* `Gtz.adj_sum_four_atomMatrix` — the ADJUGATE CAUCHY-BINET: the adjugate of
  a weighted sum of four atoms is the pair-wedge sum

    `adj(Σ_a w_a v_av_aᵀ) = Σ_{a<b} w_aw_b·(v_a×v_b)(v_a×v_b)ᵀ` .

* `Gtz.adj_probe_two_excluded` — with `C = A + t_xG_x + t_zG_z`, the
  `z`-probe of `adj A` transports to `C`:

    `g_zᵀ(adj A)g_z = g_zᵀ(adj C)g_z − t_x·(g_z×g_x)ᵀC(g_z×g_x)` .

## The corner consequence

At the corner the coweighted member sum IS `C = A_y + t_xG_x + t_zG_z`
(`Gtz.coweighted_member_sum_eq`), a PSD matrix, and `g_zᵀ(adjA_y)g_z` is the
reading `r_z·det A_y`.  So the second-compound probe becomes
(`Gtz.corner_excluded_reading_wedge_dominated`):

  `det A_y·r_z + t_x·(g_z×g_x)ᵀC(g_z×g_x) = g_zᵀ·adj(C)·g_z` ,

with both left terms nonnegative on the cell.  By the adjugate Cauchy-Binet
the right side is the coweighted PAIR-WEDGE energy of the members read at
`g_z` — a quantity the trace-level ledgers cannot see.  This is the first
family that couples an excluded reading to the member wedges exactly, which
is the coupling the tetrahedral foil proves every certificate must have.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The three primitives -/

/-- **THE MIXED COMPOUND PROBE.**  Adding one atom moves an adjugate reading
by a cross energy:

  `wᵀ·adj(M + vvᵀ)·w = wᵀ·(adj M)·w + (w×v)ᵀM(w×v)` . -/
theorem adj_add_atomMatrix_probe (M : Matrix (Fin 3) (Fin 3) ℝ)
    (v w : Fin 3 → ℝ) :
    w ⬝ᵥ ((M + atomMatrix v).adjugate *ᵥ w)
      = w ⬝ᵥ (M.adjugate *ᵥ w)
        + crossProduct w v ⬝ᵥ (M *ᵥ crossProduct w v) := by
  simp only [Matrix.adjugate_fin_three, atomMatrix, Matrix.add_apply,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE ADJUGATE CAUCHY-BINET.**  The adjugate of a weighted sum of four
rank-one atoms of `ℝ³` is the weighted sum of its pair wedges:

  `adj(Σ_a w_a v_av_aᵀ) = Σ_{a<b} w_aw_b·(v_a×v_b)(v_a×v_b)ᵀ` . -/
theorem adj_sum_four_atomMatrix (w₁ w₂ w₃ w₄ : ℝ) (v₁ v₂ v₃ v₄ : Fin 3 → ℝ) :
    (w₁ • atomMatrix v₁ + w₂ • atomMatrix v₂ + w₃ • atomMatrix v₃
      + w₄ • atomMatrix v₄).adjugate
      = (w₁ * w₂) • atomMatrix (crossProduct v₁ v₂)
        + (w₁ * w₃) • atomMatrix (crossProduct v₁ v₃)
        + (w₁ * w₄) • atomMatrix (crossProduct v₁ v₄)
        + (w₂ * w₃) • atomMatrix (crossProduct v₂ v₃)
        + (w₂ * w₄) • atomMatrix (crossProduct v₂ v₄)
        + (w₃ * w₄) • atomMatrix (crossProduct v₃ v₄) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.adjugate_fin_three, atomMatrix, Matrix.vecMulVec_apply,
        cross_apply]
      ring

/-- **THE TWO-EXCLUDED PROBE.**  With `C = A + t_xG_x + t_zG_z`, the
`z`-probe of `adj A` transports to `C` with one cross energy:

  `g_zᵀ(adj A)g_z = g_zᵀ(adj C)g_z − t_x·(g_z×g_x)ᵀC(g_z×g_x)` . -/
theorem adj_probe_two_excluded (A : Matrix (Fin 3) (Fin 3) ℝ)
    (gx gz : Fin 3 → ℝ) (tx tz : ℝ) :
    gz ⬝ᵥ (A.adjugate *ᵥ gz)
      = gz ⬝ᵥ ((A + tx • atomMatrix gx + tz • atomMatrix gz).adjugate *ᵥ gz)
        - tx * (crossProduct gz gx
            ⬝ᵥ ((A + tx • atomMatrix gx + tz • atomMatrix gz)
              *ᵥ crossProduct gz gx)) := by
  simp only [Matrix.adjugate_fin_three, atomMatrix, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, cross_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  ring

/-! ## 2. The corner consequence -/

/-- The coweighted member sum is positive semidefinite. -/
theorem coweighted_member_sum_posSemidef (D : WeightedDesign m 3)
    (F : Finset (Fin m)) :
    (∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)).PosSemidef := by
  classical
  refine Matrix.posSemidef_sum F fun a _ => ?_
  have hle : D.weight a ≤ 1 := by
    rw [← D.weight_sum_one]
    exact Finset.single_le_sum (fun c _ => (D.weight_pos c).le)
      (Finset.mem_univ a)
  exact (posSemidef_atomMatrix (D.atom a)).smul (by linarith)

/-- **THE EXCLUDED READING IS WEDGE-DOMINATED.**  At a subset with two
excluded atoms and a positive definite gap, the excluded reading plus a
nonnegative cross energy is the second-compound reading of the coweighted
member sum:

  `det A·r_z + t_x·(g_z×g_x)ᵀC(g_z×g_x) = g_zᵀ·adj(C)·g_z` ,

so in particular `det A·r_z ≤ g_zᵀ·adj(C)·g_z`. -/
theorem corner_excluded_reading_wedge_dominated (D : WeightedDesign m 3)
    (F : Finset (Fin m)) {x z : Fin m} (hxz : x ≠ z)
    (hcompl : (Fᶜ : Finset (Fin m)) = {x, z})
    (hpd : (subsetSum D F - 1).PosDef) :
    (subsetSum D F - 1).det
        * (D.atom z ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom z))
      ≤ D.atom z ⬝ᵥ
          ((∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)).adjugate
            *ᵥ D.atom z) := by
  classical
  have hsum : ∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)
      = (subsetSum D F - 1) + D.weight x • atomMatrix (D.atom x)
        + D.weight z • atomMatrix (D.atom z) := by
    have h := coweighted_member_sum_eq D F
    rw [hcompl] at h
    have hxs : x ∉ ({z} : Finset (Fin m)) := by simp [hxz]
    rw [Finset.sum_insert hxs, Finset.sum_singleton] at h
    rw [h]
    abel
  have hprobe := adj_probe_two_excluded (subsetSum D F - 1)
    (D.atom x) (D.atom z) (D.weight x) (D.weight z)
  rw [← hsum] at hprobe
  rw [← adjugate_reading D F hpd (D.atom z), hprobe]
  have hcross : 0 ≤ D.weight x
      * (crossProduct (D.atom z) (D.atom x)
          ⬝ᵥ ((∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a))
            *ᵥ crossProduct (D.atom z) (D.atom x))) := by
    refine mul_nonneg (D.weight_pos x).le ?_
    have hpsd := coweighted_member_sum_posSemidef D F
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 _
  linarith

/-- The symmetric `x`-side form of the wedge domination. -/
theorem corner_excluded_reading_wedge_dominated_x (D : WeightedDesign m 3)
    (F : Finset (Fin m)) {x z : Fin m} (hxz : x ≠ z)
    (hcompl : (Fᶜ : Finset (Fin m)) = {x, z})
    (hpd : (subsetSum D F - 1).PosDef) :
    (subsetSum D F - 1).det
        * (D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom x))
      ≤ D.atom x ⬝ᵥ
          ((∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)).adjugate
            *ᵥ D.atom x) := by
  classical
  have hswap : ((Fᶜ : Finset (Fin m))) = {z, x} := by
    rw [hcompl]
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hsum : ∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)
      = (subsetSum D F - 1) + D.weight z • atomMatrix (D.atom z)
        + D.weight x • atomMatrix (D.atom x) := by
    have h := coweighted_member_sum_eq D F
    rw [hswap] at h
    have hzs : z ∉ ({x} : Finset (Fin m)) := by simp [Ne.symm hxz]
    rw [Finset.sum_insert hzs, Finset.sum_singleton] at h
    rw [h]
    abel
  have hprobe := adj_probe_two_excluded (subsetSum D F - 1)
    (D.atom z) (D.atom x) (D.weight z) (D.weight x)
  rw [← hsum] at hprobe
  rw [← adjugate_reading D F hpd (D.atom x), hprobe]
  have hcross : 0 ≤ D.weight z
      * (crossProduct (D.atom x) (D.atom z)
          ⬝ᵥ ((∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a))
            *ᵥ crossProduct (D.atom x) (D.atom z))) := by
    refine mul_nonneg (D.weight_pos z).le ?_
    have hpsd := coweighted_member_sum_posSemidef D F
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 _
  linarith

end Gtz
