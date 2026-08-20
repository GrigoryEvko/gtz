import Gtz.Wave.FourSetTetrahedralFoil

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-!
# The adjugate readings of a rank-one downdate

The weight-gap determinant law reads the outside gap `K = S_{Cᶜ} − 1` through
three adjugate readings and two cross quadratic forms.  On the heavy-inside
cell `K` is the rank-one DOWNDATE `A_y − g_yg_yᵀ` of the surviving four-set
gap, and this module proves the three exact identities that transport every
`K`-quantity to `A_y`:

* `Gtz.adj_sub_atomMatrix_self_reading` — the self reading of the adjugate is
  INVARIANT under the downdate by the same vector:

    `gᵀ·adj(A − ggᵀ)·g = gᵀ·(adj A)·g` .

* `Gtz.det_mul_adj_sub_atomMatrix_reading` — the general reading transports
  with one determinant factor:

    `det A · vᵀadj(A−ggᵀ)v
       = (det A − gᵀ(adjA)g)·vᵀ(adjA)v + (vᵀ(adjA)g)·(gᵀ(adjA)v)` .

* `Gtz.cross_quadForm_sub_atomMatrix` — a cross product through `g`
  annihilates the downdate:

    `(x×g)ᵀ(A − ggᵀ)(x×g) = (x×g)ᵀA(x×g)` .

All three are polynomial identities of `3×3` matrices — no symmetry, no
invertibility, no positivity.

## What they give the heavy-inside cell

With `A = A_y`, `g = g_y` and the landed `adjugate_reading`, the three
adjugate terms of the weight-gap law become `A_y`-readings
(`Gtz.corner_oneAxisZero_heavyInside_KRy_eq` and companions):

  `g_yᵀ(adj K)g_y = r_y·det A_y` ,
  `g_zᵀ(adj K)g_z = det A_y·((1−r_y)·r_z + ρ²)` ,
  `(g_x×g_y)ᵀK(g_x×g_y) = (g_x×g_y)ᵀA_y(g_x×g_y)` ,

and the sign census of the cell follows: `g_yᵀ(adjK)g_y > 0` and
`(g_x×g_y)ᵀK(g_x×g_y) > 0` on ALL of cell H (measured at 100.0000% of eight
million samples before landing).  The excluded-pair adjugate terms carry the
mixed signs, exactly as measured.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The three transport identities -/

/-- **THE SELF READING IS DOWNDATE-INVARIANT.**
`gᵀ·adj(A − ggᵀ)·g = gᵀ·(adj A)·g` for every `3×3` matrix. -/
theorem adj_sub_atomMatrix_self_reading (A : Matrix (Fin 3) (Fin 3) ℝ)
    (g : Fin 3 → ℝ) :
    g ⬝ᵥ ((A - atomMatrix g).adjugate *ᵥ g) = g ⬝ᵥ (A.adjugate *ᵥ g) := by
  simp only [Matrix.adjugate_fin_three, atomMatrix, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE GENERAL READING TRANSPORT.**  One determinant factor moves any
adjugate reading across the downdate:

  `det A · vᵀadj(A−ggᵀ)v
     = (det A − gᵀ(adjA)g)·vᵀ(adjA)v + (vᵀ(adjA)g)·(gᵀ(adjA)v)` . -/
theorem det_mul_adj_sub_atomMatrix_reading (A : Matrix (Fin 3) (Fin 3) ℝ)
    (g v : Fin 3 → ℝ) :
    A.det * (v ⬝ᵥ ((A - atomMatrix g).adjugate *ᵥ v))
      = (A.det - g ⬝ᵥ (A.adjugate *ᵥ g)) * (v ⬝ᵥ (A.adjugate *ᵥ v))
        + (v ⬝ᵥ (A.adjugate *ᵥ g)) * (g ⬝ᵥ (A.adjugate *ᵥ v)) := by
  simp only [Matrix.det_fin_three, Matrix.adjugate_fin_three, atomMatrix,
    Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **THE CROSS ANNIHILATES THE DOWNDATE.**
`(x×g)ᵀ(A − ggᵀ)(x×g) = (x×g)ᵀA(x×g)` — the cross product through `g` never
sees the subtracted atom. -/
theorem cross_quadForm_sub_atomMatrix (A : Matrix (Fin 3) (Fin 3) ℝ)
    (x g : Fin 3 → ℝ) :
    crossProduct x g ⬝ᵥ ((A - atomMatrix g) *ᵥ crossProduct x g)
      = crossProduct x g ⬝ᵥ (A *ᵥ crossProduct x g) := by
  simp only [atomMatrix, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **LAGRANGE.**  `|x×g|² = |x|²·|g|² − (x·g)²`. -/
theorem cross_dotProduct_self (x g : Fin 3 → ℝ) :
    crossProduct x g ⬝ᵥ crossProduct x g
      = (x ⬝ᵥ x) * (g ⬝ᵥ g) - (x ⬝ᵥ g) ^ 2 := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

/-! ## 2. The outside gap is the downdated four-set gap -/

/-- The outside triple gap is the rank-one downdate of the four-set gap by
the inserted atom. -/
theorem outside_gap_eq_fourSet_downdate (D : WeightedDesign 6 3)
    (K : Finset (Fin 6)) {y : Fin 6} (hyK : y ∉ K) :
    subsetSum D K - 1
      = (subsetSum D (insert y K) - 1) - atomMatrix (D.atom y) := by
  rw [subsetSum_insert_sub_one D hyK]
  abel

/-! ## 3. The heavy-inside transports -/

/-- **THE Y-ADJUGATE TERM IS THE READING.**  On the surviving four-set of the
corner, the weight-gap law's inside adjugate term is the reading times the
determinant:

  `g_yᵀ·adj(S_{Cᶜ} − 1)·g_y = det A_y · r_y` . -/
theorem corner_oneAxisZero_heavyInside_KRy_eq (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    D.atom y ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).adjugate
        *ᵥ D.atom y)
      = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
        * (D.atom y ⬝ᵥ
            ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom y)) := by
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  rw [outside_gap_eq_fourSet_downdate D _ hyK,
    adj_sub_atomMatrix_self_reading,
    adjugate_reading D _ hAy (D.atom y)]

/-- **THE Z-ADJUGATE TERM IN READINGS.**  The excluded-side adjugate term of
the weight-gap law transports to the four-set readings:

  `g_zᵀ·adj(S_{Cᶜ} − 1)·g_z = det A_y·((1 − r_y)·r_z + ρ²)` . -/
theorem corner_oneAxisZero_heavyInside_KRz_eq (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    D.atom z ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).adjugate
        *ᵥ D.atom z)
      = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
        * ((1 - D.atom y ⬝ᵥ
              ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                *ᵥ D.atom y))
            * (D.atom z ⬝ᵥ
              ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                *ᵥ D.atom z))
          + (D.atom y ⬝ᵥ
              ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
                *ᵥ D.atom z)) ^ 2) := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1 with hA
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hdown : subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1
      = A - atomMatrix (D.atom y) := by
    rw [hA]; exact outside_gap_eq_fourSet_downdate D _ hyK
  have hne : A.det ≠ 0 := ne_of_gt hAy.det_pos
  have hkey := det_mul_adj_sub_atomMatrix_reading A (D.atom y) (D.atom z)
  rw [adjugate_reading D _ hAy (D.atom y), adjugate_reading D _ hAy (D.atom z),
    adjugate_cross_reading D _ hAy (D.atom z) (D.atom y),
    adjugate_cross_reading D _ hAy (D.atom y) (D.atom z), ← hA] at hkey
  rw [hdown]
  refine mul_left_cancel₀ hne ?_
  rw [hkey, inv_reading_symm hAy (D.atom z) (D.atom y)]
  ring

/-- **THE INSIDE CROSS TERM IS POSITIVE.**  The weight-gap law's inside cross
quadratic form is an `A_y`-form of a nonzero vector, hence strictly positive
on the cell:

  `(g_x×g_y)ᵀ(S_{Cᶜ}−1)(g_x×g_y) = (g_x×g_y)ᵀA_y(g_x×g_y) > 0` . -/
theorem corner_oneAxisZero_heavyInside_crossY_pos (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hay : D.atom y ⬝ᵥ u ≠ 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    0 < crossProduct (D.atom x) (D.atom y)
        ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1)
            *ᵥ crossProduct (D.atom x) (D.atom y)) := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  rw [outside_gap_eq_fourSet_downdate D _ hyK, cross_quadForm_sub_atomMatrix]
  have hxunit : D.atom x ⬝ᵥ D.atom x = 1 :=
    corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam.le hunit hgap
      (by simp) hax
  have hxy0 : D.atom x ⬝ᵥ D.atom y = 0 :=
    (corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam.le hunit hgap hax).1
  have hynz : D.atom y ≠ 0 := by
    intro hcon
    exact hay (by rw [hcon]; simp)
  have hyy : 0 < D.atom y ⬝ᵥ D.atom y := dotProduct_self_pos hynz
  have hcross : crossProduct (D.atom x) (D.atom y) ≠ 0 := by
    intro hcon
    have h0 : crossProduct (D.atom x) (D.atom y)
        ⬝ᵥ crossProduct (D.atom x) (D.atom y) = 0 := by
      rw [hcon]
      simp [dotProduct]
    rw [cross_dotProduct_self, hxunit, hxy0] at h0
    nlinarith [hyy]
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hAy).2 hcross
  simpa using hpos

end Gtz
