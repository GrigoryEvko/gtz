/-
# Reading a design in an adapted orthonormal frame

`Gtz.k2Frame_kill` closes the two-zero stratum for a design presented in the
normal frame.  Presenting an arbitrary design that way is a change of
orthonormal basis, and the only fact a change of basis needs is that the new
basis resolves the identity.

Three orthonormal vectors of `ℝ³` do resolve it, and the proof is one line of
matrix algebra rather than a rank argument: stack them as the rows of `M`, read
the six orthonormality conditions as `M Mᵀ = 1`, and use that a square matrix
with a right inverse has the same left inverse.  `Mᵀ M = 1` is exactly the
resolution (`Gtz.orthonormal_three_resolution`).

From it every inner product is the inner product of the coordinate vectors
(`Gtz.dotProduct_eq_frame_coords`), so every Gram-defined quantity — leverage,
pairing, wedge, bracket, gap determinant — may be computed in coordinates.  The
campaign's charts are all Gram-defined, so this is the transport they were
missing: `Gtz.tripleGram_eq_frame_coords` moves a whole triple's Gram, and
`Gtz.tripleGapDet_eq_frame_coords` moves its gap determinant.
-/
import Gtz.Wave.KTwoFrameKill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. Three orthonormal vectors resolve the identity -/

/-- **AN ORTHONORMAL TRIPLE OF `ℝ³` RESOLVES THE IDENTITY.**  Stack the three as
rows: orthonormality says the matrix times its transpose is one, and a square
matrix with a right inverse has that inverse on the left as well. -/
theorem orthonormal_three_resolution {u v w : Fin 3 → ℝ}
    (huu : u ⬝ᵥ u = 1) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0) :
    Matrix.vecMulVec u u + Matrix.vecMulVec v v + Matrix.vecMulVec w w = 1 := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  have hwu : w ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huw
  have hwv : w ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact hvw
  have hMMt : (Matrix.of ![u, v, w] : Matrix (Fin 3) (Fin 3) ℝ)
      * (Matrix.of ![u, v, w])ᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
        Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        Fin.sum_univ_three, dotProduct] at huu hvv hww huv huw hvw hvu hwu hwv ⊢ <;>
      norm_num <;>
      linarith [huu, hvv, hww, huv, huw, hvw, hvu, hwu, hwv]
  have hMtM : (Matrix.of ![u, v, w] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
      * (Matrix.of ![u, v, w]) = 1 := mul_eq_one_comm.mp hMMt
  ext i j
  have h := congrFun (congrFun hMtM i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.sum_univ_three] at h
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
  linarith [h]

/-- The nine entries of the resolution, as an indexed family. -/
theorem orthonormal_three_entry {u v w : Fin 3 → ℝ}
    (huu : u ⬝ᵥ u = 1) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0) (i j : Fin 3) :
    u i * u j + v i * v j + w i * w j = if i = j then 1 else 0 := by
  have hres := orthonormal_three_resolution huu hvv hww huv huw hvw
  have h := congrFun (congrFun hres i) j
  simpa only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply] using h

/-- A rank-one frame reads a probe on each side. -/
theorem dotProduct_vecMulVec_mulVec_pair (a p q b : Fin 3 → ℝ) :
    a ⬝ᵥ (Matrix.vecMulVec p q *ᵥ b) = (a ⬝ᵥ p) * (q ⬝ᵥ b) := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- **INNER PRODUCTS ARE COORDINATE INNER PRODUCTS.**  In an orthonormal frame
every pairing is the pairing of the two coordinate vectors. -/
theorem dotProduct_eq_frame_coords {u v w : Fin 3 → ℝ}
    (huu : u ⬝ᵥ u = 1) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0)
    (a b : Fin 3 → ℝ) :
    a ⬝ᵥ b = (a ⬝ᵥ u)*(b ⬝ᵥ u) + (a ⬝ᵥ v)*(b ⬝ᵥ v) + (a ⬝ᵥ w)*(b ⬝ᵥ w) := by
  have hres := orthonormal_three_resolution huu hvv hww huv huw hvw
  have h : a ⬝ᵥ ((Matrix.vecMulVec u u + Matrix.vecMulVec v v
        + Matrix.vecMulVec w w) *ᵥ b)
      = a ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ b) := by rw [hres]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    dotProduct_vecMulVec_mulVec_pair, dotProduct_vecMulVec_mulVec_pair,
    dotProduct_vecMulVec_mulVec_pair, Matrix.one_mulVec,
    dotProduct_comm u b, dotProduct_comm v b, dotProduct_comm w b] at h
  linarith [h]

/-! ## 2. The Gram of a triple in coordinates -/

/-- **THE GRAM OF A TRIPLE IS ITS COORDINATE GRAM.**  Every entry is a pairing,
and every pairing is a coordinate pairing. -/
theorem tripleGram_eq_frame_coords {u v w : Fin 3 → ℝ}
    (huu : u ⬝ᵥ u = 1) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0)
    (a b c : Fin 3 → ℝ) :
    tripleGram a b c
      = tripleGram ![a ⬝ᵥ u, a ⬝ᵥ v, a ⬝ᵥ w] ![b ⬝ᵥ u, b ⬝ᵥ v, b ⬝ᵥ w]
          ![c ⬝ᵥ u, c ⬝ᵥ v, c ⬝ᵥ w] := by
  have key : ∀ s t : Fin 3 → ℝ, s ⬝ᵥ t
      = ![s ⬝ᵥ u, s ⬝ᵥ v, s ⬝ᵥ w] ⬝ᵥ ![t ⬝ᵥ u, t ⬝ᵥ v, t ⬝ᵥ w] := by
    intro s t
    rw [dotProduct_eq_frame_coords huu hvv hww huv huw hvw s t]
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
  ext i j
  rw [tripleGram_apply, tripleGram_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.mk_zero, Fin.mk_one,
      Fin.isValue] <;>
    [ exact key a a; exact key a b; exact key a c;
      exact key b a; exact key b b; exact key b c;
      exact key c a; exact key c b; exact key c c ]

/-- **THE GAP DETERMINANT OF A TRIPLE IS ITS COORDINATE GAP DETERMINANT.**  The
gap determinant is a polynomial in the leverages and the three pairings, and
each of those is a coordinate quantity. -/
theorem tripleGapDet_eq_frame_coords {u v w : Fin 3 → ℝ}
    (huu : u ⬝ᵥ u = 1) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0)
    (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = tripleGapDet ![a ⬝ᵥ u, a ⬝ᵥ v, a ⬝ᵥ w] ![b ⬝ᵥ u, b ⬝ᵥ v, b ⬝ᵥ w]
          ![c ⬝ᵥ u, c ⬝ᵥ v, c ⬝ᵥ w] := by
  have key := dotProduct_eq_frame_coords huu hvv hww huv huw hvw
  have hlev : ∀ s : Fin 3 → ℝ, leverageOf s = s ⬝ᵥ s := by
    intro s; simp only [leverageOf, dotProduct, Fin.sum_univ_three]; ring
  unfold tripleGapDet
  simp only [hlev]
  rw [key a a, key a b, key a c, key b b, key b c, key c c]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

end Gtz
