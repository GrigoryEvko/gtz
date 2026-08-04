import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Cholesky path-transfer for the connectedness route (phase-6 whitening lane)

`Gtz.ParallelFreeReachesAnchor` -- the ONE open hypothesis of the landed
connectedness route (`Gtz/Reduction/ConnectednessRoute.lean`) -- asks for a
continuous path of atom families passing through parallel-free designs.  The
free-tuple lane (T1) produces a continuous path of spanning six-tuples with no
Parseval constraint; this file is T2, the transfer: pointwise closed-form 3x3
Cholesky whitening turns a spanning path whose endpoint Gram matrices are the
identity into a path of EXACT Parseval tuples, and each time-slice moves by one
invertible matrix, so parallelism patterns transport.

No spectral theory is used anywhere.  `Matrix.PosSemidef.sqrt` does not resolve
at this pin and none of it is needed: the three Cholesky pivots are extracted
from `Matrix.PosDef` by three explicit test vectors (the third replaces
`PosDef.det_pos`, which this pin's `PosDef` file does not carry), and every
identity below is scalar algebra dispatched by `field_simp` and `ring`.

The three quadratic-form identities feeding the test vectors were verified
symbolically before formalization:
* `y = (m10, -m00, 0)`            gives  `yᵀMy = m00 * pivotTwo`;
* `x = (m10*m21 - m11*m20, m10*m20 - m00*m21, pivotTwo)`
                                  gives  `xᵀMx = pivotTwo * lowerDet`;
* the `(2,2)` Cholesky entry is
  `m20²·d₂ + (m00·m21 − m10·m20)² + m00·d₃ = m00·d₂·m22`.
-/

set_option autoImplicit false

namespace Gtz

open Matrix

noncomputable section

/-! ## The Gram matrix of a six-atom family -/

/-- The Gram matrix `Σ_c v_c v_cᵀ` of six atoms in `ℝ³`.  A `WeightedDesign`'s
Parseval condition says exactly `gramMatrix (fun c => √(w c) • atom c) = 1`. -/
def gramMatrix (v : Fin 6 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ c, Matrix.vecMulVec (v c) (v c)

lemma gramMatrix_apply (v : Fin 6 → Fin 3 → ℝ) (i j : Fin 3) :
    gramMatrix v i j = ∑ c, v c i * v c j := by
  simp [gramMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]

lemma gramMatrix_comm (v : Fin 6 → Fin 3 → ℝ) (i j : Fin 3) :
    gramMatrix v i j = gramMatrix v j i := by
  simp only [gramMatrix_apply]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-! ## The three Cholesky pivots, extracted from positive definiteness by
explicit test vectors -- no eigenvalues, no determinant API, no matrix root -/

/-- The second leading principal minor, written on the lower triangle. -/
def pivotTwo (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  M 0 0 * M 1 1 - M 1 0 * M 1 0

/-- The determinant, written on the lower triangle; for a symmetric matrix
this is the determinant, and only symmetric matrices reach it below. -/
def lowerDet (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  M 0 0 * (M 1 1 * M 2 2 - M 2 1 * M 2 1)
    - M 1 0 * (M 1 0 * M 2 2 - M 2 1 * M 2 0)
    + M 2 0 * (M 1 0 * M 2 1 - M 1 1 * M 2 0)

section Pivots

variable {M : Matrix (Fin 3) (Fin 3) ℝ}

/-- The `PosDef` quadratic form at a nonzero real vector, with the trivial
star removed. -/
lemma quadForm_pos (hM : M.PosDef) {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (M *ᵥ x) := by
  have h := hM.dotProduct_mulVec_pos hx
  rwa [star_trivial] at h

lemma entry00_pos (hM : M.PosDef) : 0 < M 0 0 := by
  have hx : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hcontra
    have h0 : (1 : ℝ) = 0 := congrFun hcontra 0
    exact one_ne_zero h0
  have h := quadForm_pos hM hx
  have hval : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ (M *ᵥ ![1, 0, 0]) = M 0 0 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  rwa [hval] at h

lemma pivotTwo_pos (hM : M.PosDef) (h01 : M 0 1 = M 1 0) : 0 < pivotTwo M := by
  have hp1 := entry00_pos hM
  have hx : (![M 1 0, -(M 0 0), 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hcontra
    have h1 : -(M 0 0) = 0 := congrFun hcontra 1
    exact hp1.ne' (neg_eq_zero.mp h1)
  have h := quadForm_pos hM hx
  have hval : (![M 1 0, -(M 0 0), 0] : Fin 3 → ℝ)
      ⬝ᵥ (M *ᵥ ![M 1 0, -(M 0 0), 0]) = M 0 0 * pivotTwo M := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, pivotTwo, h01]
    ring
  rw [hval] at h
  by_contra hcon
  nlinarith [h, mul_nonneg hp1.le (neg_nonneg.mpr (not_lt.mp hcon))]

/-- Positivity of the third pivot WITHOUT any determinant API: the bordered
test vector `(m10·m21 − m11·m20, m10·m20 − m00·m21, pivotTwo)` has quadratic
form exactly `pivotTwo * lowerDet`. -/
lemma lowerDet_pos (hM : M.PosDef) (h01 : M 0 1 = M 1 0) (h02 : M 0 2 = M 2 0)
    (h12 : M 1 2 = M 2 1) : 0 < lowerDet M := by
  have hp2 := pivotTwo_pos hM h01
  have hx : (![M 1 0 * M 2 1 - M 1 1 * M 2 0, M 1 0 * M 2 0 - M 0 0 * M 2 1,
      pivotTwo M] : Fin 3 → ℝ) ≠ 0 := by
    intro hcontra
    have h2 : pivotTwo M = 0 := congrFun hcontra 2
    exact hp2.ne' h2
  have h := quadForm_pos hM hx
  have hval : (![M 1 0 * M 2 1 - M 1 1 * M 2 0, M 1 0 * M 2 0 - M 0 0 * M 2 1,
      pivotTwo M] : Fin 3 → ℝ)
      ⬝ᵥ (M *ᵥ ![M 1 0 * M 2 1 - M 1 1 * M 2 0, M 1 0 * M 2 0 - M 0 0 * M 2 1,
        pivotTwo M]) = pivotTwo M * lowerDet M := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, pivotTwo, lowerDet,
      h01, h02, h12]
    ring
  rw [hval] at h
  by_contra hcon
  nlinarith [h, mul_nonneg hp2.le (neg_nonneg.mpr (not_lt.mp hcon))]

end Pivots

/-! ## The Cholesky factor and its closed-form inverse -/

/-- First Cholesky diagonal, `√(M 0 0)`. -/
def sqrtOne (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.sqrt (M 0 0)

/-- Second Cholesky diagonal, `√(pivotTwo/M00)`. -/
def sqrtTwo (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.sqrt (pivotTwo M / M 0 0)

/-- Third Cholesky diagonal, `√(lowerDet/pivotTwo)`. -/
def sqrtThree (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sqrt (lowerDet M / pivotTwo M)

/-- The `(1,0)` Cholesky entry. -/
def offTen (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := M 1 0 / sqrtOne M

/-- The `(2,0)` Cholesky entry. -/
def offTwenty (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := M 2 0 / sqrtOne M

/-- The `(2,1)` Cholesky entry. -/
def offTwentyOne (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (M 2 1 - M 2 0 * M 1 0 / M 0 0) / sqrtTwo M

/-- The lower-triangular Cholesky factor of a symmetric positive-definite
3x3 matrix, entrywise. -/
def cholOf (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sqrtOne M, 0, 0;
     offTen M, sqrtTwo M, 0;
     offTwenty M, offTwentyOne M, sqrtThree M]

/-- The closed-form inverse of the Cholesky factor: the whitening matrix. -/
def whitenMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(sqrtOne M)⁻¹, 0, 0;
     -(offTen M / (sqrtOne M * sqrtTwo M)), (sqrtTwo M)⁻¹, 0;
     (offTen M * offTwentyOne M - sqrtTwo M * offTwenty M)
         / (sqrtOne M * sqrtTwo M * sqrtThree M),
       -(offTwentyOne M / (sqrtTwo M * sqrtThree M)), (sqrtThree M)⁻¹]

section Factor

variable {M : Matrix (Fin 3) (Fin 3) ℝ}

lemma sqrtOne_pos (hM : M.PosDef) : 0 < sqrtOne M :=
  Real.sqrt_pos.mpr (entry00_pos hM)

lemma sqrtTwo_pos (hM : M.PosDef) (h01 : M 0 1 = M 1 0) : 0 < sqrtTwo M :=
  Real.sqrt_pos.mpr (div_pos (pivotTwo_pos hM h01) (entry00_pos hM))

lemma sqrtThree_pos (hM : M.PosDef) (h01 : M 0 1 = M 1 0) (h02 : M 0 2 = M 2 0)
    (h12 : M 1 2 = M 2 1) : 0 < sqrtThree M :=
  Real.sqrt_pos.mpr (div_pos (lowerDet_pos hM h01 h02 h12) (pivotTwo_pos hM h01))

/-- The abstract closed-form inverse of a lower-triangular 3x3 matrix with
nonzero diagonal: only the three diagonal nonvanishing facts are needed. -/
lemma lowerInv_mul_lower (a b c d e f : ℝ) (ha : a ≠ 0) (hc : c ≠ 0)
    (hf : f ≠ 0) :
    (!![a⁻¹, 0, 0;
       -(b / (a * c)), c⁻¹, 0;
       (b * e - c * d) / (a * c * f), -(e / (c * f)), f⁻¹] :
        Matrix (Fin 3) (Fin 3) ℝ) * !![a, 0, 0; b, c, 0; d, e, f] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;>
    ring

/-- The whitening matrix is a left inverse of the Cholesky factor. -/
lemma whitenMatrix_mul_cholOf (hM : M.PosDef) (h01 : M 0 1 = M 1 0)
    (h02 : M 0 2 = M 2 0) (h12 : M 1 2 = M 2 1) :
    whitenMatrix M * cholOf M = 1 := by
  unfold whitenMatrix cholOf
  exact lowerInv_mul_lower _ _ _ _ _ _ (sqrtOne_pos hM).ne'
    (sqrtTwo_pos hM h01).ne' (sqrtThree_pos hM h01 h02 h12).ne'

/-- **The Cholesky identity**: `L Lᵀ = M` for symmetric positive-definite `M`. -/
lemma cholOf_mul_transpose (hM : M.PosDef) (h01 : M 0 1 = M 1 0)
    (h02 : M 0 2 = M 2 0) (h12 : M 1 2 = M 2 1) :
    cholOf M * (cholOf M)ᵀ = M := by
  have hp1 := entry00_pos hM
  have hp2 := pivotTwo_pos hM h01
  have hp3 := lowerDet_pos hM h01 h02 h12
  have h1ne : sqrtOne M ≠ 0 := (sqrtOne_pos hM).ne'
  have h2ne : sqrtTwo M ≠ 0 := (sqrtTwo_pos hM h01).ne'
  have h00ne : M 0 0 ≠ 0 := hp1.ne'
  have hp2ne : M 0 0 * M 1 1 - M 1 0 * M 1 0 ≠ 0 := by
    have := hp2.ne'
    simpa [pivotTwo] using this
  have hp2sq : M 0 0 * M 1 1 - M 1 0 ^ 2 ≠ 0 := by
    rw [sq]
    exact hp2ne
  have hs1 : sqrtOne M * sqrtOne M = M 0 0 := Real.mul_self_sqrt hp1.le
  have hs2 : sqrtTwo M * sqrtTwo M = pivotTwo M / M 0 0 :=
    Real.mul_self_sqrt (div_pos hp2 hp1).le
  have hs3 : sqrtThree M * sqrtThree M = lowerDet M / pivotTwo M :=
    Real.mul_self_sqrt (div_pos hp3 hp2).le
  have hbmul : offTen M * sqrtOne M = M 1 0 := by
    simp only [offTen]
    exact div_mul_cancel₀ _ h1ne
  have hdmul : offTwenty M * sqrtOne M = M 2 0 := by
    simp only [offTwenty]
    exact div_mul_cancel₀ _ h1ne
  have hemul : offTwentyOne M * sqrtTwo M = M 2 1 - M 2 0 * M 1 0 / M 0 0 := by
    simp only [offTwentyOne]
    exact div_mul_cancel₀ _ h2ne
  ext i j
  fin_cases i <;> fin_cases j
  · show (cholOf M * (cholOf M)ᵀ) 0 0 = M 0 0
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    exact hs1
  · show (cholOf M * (cholOf M)ᵀ) 0 1 = M 0 1
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [h01, ← hbmul]
    ring
  · show (cholOf M * (cholOf M)ᵀ) 0 2 = M 0 2
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [h02, ← hdmul]
    ring
  · show (cholOf M * (cholOf M)ᵀ) 1 0 = M 1 0
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [← hbmul]
  · show (cholOf M * (cholOf M)ᵀ) 1 1 = M 1 1
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [hs2]
    simp only [offTen]
    rw [div_mul_div_comm, hs1, pivotTwo]
    field_simp
    ring
  · show (cholOf M * (cholOf M)ᵀ) 1 2 = M 1 2
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [h12, mul_comm (sqrtTwo M) (offTwentyOne M), hemul]
    simp only [offTen, offTwenty]
    rw [div_mul_div_comm, hs1]
    field_simp
    ring
  · show (cholOf M * (cholOf M)ᵀ) 2 0 = M 2 0
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [← hdmul]
  · show (cholOf M * (cholOf M)ᵀ) 2 1 = M 2 1
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [hemul]
    simp only [offTwenty, offTen]
    rw [div_mul_div_comm, hs1]
    field_simp
    ring
  · show (cholOf M * (cholOf M)ᵀ) 2 2 = M 2 2
    simp [cholOf, Matrix.mul_apply, Fin.sum_univ_three]
    rw [hs3]
    simp only [offTwenty, offTwentyOne]
    rw [div_mul_div_comm, div_mul_div_comm, hs1, hs2]
    rw [pivotTwo, lowerDet]
    field_simp [h00ne, hp2ne, hp2sq]
    ring

/-- The whitening matrix has nonzero determinant, from the left-inverse
identity alone -- no determinant computation. -/
lemma whitenMatrix_det_ne_zero (hM : M.PosDef) (h01 : M 0 1 = M 1 0)
    (h02 : M 0 2 = M 2 0) (h12 : M 1 2 = M 2 1) :
    (whitenMatrix M).det ≠ 0 := by
  have hAL := whitenMatrix_mul_cholOf hM h01 h02 h12
  have hdet : (whitenMatrix M).det * (cholOf M).det = 1 := by
    rw [← Matrix.det_mul, hAL, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one hdet

end Factor

/-! ## The Gram matrix transforms by congruence -/

lemma vecMulVec_mulVec_left (B : Matrix (Fin 3) (Fin 3) ℝ) (y : Fin 3 → ℝ) :
    Matrix.vecMulVec (B *ᵥ y) (B *ᵥ y) = B * Matrix.vecMulVec y y * Bᵀ := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma gramMatrix_mulVec (B : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 6 → Fin 3 → ℝ) :
    gramMatrix (fun c => B *ᵥ w c) = B * gramMatrix w * Bᵀ := by
  unfold gramMatrix
  calc (∑ c, Matrix.vecMulVec (B *ᵥ w c) (B *ᵥ w c))
      = ∑ c, B * Matrix.vecMulVec (w c) (w c) * Bᵀ :=
        Finset.sum_congr rfl fun c _ => vecMulVec_mulVec_left B (w c)
    _ = (∑ c, B * Matrix.vecMulVec (w c) (w c)) * Bᵀ := by
        rw [← Finset.sum_mul]
    _ = B * (∑ c, Matrix.vecMulVec (w c) (w c)) * Bᵀ := by
        rw [← Finset.mul_sum]

/-- The sandwich collapse: a left inverse of a Cholesky factor whitens. -/
lemma sandwich_eq_one {A L M : Matrix (Fin 3) (Fin 3) ℝ}
    (hLL : L * Lᵀ = M) (hAL : A * L = 1) : A * M * Aᵀ = 1 := by
  have h2 : Lᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, hAL, Matrix.transpose_one]
  calc A * M * Aᵀ = A * (L * Lᵀ) * Aᵀ := by rw [hLL]
    _ = ((A * L) * Lᵀ) * Aᵀ := by rw [mul_assoc A L]
    _ = (A * L) * (Lᵀ * Aᵀ) := by rw [mul_assoc]
    _ = 1 := by rw [hAL, h2, one_mul]

/-- **Pointwise whitening**: applying the whitening matrix of a
positive-definite Gram matrix produces an exact Parseval family. -/
theorem gramMatrix_whiten_eq_one {v : Fin 6 → Fin 3 → ℝ}
    (hpd : (gramMatrix v).PosDef) :
    gramMatrix (fun c => whitenMatrix (gramMatrix v) *ᵥ v c) = 1 := by
  have h01 := gramMatrix_comm v 0 1
  have h02 := gramMatrix_comm v 0 2
  have h12 := gramMatrix_comm v 1 2
  rw [gramMatrix_mulVec]
  exact sandwich_eq_one (cholOf_mul_transpose hpd h01 h02 h12)
    (whitenMatrix_mul_cholOf hpd h01 h02 h12)

/-! ## The endpoint normalization: at `M = 1` the whitening is the identity -/

lemma pivotTwo_one : pivotTwo (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  simp [pivotTwo]

lemma lowerDet_one : lowerDet (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  simp [lowerDet]

lemma sqrtOne_one : sqrtOne (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  simp [sqrtOne]

lemma sqrtTwo_one : sqrtTwo (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  simp [sqrtTwo, pivotTwo_one]

lemma sqrtThree_one : sqrtThree (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  simp [sqrtThree, lowerDet_one, pivotTwo_one]

lemma offTen_one : offTen (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  simp [offTen]

lemma offTwenty_one : offTwenty (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  simp [offTwenty]

lemma offTwentyOne_one : offTwentyOne (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  simp [offTwentyOne]

lemma whitenMatrix_one : whitenMatrix (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [whitenMatrix, sqrtOne_one, sqrtTwo_one, sqrtThree_one, offTen_one,
      offTwenty_one, offTwentyOne_one]

/-! ## The whitened path and its continuity -/

/-- The whitened path: each time-slice of the free path is moved by the
whitening matrix of its own Gram matrix. -/
def whitenPath (v : ℝ → Fin 6 → Fin 3 → ℝ) : ℝ → Fin 6 → Fin 3 → ℝ :=
  fun t c => whitenMatrix (gramMatrix (v t)) *ᵥ v t c

section Continuity

variable {v : ℝ → Fin 6 → Fin 3 → ℝ}

lemma continuous_gram_entry (hcont : Continuous v) (i j : Fin 3) :
    Continuous fun t => gramMatrix (v t) i j := by
  simp only [gramMatrix_apply]
  refine continuous_finsetSum _ fun c _ => Continuous.mul ?_ ?_ <;>
    exact (continuous_apply _).comp ((continuous_apply _).comp hcont)

lemma continuous_pivotTwo_comp (hcont : Continuous v) :
    Continuous fun t => pivotTwo (gramMatrix (v t)) := by
  simp only [pivotTwo]
  exact ((continuous_gram_entry hcont 0 0).mul (continuous_gram_entry hcont 1 1)).sub
    ((continuous_gram_entry hcont 1 0).mul (continuous_gram_entry hcont 1 0))

lemma continuous_lowerDet_comp (hcont : Continuous v) :
    Continuous fun t => lowerDet (gramMatrix (v t)) := by
  simp only [lowerDet]
  exact (((continuous_gram_entry hcont 0 0).mul
      (((continuous_gram_entry hcont 1 1).mul (continuous_gram_entry hcont 2 2)).sub
        ((continuous_gram_entry hcont 2 1).mul (continuous_gram_entry hcont 2 1)))).sub
    ((continuous_gram_entry hcont 1 0).mul
      (((continuous_gram_entry hcont 1 0).mul (continuous_gram_entry hcont 2 2)).sub
        ((continuous_gram_entry hcont 2 1).mul (continuous_gram_entry hcont 2 0))))).add
    ((continuous_gram_entry hcont 2 0).mul
      (((continuous_gram_entry hcont 1 0).mul (continuous_gram_entry hcont 2 1)).sub
        ((continuous_gram_entry hcont 1 1).mul (continuous_gram_entry hcont 2 0))))

lemma continuous_sqrtOne_comp (hcont : Continuous v) :
    Continuous fun t => sqrtOne (gramMatrix (v t)) := by
  simp only [sqrtOne]
  exact Real.continuous_sqrt.comp (continuous_gram_entry hcont 0 0)

lemma continuous_sqrtTwo_comp (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef) :
    Continuous fun t => sqrtTwo (gramMatrix (v t)) := by
  simp only [sqrtTwo]
  exact Real.continuous_sqrt.comp ((continuous_pivotTwo_comp hcont).div
    (continuous_gram_entry hcont 0 0) fun t => (entry00_pos (hpd t)).ne')

lemma continuous_sqrtThree_comp (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef) :
    Continuous fun t => sqrtThree (gramMatrix (v t)) := by
  simp only [sqrtThree]
  exact Real.continuous_sqrt.comp ((continuous_lowerDet_comp hcont).div
    (continuous_pivotTwo_comp hcont)
    fun t => (pivotTwo_pos (hpd t) (gramMatrix_comm (v t) 0 1)).ne')

lemma continuous_offTen_comp (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef) :
    Continuous fun t => offTen (gramMatrix (v t)) := by
  simp only [offTen]
  exact (continuous_gram_entry hcont 1 0).div (continuous_sqrtOne_comp hcont)
    fun t => (sqrtOne_pos (hpd t)).ne'

lemma continuous_offTwenty_comp (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef) :
    Continuous fun t => offTwenty (gramMatrix (v t)) := by
  simp only [offTwenty]
  exact (continuous_gram_entry hcont 2 0).div (continuous_sqrtOne_comp hcont)
    fun t => (sqrtOne_pos (hpd t)).ne'

lemma continuous_offTwentyOne_comp (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef) :
    Continuous fun t => offTwentyOne (gramMatrix (v t)) := by
  simp only [offTwentyOne]
  exact ((continuous_gram_entry hcont 2 1).sub
      (((continuous_gram_entry hcont 2 0).mul (continuous_gram_entry hcont 1 0)).div
        (continuous_gram_entry hcont 0 0) fun t => (entry00_pos (hpd t)).ne')).div
    (continuous_sqrtTwo_comp hcont hpd)
    fun t => (sqrtTwo_pos (hpd t) (gramMatrix_comm (v t) 0 1)).ne'

lemma continuous_whiten_entry (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef) (i j : Fin 3) :
    Continuous fun t => whitenMatrix (gramMatrix (v t)) i j := by
  have hs1 := continuous_sqrtOne_comp (v := v) hcont
  have hs2 := continuous_sqrtTwo_comp (v := v) hcont hpd
  have hs3 := continuous_sqrtThree_comp (v := v) hcont hpd
  have hb := continuous_offTen_comp (v := v) hcont hpd
  have hd := continuous_offTwenty_comp (v := v) hcont hpd
  have he := continuous_offTwentyOne_comp (v := v) hcont hpd
  have hs1ne : ∀ t, sqrtOne (gramMatrix (v t)) ≠ 0 :=
    fun t => (sqrtOne_pos (hpd t)).ne'
  have hs2ne : ∀ t, sqrtTwo (gramMatrix (v t)) ≠ 0 :=
    fun t => (sqrtTwo_pos (hpd t) (gramMatrix_comm (v t) 0 1)).ne'
  have hs3ne : ∀ t, sqrtThree (gramMatrix (v t)) ≠ 0 :=
    fun t => (sqrtThree_pos (hpd t) (gramMatrix_comm (v t) 0 1)
      (gramMatrix_comm (v t) 0 2) (gramMatrix_comm (v t) 1 2)).ne'
  fin_cases i <;> fin_cases j
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 0 0
    exact (hs1.inv₀ hs1ne).congr fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 0 1
    exact (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)).congr
      fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 0 2
    exact (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)).congr
      fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 1 0
    exact ((hb.div (hs1.mul hs2) fun t => mul_ne_zero (hs1ne t) (hs2ne t)).neg).congr
      fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 1 1
    exact (hs2.inv₀ hs2ne).congr fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 1 2
    exact (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)).congr
      fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 2 0
    exact (((hb.mul he).sub (hs2.mul hd)).div ((hs1.mul hs2).mul hs3)
        fun t => mul_ne_zero (mul_ne_zero (hs1ne t) (hs2ne t)) (hs3ne t)).congr
      fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 2 1
    exact ((he.div (hs2.mul hs3) fun t => mul_ne_zero (hs2ne t) (hs3ne t)).neg).congr
      fun t => by simp [whitenMatrix]
  · show Continuous fun t => whitenMatrix (gramMatrix (v t)) 2 2
    exact (hs3.inv₀ hs3ne).congr fun t => by simp [whitenMatrix]

lemma continuous_whitenPath (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef) : Continuous (whitenPath v) := by
  refine continuous_pi fun c => continuous_pi fun i => ?_
  show Continuous fun t => ∑ j, whitenMatrix (gramMatrix (v t)) i j * v t c j
  refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
  · exact continuous_whiten_entry hcont hpd i j
  · exact (continuous_apply _).comp ((continuous_apply _).comp hcont)

end Continuity

/-! ## The capstone -/

/-- **The Cholesky path transfer.**  A continuous path of six-atom families in
`ℝ³` whose Gram matrix is everywhere positive definite and equals the identity
at both endpoints can be replaced by a continuous path of EXACT Parseval
families with the same endpoints, each time-slice of which differs from the
original by one invertible matrix (so parallelism patterns transport).  This is
step T2 of `Gtz.ParallelFreeReachesAnchor 6 3 icosaDesign`. -/
theorem exists_gramOne_path
    (v : ℝ → Fin 6 → Fin 3 → ℝ) (hcont : Continuous v)
    (hpd : ∀ t, (gramMatrix (v t)).PosDef)
    (hstart : gramMatrix (v 0) = 1) (hend : gramMatrix (v 1) = 1) :
    ∃ ρ : ℝ → Fin 6 → Fin 3 → ℝ, Continuous ρ ∧ ρ 0 = v 0 ∧ ρ 1 = v 1 ∧
      (∀ t, gramMatrix (ρ t) = 1) ∧
      (∀ t, ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.det ≠ 0 ∧
        ∀ c, ρ t c = A.mulVec (v t c)) := by
  refine ⟨whitenPath v, continuous_whitenPath hcont hpd, ?_, ?_, ?_, ?_⟩
  · funext c
    show whitenMatrix (gramMatrix (v 0)) *ᵥ v 0 c = v 0 c
    rw [hstart, whitenMatrix_one, Matrix.one_mulVec]
  · funext c
    show whitenMatrix (gramMatrix (v 1)) *ᵥ v 1 c = v 1 c
    rw [hend, whitenMatrix_one, Matrix.one_mulVec]
  · exact fun t => gramMatrix_whiten_eq_one (hpd t)
  · intro t
    exact ⟨whitenMatrix (gramMatrix (v t)),
      whitenMatrix_det_ne_zero (hpd t) (gramMatrix_comm (v t) 0 1)
        (gramMatrix_comm (v t) 0 2) (gramMatrix_comm (v t) 1 2),
      fun c => rfl⟩

/-! ## Non-vacuity: the hypotheses are jointly satisfiable -/

/-- The first three standard basis vectors of `ℝ³` padded with three zero
atoms: an exact Parseval six-tuple with rational entries. -/
def basisTuple : Fin 6 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]

lemma gramMatrix_basisTuple : gramMatrix basisTuple = 1 := by
  ext i j
  rw [gramMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [basisTuple, Fin.sum_univ_six]

lemma posDef_one_finThree : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.isHermitian_one,
    fun x hx => ?_⟩
  rw [star_trivial, Matrix.one_mulVec]
  show 0 < ∑ i, x i * x i
  obtain ⟨badCoord, hbad⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos' (fun i _ => mul_self_nonneg (x i))
    ⟨badCoord, Finset.mem_univ badCoord, ?_⟩
  exact mul_self_pos.mpr (by simpa using hbad)

/-- The transfer theorem is not vacuous: the constant path at `basisTuple`
satisfies every hypothesis. -/
theorem exists_gramOne_path_nonvacuous :
    ∃ ρ : ℝ → Fin 6 → Fin 3 → ℝ, Continuous ρ ∧
      ρ 0 = basisTuple ∧ ρ 1 = basisTuple ∧
      (∀ t, gramMatrix (ρ t) = 1) ∧
      (∀ t, ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.det ≠ 0 ∧
        ∀ c, ρ t c = A.mulVec (basisTuple c)) :=
  exists_gramOne_path (fun _ => basisTuple) continuous_const
    (fun _ => by rw [gramMatrix_basisTuple]; exact posDef_one_finThree)
    gramMatrix_basisTuple gramMatrix_basisTuple

end

end Gtz
