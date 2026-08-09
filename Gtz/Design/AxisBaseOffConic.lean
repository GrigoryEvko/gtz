import Gtz.Design.FreePairPlane

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace Gtz

open Matrix

/-- Six atoms with the first three supported on the three coordinate axes and
the last three supplied by `freeAtom`.  This is the canonical coordinate shape
of the co-weighted base frame after whitening. -/
def axisBaseAtom (baseScale : Fin 3 → ℝ)
    (freeAtom : Fin 3 → Fin 3 → ℝ) : Fin 6 → Fin 3 → ℝ :=
  ![![baseScale 0, 0, 0], ![0, baseScale 1, 0], ![0, 0, baseScale 2],
    freeAtom 0, freeAtom 1, freeAtom 2]

/-- The three off-diagonal Veronese coordinates `(xy,xz,yz)` of each of the
three free atoms. -/
def freeOffDiagonalGrid (freeAtom : Fin 3 → Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![freeAtom 0 0 * freeAtom 0 1,
      freeAtom 0 0 * freeAtom 0 2,
      freeAtom 0 1 * freeAtom 0 2;
    freeAtom 1 0 * freeAtom 1 1,
      freeAtom 1 0 * freeAtom 1 2,
      freeAtom 1 1 * freeAtom 1 2;
    freeAtom 2 0 * freeAtom 2 1,
      freeAtom 2 0 * freeAtom 2 2,
      freeAtom 2 1 * freeAtom 2 2]

/-- A symmetric conic with zero diagonal, parametrized by its three doubled
off-diagonal coefficients. -/
def offDiagonalConic (coefficient : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, coefficient 0, coefficient 1;
    coefficient 0, 0, coefficient 2;
    coefficient 1, coefficient 2, 0]

theorem offDiagonalConic_isHermitian (coefficient : Fin 3 → ℝ) :
    (offDiagonalConic coefficient)ᵀ = offDiagonalConic coefficient := by
  ext row col
  fin_cases row <;> fin_cases col <;> rfl

/-- Evaluation of the zero-diagonal conic is the dot product with the three
off-diagonal Veronese coordinates. -/
theorem dotProduct_offDiagonalConic_mulVec (coefficient vector : Fin 3 → ℝ) :
    vector ⬝ᵥ (offDiagonalConic coefficient *ᵥ vector)
      = 2 * (coefficient 0 * (vector 0 * vector 1)
        + coefficient 1 * (vector 0 * vector 2)
        + coefficient 2 * (vector 1 * vector 2)) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, offDiagonalConic]
  ring

theorem offDiagonalConic_ne_zero {coefficient : Fin 3 → ℝ}
    (hne : coefficient ≠ 0) : offDiagonalConic coefficient ≠ 0 := by
  intro hzero
  apply hne
  funext index
  fin_cases index
  · have hentry := congrFun (congrFun hzero 0) 1
    simpa [offDiagonalConic] using hentry
  · have hentry := congrFun (congrFun hzero 0) 2
    simpa [offDiagonalConic] using hentry
  · have hentry := congrFun (congrFun hzero 1) 2
    simpa [offDiagonalConic] using hentry

/-- **The off-conic condition in axis-base coordinates.**  If the three base
atoms lie on the coordinate axes, off-conicity forces the three free atoms'
off-diagonal Veronese rows to be independent.  Thus the plane branch's `6×6`
Veronese nondegeneracy reduces to one `3×3` determinant after normalization. -/
theorem freeOffDiagonalGrid_det_ne_zero_of_hasNoCommonQuadric
    (baseScale : Fin 3 → ℝ) (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hoffConic : HasNoCommonQuadric (axisBaseAtom baseScale freeAtom)) :
    (freeOffDiagonalGrid freeAtom).det ≠ 0 := by
  intro hdet
  obtain ⟨coefficient, hcoefficientNe, hkernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hquadric : ∀ atomIndex,
      axisBaseAtom baseScale freeAtom atomIndex ⬝ᵥ
        (offDiagonalConic coefficient *ᵥ axisBaseAtom baseScale freeAtom atomIndex) = 0 := by
    intro atomIndex
    fin_cases atomIndex
    · rw [dotProduct_offDiagonalConic_mulVec]
      simp [axisBaseAtom]
    · rw [dotProduct_offDiagonalConic_mulVec]
      simp [axisBaseAtom]
    · rw [dotProduct_offDiagonalConic_mulVec]
      simp [axisBaseAtom]
    · change freeAtom 0 ⬝ᵥ (offDiagonalConic coefficient *ᵥ freeAtom 0) = 0
      rw [dotProduct_offDiagonalConic_mulVec]
      have hrow := congrFun hkernel 0
      simp [freeOffDiagonalGrid, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hrow
      nlinarith
    · change freeAtom 1 ⬝ᵥ (offDiagonalConic coefficient *ᵥ freeAtom 1) = 0
      rw [dotProduct_offDiagonalConic_mulVec]
      have hrow := congrFun hkernel 1
      simp [freeOffDiagonalGrid, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hrow
      nlinarith
    · change freeAtom 2 ⬝ᵥ (offDiagonalConic coefficient *ᵥ freeAtom 2) = 0
      rw [dotProduct_offDiagonalConic_mulVec]
      have hrow := congrFun hkernel 2
      simp [freeOffDiagonalGrid, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hrow
      nlinarith
  exact offDiagonalConic_ne_zero hcoefficientNe
    (hoffConic (offDiagonalConic coefficient)
      (offDiagonalConic_isHermitian coefficient) hquadric)

/-- With nonzero axis atoms the preceding implication is an equivalence.  The
three axis equations kill a common conic's diagonal entries; the free equations
then say its off-diagonal coefficient vector lies in `freeOffDiagonalGrid`'s
kernel. -/
theorem hasNoCommonQuadric_axisBaseAtom_iff_freeOffDiagonalGrid_det_ne_zero
    (baseScale : Fin 3 → ℝ) (freeAtom : Fin 3 → Fin 3 → ℝ)
    (hbaseScale : ∀ index, baseScale index ≠ 0) :
    HasNoCommonQuadric (axisBaseAtom baseScale freeAtom)
      ↔ (freeOffDiagonalGrid freeAtom).det ≠ 0 := by
  constructor
  · exact freeOffDiagonalGrid_det_ne_zero_of_hasNoCommonQuadric baseScale freeAtom
  · intro hdet form hsym hquadric
    have hzeroZero : form 0 0 = 0 := by
      have hvalue := hquadric 0
      simp [axisBaseAtom, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
      rcases hvalue with hscale | hentry | hscale
      · exact (hbaseScale 0 hscale).elim
      · exact hentry
      · exact (hbaseScale 0 hscale).elim
    have honeOne : form 1 1 = 0 := by
      have hvalue := hquadric 1
      simp [axisBaseAtom, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
      rcases hvalue with hscale | hentry | hscale
      · exact (hbaseScale 1 hscale).elim
      · exact hentry
      · exact (hbaseScale 1 hscale).elim
    have htwoTwo : form 2 2 = 0 := by
      have hvalue := hquadric 2
      simp [axisBaseAtom, dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
      rcases hvalue with hscale | hentry | hscale
      · exact (hbaseScale 2 hscale).elim
      · exact hentry
      · exact (hbaseScale 2 hscale).elim
    have honeZero : form 1 0 = form 0 1 := by
      have hentry := congrFun (congrFun hsym 0) 1
      simpa [Matrix.transpose_apply] using hentry
    have htwoZero : form 2 0 = form 0 2 := by
      have hentry := congrFun (congrFun hsym 0) 2
      simpa [Matrix.transpose_apply] using hentry
    have htwoOne : form 2 1 = form 1 2 := by
      have hentry := congrFun (congrFun hsym 1) 2
      simpa [Matrix.transpose_apply] using hentry
    let coefficient : Fin 3 → ℝ := ![form 0 1, form 0 2, form 1 2]
    have hkernel : freeOffDiagonalGrid freeAtom *ᵥ coefficient = 0 := by
      funext row
      fin_cases row
      · have hvalue := hquadric 3
        change freeAtom 0 ⬝ᵥ (form *ᵥ freeAtom 0) = 0 at hvalue
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
        rw [hzeroZero, honeOne, htwoTwo, honeZero, htwoZero, htwoOne] at hvalue
        simp [freeOffDiagonalGrid, coefficient, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
        nlinarith
      · have hvalue := hquadric 4
        change freeAtom 1 ⬝ᵥ (form *ᵥ freeAtom 1) = 0 at hvalue
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
        rw [hzeroZero, honeOne, htwoTwo, honeZero, htwoZero, htwoOne] at hvalue
        simp [freeOffDiagonalGrid, coefficient, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
        nlinarith
      · have hvalue := hquadric 5
        change freeAtom 2 ⬝ᵥ (form *ᵥ freeAtom 2) = 0 at hvalue
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
        rw [hzeroZero, honeOne, htwoTwo, honeZero, htwoZero, htwoOne] at hvalue
        simp [freeOffDiagonalGrid, coefficient, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
        nlinarith
    have hcoefficient : coefficient = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero hdet hkernel
    have hzeroOne : form 0 1 = 0 := by
      have hentry := congrFun hcoefficient 0
      simpa [coefficient] using hentry
    have hzeroTwo : form 0 2 = 0 := by
      have hentry := congrFun hcoefficient 1
      simpa [coefficient] using hentry
    have honeTwo : form 1 2 = 0 := by
      have hentry := congrFun hcoefficient 2
      simpa [coefficient] using hentry
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp_all [Matrix.zero_apply]

end Gtz
