import Gtz.Wave.CarriedRowReading

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The dense eigenpair trace — two independent eigenvectors read the trace

A two-by-two real matrix with two eigenvectors of nonzero cross
determinant has the two eigenvalues as its full spectrum: the trace is
their sum.  A shared support supplies the two eigenvectors: if all cross
determinants on the shared support vanish, the two basis columns are
proportional, against the left inverse.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.trace_eq_add_of_eigen_pair` — **THE TRACE READING.**
* `Gtz.exists_support_det_ne_zero` — **THE INDEPENDENT PAIR.**

## Vacuity

The statements are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE TRACE READING.**  Two eigenvectors with a nonzero cross
determinant exhaust the spectrum of a two-by-two matrix. -/
theorem trace_eq_add_of_eigen_pair
    {N : Matrix (Fin 2) (Fin 2) ℝ} {v w : Fin 2 → ℝ} {a b : ℝ}
    (hv : N *ᵥ v = a • v) (hw : N *ᵥ w = b • w)
    (hdet : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    Matrix.trace N = a + b := by
  classical
  have hv0 : N 0 0 * v 0 + N 0 1 * v 1 = a * v 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
  have hv1 : N 1 0 * v 0 + N 1 1 * v 1 = a * v 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
  have hw0 : N 0 0 * w 0 + N 0 1 * w 1 = b * w 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hw 0
  have hw1 : N 1 0 * w 0 + N 1 1 * w 1 = b * w 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hw 1
  have hconj : Matrix.of ![v, w] * Nᵀ
      = Matrix.diagonal ![a, b] * Matrix.of ![v, w] := by
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    fin_cases rowIndex <;> fin_cases colIndex
    · simp [Fin.sum_univ_two]
      linear_combination hv0
    · simp [Fin.sum_univ_two]
      linear_combination hv1
    · simp [Fin.sum_univ_two]
      linear_combination hw0
    · simp [Fin.sum_univ_two]
      linear_combination hw1
  have hker : ∀ coeffVec : Fin 2 → ℝ,
      Matrix.of ![v, w] *ᵥ coeffVec = 0 → coeffVec = 0 := by
    intro coeffVec hzero
    by_contra hne
    have hdetZero : (Matrix.of ![v, w] : Matrix (Fin 2) (Fin 2) ℝ).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨coeffVec, hne, hzero⟩
    rw [Matrix.det_fin_two] at hdetZero
    apply hdet
    simpa using hdetZero
  have htransfer := trace_eq_of_kernel_free_conjugation hconj hker
  rw [Matrix.trace_transpose, Matrix.trace_diagonal] at htransfer
  rw [htransfer]
  simp [Fin.sum_univ_two]

/-- **THE INDEPENDENT PAIR.**  Two basis columns with the same support
give two support atoms with a nonzero cross determinant: if all the cross
determinants vanish, the columns are proportional, against the left
inverse. -/
theorem exists_support_det_ne_zero
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    (hshared : datumTightSupport tightDir (basisLabel firstSlot)
      = datumTightSupport tightDir (basisLabel secondSlot))
    (hnonempty : (datumTightSupport tightDir (basisLabel firstSlot)).Nonempty) :
    ∃ firstAtom ∈ datumTightSupport tightDir (basisLabel firstSlot),
      ∃ secondAtom ∈ datumTightSupport tightDir (basisLabel firstSlot),
        tightDir (basisLabel firstSlot) firstAtom
              * tightDir (basisLabel secondSlot) secondAtom
            - tightDir (basisLabel firstSlot) secondAtom
              * tightDir (basisLabel secondSlot) firstAtom ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨baseAtom, hbaseMem⟩ := hnonempty
  have hbaseNe : tightDir (basisLabel firstSlot) baseAtom ≠ 0 :=
    mem_datumTightSupport.mp hbaseMem
  set ratio : ℝ := tightDir (basisLabel secondSlot) baseAtom
    / tightDir (basisLabel firstSlot) baseAtom with hratio
  have hdep : tightDir (basisLabel secondSlot)
      = ratio • tightDir (basisLabel firstSlot) := by
    funext atomIndex
    rw [Pi.smul_apply, smul_eq_mul, hratio]
    by_cases hmem : atomIndex ∈ datumTightSupport tightDir (basisLabel firstSlot)
    · have hminor := hall baseAtom hbaseMem atomIndex hmem
      rw [div_mul_eq_mul_div, eq_comm, div_eq_iff hbaseNe]
      linear_combination -hminor
    · have hfirstZero : tightDir (basisLabel firstSlot) atomIndex = 0 := by
        by_contra hnonzero
        exact hmem (mem_datumTightSupport.mpr hnonzero)
      have hsecondZero : tightDir (basisLabel secondSlot) atomIndex = 0 := by
        by_contra hnonzero
        exact hmem (hshared ▸ mem_datumTightSupport.mpr hnonzero)
      rw [hfirstZero, hsecondZero, mul_zero]
  have hcombo : tightBasisColumns tightDir basisLabel
      *ᵥ (Pi.single secondSlot 1 - ratio • Pi.single firstSlot 1) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul,
      tightBasisColumns_mulVec_single (tightDir := tightDir) basisLabel secondSlot,
      tightBasisColumns_mulVec_single (tightDir := tightDir) basisLabel firstSlot,
      hdep, sub_self]
  have hvanish : (Pi.single secondSlot 1 - ratio • Pi.single firstSlot 1
      : Fin basisCount → ℝ) = 0 := by
    have hchain : (Pi.single secondSlot 1 - ratio • Pi.single firstSlot 1
        : Fin basisCount → ℝ)
        = L *ᵥ (tightBasisColumns tightDir basisLabel
            *ᵥ (Pi.single secondSlot 1 - ratio • Pi.single firstSlot 1)) := by
      rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    rw [hchain, hcombo, Matrix.mulVec_zero]
  have hentry := congrFun hvanish secondSlot
  rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hne) 1, smul_zero, sub_zero, Pi.zero_apply] at hentry
  exact one_ne_zero hentry

end Gtz
