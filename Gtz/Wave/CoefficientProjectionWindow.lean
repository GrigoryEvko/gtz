import Gtz.Wave.PrivateAtomGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coefficient projection window and the Gram sum

Two laws of the coefficient coordinates.  The window: the capture `M * H`
and its complement `H - M * H` are positive semidefinite, because the
exchange law folds each into a conjugation of `H`.  The Gram sum: the
coefficient Gram `H` is the multiplier combination of the coefficient
atoms, because the left inverse conjugates the assembly sum termwise.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.leftInverse_atomMatrix_conjugation` — a conjugated atom is the atom
  of the read vector.
* `Gtz.coefficientGram_eq_sum_of_Hform` — **THE GRAM SUM.**
* `Gtz.coefficientCapture_posSemidef` — `M * H` is positive semidefinite.
* `Gtz.coefficientComplement_posSemidef` — `H - M * H` is positive
  semidefinite.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every
stationary datum with a chosen basis and left inverse, and the window laws
hold for every idempotent with the exchange law.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {activeSet : Finset activeIndex}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- A conjugated atom is the atom of the read vector:
`L (g gᵀ) Lᵀ = (L g) (L g)ᵀ`. -/
theorem leftInverse_atomMatrix_conjugation
    (L : Matrix (Fin basisCount) (Fin size) ℝ) (direction : Fin size → ℝ) :
    L * atomMatrix direction * Lᵀ = atomMatrix (L *ᵥ direction) := by
  ext rowIndex colIndex
  simp only [Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct]
  calc ∑ secondAtom, (∑ firstAtom, L rowIndex firstAtom
        * (direction firstAtom * direction secondAtom)) * L colIndex secondAtom
      = ∑ secondAtom, ∑ firstAtom, L rowIndex firstAtom
          * (direction firstAtom * direction secondAtom) * L colIndex secondAtom := by
        refine Finset.sum_congr rfl fun secondAtom _ => ?_
        rw [Finset.sum_mul]
    _ = (∑ firstAtom, L rowIndex firstAtom * direction firstAtom)
          * ∑ secondAtom, L colIndex secondAtom * direction secondAtom := by
        rw [Finset.sum_mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun secondAtom _ =>
          Finset.sum_congr rfl fun firstAtom _ => ?_
        ring

/-- **THE GRAM SUM.**  The coefficient Gram is the multiplier combination of
the coefficient atoms: the left inverse conjugates the assembly termwise. -/
theorem coefficientGram_eq_sum_of_Hform
    (basisLabel : Fin basisCount → activeIndex)
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir) :
    H = ∑ label ∈ activeSet,
        activeWeight label • atomMatrix (L *ᵥ tightDir label) := by
  have hH : H = L * chartMultiplierAssembly activeSet activeWeight tightDir * Lᵀ := by
    rw [← hHform, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hleft, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.transpose_mul, hleft, Matrix.transpose_one,
      Matrix.mul_one]
  rw [hH, chartMultiplierAssembly, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, leftInverse_atomMatrix_conjugation]

/-- The capture `M * H` is positive semidefinite: the exchange law folds it
into the conjugation `M H Mᵀ`. -/
theorem coefficientCapture_posSemidef
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hidempotent : M * M = M) (hpsd : H.PosSemidef) (hexchange : M * H = H * Mᵀ) :
    (M * H).PosSemidef := by
  have hfold : M * H * Mᵀ = M * H := by
    calc M * H * Mᵀ = M * (H * Mᵀ) := Matrix.mul_assoc M H Mᵀ
      _ = M * (M * H) := by rw [← hexchange]
      _ = M * M * H := (Matrix.mul_assoc M M H).symm
      _ = M * H := by rw [hidempotent]
  rw [← hfold]
  have hconjugated := hpsd.mul_mul_conjTranspose_same M
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hconjugated

/-- The complement `H - M * H` is positive semidefinite: the complement
idempotent `1 - M` obeys the same exchange law. -/
theorem coefficientComplement_posSemidef
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hidempotent : M * M = M) (hpsd : H.PosSemidef) (hexchange : M * H = H * Mᵀ) :
    (H - M * H).PosSemidef := by
  have hcompIdempotent : (1 - M) * (1 - M) = 1 - M := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hidempotent]
    abel
  have hcompExchange : (1 - M) * H = H * (1 - M)ᵀ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.mul_sub, Matrix.mul_one, hexchange]
  have hcapture := coefficientCapture_posSemidef hcompIdempotent hpsd hcompExchange
  rwa [Matrix.sub_mul, Matrix.one_mul] at hcapture

end Gtz
