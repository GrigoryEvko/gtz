import Gtz.Wave.PinnedSupportDispatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The capture tightness — the private atom aligns the captured Gram diagonal

At a private atom, the captured form `B (M H) Bᵀ = P Ξ` and the forced
diagonal `(P Ξ)_yy = (value + weight) / size` collapse to one coefficient
relation: `(M H)_ss = (value + weight) * H_ss`.  The capture window bounds
`(M H)_ss` between `0` and `H_ss`, thus the pin value sits inside `[0, 1]`
with EQUALITY structure: at the two boundary values the positive
semidefinite complement loses a full column.  The column law is the second
statement of this file.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.posSemidef_col_eq_zero_of_diag_eq_zero` — a positive semidefinite
  matrix with a zero diagonal entry has a zero column there.
* `Gtz.private_atom_capture_tight` — **THE CAPTURE TIGHTNESS.**
  `(M H)_ss = (value + weight) * H_ss` at each private atom.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every
stationary datum with a chosen basis, and the matrix law is unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- A positive semidefinite matrix with a zero diagonal entry has a zero
column there: the axis quadratic form vanishes, thus the axis image is
zero. -/
theorem posSemidef_col_eq_zero_of_diag_eq_zero
    {H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hpsd : H.PosSemidef) {slotIndex : Fin basisCount}
    (hdiag : H slotIndex slotIndex = 0) (rowIndex : Fin basisCount) :
    H rowIndex slotIndex = 0 := by
  classical
  have hstar : star (Pi.single slotIndex 1 : Fin basisCount → ℝ)
      = Pi.single slotIndex 1 := by
    ext otherIndex
    simp
  have hdot : Pi.single slotIndex (1 : ℝ) ⬝ᵥ (H *ᵥ Pi.single slotIndex 1)
      = H slotIndex slotIndex := by
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    simp [Matrix.col]
  have hzeroDot : star (Pi.single slotIndex 1 : Fin basisCount → ℝ)
      ⬝ᵥ (H *ᵥ Pi.single slotIndex 1) = 0 := by
    rw [hstar, hdot, hdiag]
  have hcolZero : H *ᵥ (Pi.single slotIndex 1 : Fin basisCount → ℝ) = 0 :=
    (hpsd.dotProduct_mulVec_zero_iff (Pi.single slotIndex 1)).mp hzeroDot
  have happly : (H *ᵥ (Pi.single slotIndex 1 : Fin basisCount → ℝ)) rowIndex
      = H rowIndex slotIndex := by
    rw [Matrix.mulVec_single_one]
    simp [Matrix.col]
  rw [hcolZero] at happly
  simpa using happly.symm

/-- **THE CAPTURE TIGHTNESS.**  At a private atom, the captured Gram
diagonal aligns with the pin: `(M H)_ss = (value + weight) * H_ss`.  The
capture form reads the ambient forced diagonal through the single
surviving coordinate, and the private square law cancels the coordinate. -/
theorem private_atom_capture_tight
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0) :
    (M * H) privateSlot privateSlot
      = (value + weight privateAtom) * H privateSlot privateSlot := by
  have hcapture := capture_Hform basisLabel hrepresentation hHform
  have hread := conjugated_diagonal_eq_of_private_atom basisLabel hcapture hprivate
  have hforced :=
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata privateAtom
  have hsquare :=
    private_atom_square_gram_eq_inv_size hdata basisLabel hHform hprivate
  have hqq : tightDir (basisLabel privateSlot) privateAtom
      * tightDir (basisLabel privateSlot) privateAtom ≠ 0 :=
    mul_ne_zero hslotNe hslotNe
  have hchain : tightDir (basisLabel privateSlot) privateAtom
        * tightDir (basisLabel privateSlot) privateAtom
        * (M * H) privateSlot privateSlot
      = tightDir (basisLabel privateSlot) privateAtom
        * tightDir (basisLabel privateSlot) privateAtom
        * ((value + weight privateAtom) * H privateSlot privateSlot) := by
    calc tightDir (basisLabel privateSlot) privateAtom
          * tightDir (basisLabel privateSlot) privateAtom
          * (M * H) privateSlot privateSlot
        = (projection * chartMultiplierAssembly activeSet activeWeight tightDir)
            privateAtom privateAtom := hread.symm
      _ = (value + weight privateAtom) * ((size : ℝ))⁻¹ := hforced
      _ = (value + weight privateAtom)
            * (tightDir (basisLabel privateSlot) privateAtom
              * tightDir (basisLabel privateSlot) privateAtom
              * H privateSlot privateSlot) := by rw [hsquare]
      _ = tightDir (basisLabel privateSlot) privateAtom
            * tightDir (basisLabel privateSlot) privateAtom
            * ((value + weight privateAtom) * H privateSlot privateSlot) := by
          ring
  exact mul_left_cancel₀ hqq hchain

end Gtz
