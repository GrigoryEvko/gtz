import Gtz.Wave.PrivateAtomGramLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The capture form and the private diagonal reading

The captured assembly has its own H-form: `B (M H) Bᵀ = P Ξ`, because the
representation law moves the chart across the basis columns.  At a private
atom every conjugated form reads through the single surviving basis
coordinate: the ambient diagonal is the squared coordinate times the
coefficient diagonal.  With the Gram form this pins `Ξ` at the atom, and
with the capture form it pins `P Ξ` at the atom.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.capture_Hform` — **THE CAPTURE FORM.**  `B (M H) Bᵀ = P Ξ`.
* `Gtz.conjugated_diagonal_eq_of_private_atom` — the private diagonal
  reading of every conjugated form.

## Vacuity

Nothing here quantifies over a crux.  The statements are matrix algebra at
every datum with a chosen basis.
-/

namespace Gtz

open Matrix

variable {size : ℕ} {activeIndex : Type*}
variable {activeSet : Finset activeIndex}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE CAPTURE FORM.**  The captured assembly is the conjugated capture:
`B (M H) Bᵀ = P Ξ`. -/
theorem capture_Hform
    (basisLabel : Fin basisCount → activeIndex)
    {projection : Matrix (Fin size) (Fin size) ℝ}
    {M H : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (hHform : tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir) :
    tightBasisColumns tightDir basisLabel * (M * H)
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = projection * chartMultiplierAssembly activeSet activeWeight tightDir := by
  calc tightBasisColumns tightDir basisLabel * (M * H)
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = tightBasisColumns tightDir basisLabel * M * H
          * (tightBasisColumns tightDir basisLabel)ᵀ := by
        rw [Matrix.mul_assoc (tightBasisColumns tightDir basisLabel) M H]
    _ = projection * tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ := by
        rw [hrepresentation]
    _ = projection * (tightBasisColumns tightDir basisLabel * H
          * (tightBasisColumns tightDir basisLabel)ᵀ) := by
        rw [Matrix.mul_assoc projection (tightBasisColumns tightDir basisLabel) H,
          Matrix.mul_assoc projection
            (tightBasisColumns tightDir basisLabel * H)
            (tightBasisColumns tightDir basisLabel)ᵀ]
    _ = projection * chartMultiplierAssembly activeSet activeWeight tightDir := by
        rw [hHform]

/-- The private diagonal reading: at a private atom every conjugated form
reads through the single surviving basis coordinate. -/
theorem conjugated_diagonal_eq_of_private_atom
    (basisLabel : Fin basisCount → activeIndex)
    {K : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    {X : Matrix (Fin size) (Fin size) ℝ}
    (hform : tightBasisColumns tightDir basisLabel * K
        * (tightBasisColumns tightDir basisLabel)ᵀ = X)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0) :
    X privateAtom privateAtom
      = tightDir (basisLabel privateSlot) privateAtom
        * tightDir (basisLabel privateSlot) privateAtom
        * K privateSlot privateSlot := by
  rw [← hform, Matrix.mul_apply]
  rw [Finset.sum_eq_single privateSlot
    (fun columnIndex _ hne => by
      have hzero : (tightBasisColumns tightDir basisLabel)ᵀ columnIndex privateAtom
          = 0 := by
        rw [Matrix.transpose_apply]
        exact hprivate columnIndex hne
      rw [hzero, mul_zero])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single privateSlot
    (fun columnIndex _ hne => by
      have hzero : tightBasisColumns tightDir basisLabel privateAtom columnIndex = 0 :=
        hprivate columnIndex hne
      rw [hzero, zero_mul])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  have hentry : tightBasisColumns tightDir basisLabel privateAtom privateSlot
      = tightDir (basisLabel privateSlot) privateAtom := rfl
  have htranspose : (tightBasisColumns tightDir basisLabel)ᵀ privateSlot privateAtom
      = tightDir (basisLabel privateSlot) privateAtom := rfl
  rw [hentry, htranspose]
  ring

end Gtz
