import Gtz.Wave.TwoCarrierDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The off-block column identity — the projected column of a full off-block slot

Fix a private slot whose FULL support is private: every atom of the slot's
support meets no other basis column.  Fix an other slot whose block covers,
together with the private support, all the atoms.  Then the projected
column of the other slot splits into two readable parts: the shifted-weight
multiple of the column itself, and the private column scaled by one
coefficient entry.  The left inverse then reads the diagonal coefficient of
the other slot from the shifted-weight vector alone.

This identity is the engine of the fully-private-block kill: with three
off-block slots the three diagonal readings sum against the trace budget.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.offblock_column_identity` — **THE COLUMN IDENTITY.**
* `Gtz.offblock_diagonal_reading` — **THE DIAGONAL READING.**

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every
stationary datum with a chosen basis.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE COLUMN IDENTITY.**  If the private slot's support meets no other
basis column, and the other slot's block covers all the atoms off that
support, then the projected column of the other slot is the shifted-weight
multiple of the column plus one coefficient multiple of the private
column. -/
theorem offblock_column_identity
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {privateSlot otherSlot : Fin basisCount} (hne : otherSlot ≠ privateSlot)
    (hmemOther : basisLabel otherSlot ∈ activeSet)
    (hprivateBlock : ∀ atomIndex : Fin size,
      tightDir (basisLabel privateSlot) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ privateSlot →
        tightDir (basisLabel columnIndex) atomIndex = 0)
    (hcoverPair : ∀ atomIndex : Fin size,
      atomIndex ∈ activeSubset (basisLabel otherSlot)
        ∨ tightDir (basisLabel privateSlot) atomIndex ≠ 0) :
    projection *ᵥ tightDir (basisLabel otherSlot)
      = (fun atomIndex => (value + weight atomIndex)
            * tightDir (basisLabel otherSlot) atomIndex)
        + M privateSlot otherSlot • tightDir (basisLabel privateSlot) := by
  classical
  funext atomIndex
  have hcolumn : (projection *ᵥ tightDir (basisLabel otherSlot)) atomIndex
      = (projection * tightBasisColumns tightDir basisLabel) atomIndex otherSlot := by
    rw [Matrix.mul_apply]
    rfl
  have hread : (projection *ᵥ tightDir (basisLabel otherSlot)) atomIndex
      = ∑ columnIndex, tightDir (basisLabel columnIndex) atomIndex
          * M columnIndex otherSlot := by
    rw [hcolumn, hrepresentation, Matrix.mul_apply]
    rfl
  by_cases hvanish : tightDir (basisLabel privateSlot) atomIndex = 0
  · have hblock : atomIndex ∈ activeSubset (basisLabel otherSlot) :=
      (hcoverPair atomIndex).resolve_right fun hcontra => hcontra hvanish
    rw [projection_mulVec_tightDir_of_mem hdata hmemOther hblock]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvanish, mul_zero, add_zero]
  · rw [hread, Finset.sum_eq_single privateSlot
      (fun columnIndex _ hneCol => by
        rw [hprivateBlock atomIndex hvanish columnIndex hneCol, zero_mul])
      (fun hnotMem => absurd (Finset.mem_univ _) hnotMem)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hprivateBlock atomIndex hvanish otherSlot hne]
    ring

/-- **THE DIAGONAL READING.**  Under the column identity, the left inverse
reads the diagonal coefficient of the other slot from the shifted-weight
vector alone: the private part lands on the private axis and vanishes at
the other slot. -/
theorem offblock_diagonal_reading
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {privateSlot otherSlot : Fin basisCount} (hne : otherSlot ≠ privateSlot)
    (hmemOther : basisLabel otherSlot ∈ activeSet)
    (hprivateBlock : ∀ atomIndex : Fin size,
      tightDir (basisLabel privateSlot) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ privateSlot →
        tightDir (basisLabel columnIndex) atomIndex = 0)
    (hcoverPair : ∀ atomIndex : Fin size,
      atomIndex ∈ activeSubset (basisLabel otherSlot)
        ∨ tightDir (basisLabel privateSlot) atomIndex ≠ 0) :
    M otherSlot otherSlot
      = (L *ᵥ fun atomIndex => (value + weight atomIndex)
          * tightDir (basisLabel otherSlot) atomIndex) otherSlot := by
  classical
  have hM : M = L * (projection * tightBasisColumns tightDir basisLabel) := by
    rw [hrepresentation, ← Matrix.mul_assoc, hleft, Matrix.one_mul]
  have hentry : M otherSlot otherSlot
      = (L *ᵥ (projection *ᵥ tightDir (basisLabel otherSlot))) otherSlot := by
    rw [hM, Matrix.mul_apply]
    rfl
  rw [hentry,
    offblock_column_identity hdata basisLabel hrepresentation hne hmemOther
      hprivateBlock hcoverPair,
    Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
    leftInverse_mulVec_tightDir_basisLabel basisLabel L hleft privateSlot]
  simp [hne]

end Gtz
