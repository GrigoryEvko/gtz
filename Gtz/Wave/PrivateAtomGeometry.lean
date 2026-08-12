import Gtz.Wave.SupportQuadrupleCensus

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The private-atom coefficient geometry

A private atom — an atom where exactly one basis direction is nonzero —
localizes the coefficient coordinates.  Four laws hold at every stationary
datum, with no argmax quantification anywhere: the interface of the
rank-four kills runs on the positive support alone.

The four laws.  The basis reading law: the left inverse reads a basis
direction as a coordinate axis.  The circuit kill: every positive label
whose block misses the private atom has a zero coefficient at the private
slot.  The diagonal pin: the private slot's diagonal entry of `M` is
`value + weight` at the private atom.  The leak dictionary: the off-slot
entries of the `M`-row at the private slot read the projection leak of the
other basis directions at the private atom.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.leftInverse_mulVec_tightDir_basisLabel` — the basis reading law.
* `Gtz.coefficientReading_eq_zero_of_private_atom` — **THE CIRCUIT KILL.**
* `Gtz.coefficient_diagonal_eq_of_private_atom` — **THE DIAGONAL PIN.**
* `Gtz.coefficient_row_eq_leak_of_private_atom` — the leak dictionary.
* `Gtz.weight_eq_weight_of_two_private_atoms` — two private atoms in one
  slot carry equal weights.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every
stationary datum with a chosen basis and left inverse.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- The basis reading law: the left inverse reads a basis direction as a
coordinate axis. -/
theorem leftInverse_mulVec_tightDir_basisLabel
    (basisLabel : Fin basisCount → activeIndex)
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (columnIndex : Fin basisCount) :
    L *ᵥ tightDir (basisLabel columnIndex) = Pi.single columnIndex 1 := by
  rw [← tightBasisColumns_mulVec_single (tightDir := tightDir) basisLabel columnIndex,
    Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]

/-- **THE CIRCUIT KILL AT A PRIVATE ATOM.**  Every positive label whose
block misses the private atom has a zero coefficient reading at the private
slot: the circuit equation at the private atom has one surviving term. -/
theorem coefficientReading_eq_zero_of_private_atom
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0)
    {label : activeIndex} (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    (hnotMem : privateAtom ∉ activeSubset label) :
    (L *ᵥ tightDir label) privateSlot = 0 := by
  have hcircuit := circuit_equation_of_mem_positive_of_notMem hdata basisLabel
    hbasisSpan L hleft hmem hnotMem
  rw [Finset.sum_eq_single privateSlot
    (fun columnIndex _ hne => by rw [hprivate columnIndex hne, mul_zero])
    (fun habs => absurd (Finset.mem_univ _) habs)] at hcircuit
  exact (mul_eq_zero.mp hcircuit).resolve_right hslotNe

/-- **THE DIAGONAL PIN.**  At a private atom inside the private slot's
block, the slot's diagonal entry of the coefficient projection `M` is the
value plus the weight at the atom: the tight equation reads the `M`-column
through the single surviving basis coordinate. -/
theorem coefficient_diagonal_eq_of_private_atom
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hmem : basisLabel privateSlot ∈ activeSet)
    (hatomMem : privateAtom ∈ activeSubset (basisLabel privateSlot))
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (hslotNe : tightDir (basisLabel privateSlot) privateAtom ≠ 0) :
    M privateSlot privateSlot = value + weight privateAtom := by
  have hentry : (projection * tightBasisColumns tightDir basisLabel)
        privateAtom privateSlot
      = (tightBasisColumns tightDir basisLabel * M) privateAtom privateSlot := by
    rw [hrepresentation]
  rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
  have hcollapse : ∑ columnIndex,
      tightBasisColumns tightDir basisLabel privateAtom columnIndex
        * M columnIndex privateSlot
      = tightDir (basisLabel privateSlot) privateAtom * M privateSlot privateSlot := by
    rw [Finset.sum_eq_single privateSlot
      (fun columnIndex _ hne => by
        have hzero : tightBasisColumns tightDir basisLabel privateAtom columnIndex = 0 :=
          hprivate columnIndex hne
        rw [hzero, zero_mul])
      (fun habs => absurd (Finset.mem_univ _) habs)]
    rfl
  rw [hcollapse] at hentry
  have htight := hdata.tightDir_isTight (basisLabel privateSlot) hmem privateAtom hatomMem
  have hgap : (chartStationaryGap projection weight
        *ᵥ tightDir (basisLabel privateSlot)) privateAtom
      = (∑ atomIndex, projection privateAtom atomIndex
          * tightDir (basisLabel privateSlot) atomIndex)
        - weight privateAtom * tightDir (basisLabel privateSlot) privateAtom := by
    rw [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    rfl
  rw [hgap] at htight
  have hproduct : (∑ atomIndex, projection privateAtom atomIndex
        * tightDir (basisLabel privateSlot) atomIndex)
      = ∑ atomIndex, projection privateAtom atomIndex
          * tightBasisColumns tightDir basisLabel atomIndex privateSlot := rfl
  rw [hproduct] at htight
  have hfinal : tightDir (basisLabel privateSlot) privateAtom
      * M privateSlot privateSlot
      = tightDir (basisLabel privateSlot) privateAtom
        * (value + weight privateAtom) := by
    rw [← hentry]
    ring_nf
    ring_nf at htight
    linarith
  exact mul_left_cancel₀ hslotNe hfinal

/-- **THE LEAK DICTIONARY.**  At a private atom, the private slot's `M`-row
reads the projection leak of every basis direction: the representation
column collapses to the single surviving basis coordinate. -/
theorem coefficient_row_eq_leak_of_private_atom
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {privateSlot : Fin basisCount} {privateAtom : Fin size}
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) privateAtom = 0)
    (columnIndex : Fin basisCount) :
    tightDir (basisLabel privateSlot) privateAtom * M privateSlot columnIndex
      = ∑ atomIndex, projection privateAtom atomIndex
          * tightDir (basisLabel columnIndex) atomIndex := by
  have hentry : (projection * tightBasisColumns tightDir basisLabel)
        privateAtom columnIndex
      = (tightBasisColumns tightDir basisLabel * M) privateAtom columnIndex := by
    rw [hrepresentation]
  rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
  have hcollapse : ∑ innerIndex,
      tightBasisColumns tightDir basisLabel privateAtom innerIndex
        * M innerIndex columnIndex
      = tightDir (basisLabel privateSlot) privateAtom * M privateSlot columnIndex := by
    rw [Finset.sum_eq_single privateSlot
      (fun innerIndex _ hne => by
        have hzero : tightBasisColumns tightDir basisLabel privateAtom innerIndex = 0 :=
          hprivate innerIndex hne
        rw [hzero, zero_mul])
      (fun habs => absurd (Finset.mem_univ _) habs)]
    rfl
  rw [hcollapse] at hentry
  exact hentry.symm

/-- Two private atoms in one slot carry equal weights: the diagonal pin
reads the same entry of `M` at the two atoms. -/
theorem weight_eq_weight_of_two_private_atoms
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {privateSlot : Fin basisCount} {firstAtom secondAtom : Fin size}
    (hmem : basisLabel privateSlot ∈ activeSet)
    (hfirstMem : firstAtom ∈ activeSubset (basisLabel privateSlot))
    (hsecondMem : secondAtom ∈ activeSubset (basisLabel privateSlot))
    (hfirstPrivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) firstAtom = 0)
    (hsecondPrivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      tightDir (basisLabel columnIndex) secondAtom = 0)
    (hfirstNe : tightDir (basisLabel privateSlot) firstAtom ≠ 0)
    (hsecondNe : tightDir (basisLabel privateSlot) secondAtom ≠ 0) :
    weight firstAtom = weight secondAtom := by
  have hfirst := coefficient_diagonal_eq_of_private_atom hdata basisLabel
    hrepresentation hmem hfirstMem hfirstPrivate hfirstNe
  have hsecond := coefficient_diagonal_eq_of_private_atom hdata basisLabel
    hrepresentation hmem hsecondMem hsecondPrivate hsecondNe
  have hcombined := hfirst.symm.trans hsecond
  linarith

end Gtz
