import Gtz.Wave.DenseEigenpairTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shared-support pair trace — two slots on one support read their trace

Two basis slots with the same support, whose support atoms no other basis
column carries, read the sum of their diagonal coefficients: it equals the
sum of two shifted weights at two support atoms.  The two-carrier row
readings make each support atom an eigenvector of the two-by-two
coefficient corner, and the independent pair exhausts the spectrum.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.pair_trace_eq_of_shared_support` — **THE PAIR TRACE.**

## Vacuity

Nothing here quantifies over a crux.  The statement holds at every
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

/-- **THE PAIR TRACE.**  Two slots with one shared support, whose atoms no
other basis column carries, read the sum of their diagonal coefficients as
two shifted weights at two distinct support atoms. -/
theorem pair_trace_eq_of_shared_support
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    {L : Matrix (Fin basisCount) (Fin size) ℝ}
    {M : Matrix (Fin basisCount) (Fin basisCount) ℝ}
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    {firstSlot secondSlot : Fin basisCount} (hne : firstSlot ≠ secondSlot)
    (hmemFirst : basisLabel firstSlot ∈ activeSet)
    (hmemSecond : basisLabel secondSlot ∈ activeSet)
    (hshared : datumTightSupport tightDir (basisLabel firstSlot)
      = datumTightSupport tightDir (basisLabel secondSlot))
    (hnonempty : (datumTightSupport tightDir (basisLabel firstSlot)).Nonempty)
    (hcarriers : ∀ atomIndex : Fin size,
      tightDir (basisLabel firstSlot) atomIndex ≠ 0 →
      ∀ columnIndex, columnIndex ≠ firstSlot → columnIndex ≠ secondSlot →
        tightDir (basisLabel columnIndex) atomIndex = 0) :
    ∃ firstAtom ∈ datumTightSupport tightDir (basisLabel firstSlot),
      ∃ secondAtom ∈ datumTightSupport tightDir (basisLabel firstSlot),
        firstAtom ≠ secondAtom
          ∧ M firstSlot firstSlot + M secondSlot secondSlot
            = (value + weight firstAtom) + (value + weight secondAtom) := by
  classical
  obtain ⟨firstAtom, hfirstMem, secondAtom, hsecondMem, hdet⟩ :=
    exists_support_det_ne_zero basisLabel hleft hne hshared hnonempty
  have hdistinct : firstAtom ≠ secondAtom := by
    intro hcontra
    apply hdet
    rw [hcontra]
    ring
  have heigen : ∀ atomIndex ∈ datumTightSupport tightDir (basisLabel firstSlot),
      (!![M firstSlot firstSlot, M secondSlot firstSlot;
          M firstSlot secondSlot, M secondSlot secondSlot] : Matrix (Fin 2) (Fin 2) ℝ)
        *ᵥ ![tightDir (basisLabel firstSlot) atomIndex,
            tightDir (basisLabel secondSlot) atomIndex]
      = (value + weight atomIndex)
        • ![tightDir (basisLabel firstSlot) atomIndex,
            tightDir (basisLabel secondSlot) atomIndex] := by
    intro atomIndex hmem
    have hblockFirst : atomIndex ∈ activeSubset (basisLabel firstSlot) :=
      datumTightSupport_subset hdata hmemFirst hmem
    have hblockSecond : atomIndex ∈ activeSubset (basisLabel secondSlot) :=
      datumTightSupport_subset hdata hmemSecond (hshared ▸ hmem)
    have hzeroOff : ∀ columnIndex, columnIndex ≠ firstSlot →
        columnIndex ≠ secondSlot →
        tightDir (basisLabel columnIndex) atomIndex = 0 :=
      hcarriers atomIndex (mem_datumTightSupport.mp hmem)
    have hreadFirst := two_carrier_row_reading hdata basisLabel hrepresentation
      hne hmemFirst hblockFirst hzeroOff
    have hreadSecond := two_carrier_row_reading hdata basisLabel hrepresentation
      hne hmemSecond hblockSecond hzeroOff
    funext coordIndex
    fin_cases coordIndex
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hreadFirst
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination hreadSecond
  have htrace := trace_eq_add_of_eigen_pair (heigen firstAtom hfirstMem)
    (heigen secondAtom hsecondMem)
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      intro hcontra
      apply hdet
      linear_combination hcontra)
  rw [Matrix.trace_fin_two_of] at htrace
  exact ⟨firstAtom, hfirstMem, secondAtom, hsecondMem, hdistinct, htrace⟩

end Gtz
