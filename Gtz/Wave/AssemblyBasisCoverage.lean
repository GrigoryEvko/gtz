import Gtz.Wave.AssemblyCircuitEquations
import Gtz.Wave.DatumSupportDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The basis coverage law — the basis supports cover every atom

The constant-diagonal field of a stationary datum forces coverage: at every
atom the assembly diagonal is `1/size`, and the diagonal is the nonnegative
overlap mass of the positive labels.  Thus every atom sits in the datum tight
support of some positive label.  The reconstruction then pushes the coverage
onto the basis: a positive direction is a coefficient combination of the basis
directions, thus a nonzero coordinate of a positive direction forces a nonzero
coordinate of some basis direction at the same atom.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.exists_positive_datumTightSupport` — **THE DATUM COVERAGE.**  Every
  atom sits in the datum tight support of a positive label.
* `Gtz.exists_basisIndex_datumTightSupport` — **THE BASIS COVERAGE.**  Every
  atom sits in the datum tight support of a basis label.
* `Gtz.biUnion_datumTightSupport_basis_eq_univ` — the packaged union form.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every stationary
datum, and at every chosen basis with a left inverse.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE DATUM COVERAGE.**  Every atom sits in the datum tight support of
some positive label.  The assembly diagonal at the atom is `1/size`, a sum of
nonnegative terms over the active family.  If no positive label touched the
atom, every term would vanish and the diagonal would read zero. -/
theorem exists_positive_datumTightSupport
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomIndex : Fin size) :
    ∃ label ∈ positiveActiveSet activeSet activeWeight,
      atomIndex ∈ datumTightSupport tightDir label := by
  by_contra hnone
  push Not at hnone
  have hvanish : ∀ label ∈ activeSet,
      activeWeight label * tightDir label atomIndex ^ 2 = 0 := by
    intro label hactive
    by_cases hpos : 0 < activeWeight label
    · have hmiss := hnone label (mem_positiveActiveSet.mpr ⟨hactive, hpos⟩)
      have hzero : tightDir label atomIndex = 0 := by
        by_contra hne
        exact hmiss (mem_datumTightSupport.mpr hne)
      rw [hzero]
      ring
    · have hzero : activeWeight label = 0 :=
        le_antisymm (not_lt.mp hpos) (hdata.activeWeight_nonneg label hactive)
      rw [hzero, zero_mul]
  have hdiagonal := hdata.assembly_diagonal atomIndex
  rw [chartMultiplierAssembly_diagonal, Finset.sum_eq_zero hvanish] at hdiagonal
  have hsizePos : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (size_pos_of_isChartStationaryData hdata))
  linarith

/-- **THE BASIS COVERAGE.**  Every atom sits in the datum tight support of
some basis label.  The datum coverage gives a positive label with a nonzero
coordinate at the atom, and the reconstruction writes that coordinate as a
coefficient combination of the basis coordinates at the same atom. -/
theorem exists_basisIndex_datumTightSupport
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    (atomIndex : Fin size) :
    ∃ columnIndex : Fin basisCount,
      atomIndex ∈ datumTightSupport tightDir (basisLabel columnIndex) := by
  obtain ⟨label, hmem, hsupport⟩ := exists_positive_datumTightSupport hdata atomIndex
  by_contra hnone
  push Not at hnone
  have hbasisZero : ∀ columnIndex : Fin basisCount,
      tightDir (basisLabel columnIndex) atomIndex = 0 := by
    intro columnIndex
    by_contra hne
    exact hnone columnIndex (mem_datumTightSupport.mpr hne)
  have hread := reconstruction_apply_of_mem_positive hdata basisLabel hbasisSpan L hleft
    hmem atomIndex
  rw [Finset.sum_eq_zero (fun columnIndex _ => by
    rw [hbasisZero columnIndex, mul_zero])] at hread
  exact mem_datumTightSupport.mp hsupport hread

/-- The packaged union form of the basis coverage: the basis datum tight
supports cover the full atom set. -/
theorem biUnion_datumTightSupport_basis_eq_univ
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1) :
    Finset.univ.biUnion
        (fun columnIndex => datumTightSupport tightDir (basisLabel columnIndex))
      = (Finset.univ : Finset (Fin size)) := by
  classical
  refine Finset.eq_univ_iff_forall.mpr fun atomIndex => ?_
  obtain ⟨columnIndex, hsupport⟩ :=
    exists_basisIndex_datumTightSupport hdata basisLabel hbasisSpan L hleft atomIndex
  exact Finset.mem_biUnion.mpr ⟨columnIndex, Finset.mem_univ columnIndex, hsupport⟩

end Gtz
