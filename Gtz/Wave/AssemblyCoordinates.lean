import Gtz.Wave.RankFourNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coordinate dictionary — every positive direction reads through `L`

Every positively weighted tight direction lies in `range Ξ`, which is the
column space of the basis matrix `B`.  The left inverse therefore READS its
coordinates: `q = B (L q)` exactly.  This is the first entry of the
two-coordinate dictionary — the sparse side keeps the label's support, the
coefficient side is the vector `L q` over the basis — and it is what makes an
extra positive label a CIRCUIT over the basis rather than free data.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.tightDir_eq_reconstruction_of_mem_positive` — **THE RECONSTRUCTION.**
  `tightDir label = B *ᵥ (L *ᵥ tightDir label)` at every positive label.

## Vacuity

Nothing here quantifies over a crux.  The statement holds at every stationary
datum with a chosen basis and left inverse.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- **THE RECONSTRUCTION.**  A positively weighted tight direction is exactly
the basis combination of its coefficient reading: `q = B (L q)`. -/
theorem tightDir_eq_reconstruction_of_mem_positive
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {label : activeIndex} (hmem : label ∈ positiveActiveSet activeSet activeWeight) :
    tightDir label
      = tightBasisColumns tightDir basisLabel *ᵥ (L *ᵥ tightDir label) := by
  obtain ⟨hactive, hpos⟩ := mem_positiveActiveSet.mp hmem
  have hrangeMem : tightDir label ∈ LinearMap.range (Matrix.toLin'
      (tightBasisColumns tightDir basisLabel)) := by
    rw [range_tightBasisColumns_eq basisLabel hbasisSpan]
    exact tightDir_mem_range_multiplier_of_pos hdata hactive hpos
  obtain ⟨coordinates, hcoordinates⟩ := hrangeMem
  rw [Matrix.toLin'_apply] at hcoordinates
  rw [← hcoordinates, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    hleft, Matrix.mul_one]

end Gtz
