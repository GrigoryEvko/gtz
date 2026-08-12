import Gtz.Wave.AssemblyCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The circuit equations — support constraints on the coefficient reading

The reconstruction `q = B (L q)` turns every support constraint on a positive
tight direction into a LINEAR EQUATION on its coefficient reading: at every
atom outside the label's block the basis combination vanishes.  These are the
circuit equations of the rank-four census — an extra positive label carries
one equation per atom outside its block, and the per-pattern work solves
exactly this system against the basis supports.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.reconstruction_apply_of_mem_positive` — the reconstruction read at one
  atom: `q y = Σ_i (L q)_i · q_i y`.
* `Gtz.circuit_equation_of_mem_positive_of_notMem` — **THE CIRCUIT
  EQUATION.**  At every atom outside the label's block the coefficient
  combination of the basis directions vanishes.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every stationary
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

/-- The reconstruction, read at one atom: a positive direction's value is the
coefficient combination of the basis directions' values. -/
theorem reconstruction_apply_of_mem_positive
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {label : activeIndex} (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    (atomIndex : Fin size) :
    tightDir label atomIndex
      = ∑ columnIndex, (L *ᵥ tightDir label) columnIndex
          * tightDir (basisLabel columnIndex) atomIndex := by
  have hreconstruction :=
    tightDir_eq_reconstruction_of_mem_positive hdata basisLabel hbasisSpan L hleft hmem
  have happly := congrFun hreconstruction atomIndex
  rw [happly, tightBasisColumns_mulVec]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **THE CIRCUIT EQUATION.**  At every atom outside a positive label's block,
the coefficient combination of the basis directions vanishes.  One linear
equation on the coefficient reading per outside atom — the system the
rank-four census solves against the basis supports. -/
theorem circuit_equation_of_mem_positive_of_notMem
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1)
    {label : activeIndex} (hmem : label ∈ positiveActiveSet activeSet activeWeight)
    {atomIndex : Fin size} (hnotMem : atomIndex ∉ activeSubset label) :
    ∑ columnIndex, (L *ᵥ tightDir label) columnIndex
        * tightDir (basisLabel columnIndex) atomIndex = 0 := by
  have hvanish : tightDir label atomIndex = 0 :=
    hdata.tightDir_support label (positiveActiveSet_subset_activeSet
      (Finset.mem_coe.mp hmem)) atomIndex hnotMem
  rw [← reconstruction_apply_of_mem_positive hdata basisLabel hbasisSpan L hleft hmem
    atomIndex]
  exact hvanish

end Gtz
