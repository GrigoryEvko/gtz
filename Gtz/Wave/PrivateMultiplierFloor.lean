import Gtz.Wave.CanonicalSharedEdgeClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}
variable {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → Fin size → ℝ}

/-- Every coordinate owned by an active row contributes exactly `1/size` to
its multiplier.  Summing those contributions and using unit norm gives the
coordinate-free multiplier floor `|owned|/size ≤ mu`. -/
theorem card_mul_inv_size_le_activeWeight_of_privateAtomSet
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {privateAtomSet : activeIndex → Finset (Fin size)}
    (hprivate : HasPrivateAtomSystem activeSet tightDir privateAtomSet)
    {ownerLabel : activeIndex} (hownerMem : ownerLabel ∈ activeSet) :
    ((privateAtomSet ownerLabel).card : ℝ) * ((size : ℝ))⁻¹
      ≤ activeWeight ownerLabel := by
  have hmass :
      ∑ atomIndex ∈ privateAtomSet ownerLabel,
          activeWeight ownerLabel * tightDir ownerLabel atomIndex ^ 2
        = ((privateAtomSet ownerLabel).card : ℝ) * ((size : ℝ))⁻¹ := by
    rw [Finset.sum_congr rfl fun atomIndex hatomMem =>
      activeWeight_mul_sq_mem_privateAtomSet hdata hprivate hownerMem hatomMem]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hunit : ∑ atomIndex : Fin size, tightDir ownerLabel atomIndex ^ 2 = 1 := by
    have hunit' := hdata.tightDir_unit ownerLabel hownerMem
    rw [dotProduct] at hunit'
    simpa only [pow_two] using hunit'
  have hsquares :
      ∑ atomIndex ∈ privateAtomSet ownerLabel, tightDir ownerLabel atomIndex ^ 2
        ≤ 1 := by
    rw [← hunit]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun atomIndex _ _ => sq_nonneg _)
  have hweightNonneg := hdata.activeWeight_nonneg ownerLabel hownerMem
  have hscaled := mul_le_mul_of_nonneg_left hsquares hweightNonneg
  rw [mul_one] at hscaled
  calc
    ((privateAtomSet ownerLabel).card : ℝ) * ((size : ℝ))⁻¹
        = activeWeight ownerLabel
            * ∑ atomIndex ∈ privateAtomSet ownerLabel,
                tightDir ownerLabel atomIndex ^ 2 := by
            rw [Finset.mul_sum]
            exact hmass.symm
    _ ≤ activeWeight ownerLabel := hscaled


end Gtz
