import Gtz.Design.TightLineBranchLivePairBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace Gtz

open Matrix Finset

/-- Every base atom transverse to the tight line, not merely one selected
base atom, makes its three one-slot completions one-determinant tests. -/
theorem oneSlot_posDef_iff_det_pos_of_transverseBaseLabel
    (design : WeightedDesign 6 3) {tightDir : Fin 3 → ℝ}
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    (hline : HasTightLineAt design ({0, 1, 2} : Finset (Fin 6)) tightDir)
    {baseLabel : Fin 6}
    (hbase : baseLabel ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hreading : design.atom baseLabel ⬝ᵥ tightDir ≠ 0)
    {swapIn : Fin 6}
    (hfree : swapIn ∉ ({0, 1, 2} : Finset (Fin 6))) :
    (subsetSum design
          (insert swapIn (({0, 1, 2} : Finset (Fin 6)).erase baseLabel)) - 1).PosDef
      ↔ 0 < (subsetSum design
          (insert swapIn (({0, 1, 2} : Finset (Fin 6)).erase baseLabel)) - 1).det := by
  have hatomNe : design.atom baseLabel ≠ 0 := by
    intro hzero
    apply hreading
    rw [hzero, zero_dotProduct]
  let axis := normalizedDirection (design.atom baseLabel)
  have haxisUnit : axis ⬝ᵥ axis = 1 :=
    normalizedDirection_isUnit (design.atom baseLabel) hatomNe
  have hpairPos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ ((subsetSum design
        (({0, 1, 2} : Finset (Fin 6)).erase baseLabel) - 1) *ᵥ probe) := by
    intro probe hperp hne
    apply basePairGap_form_pos_of_tightLine design tightDir baseLabel hbase
      hdominates hline hreading probe
    · exact (dotProduct_normalizedDirection_eq_zero_iff probe
        (design.atom baseLabel) hatomNe).mp hperp
    · exact hne
  have hnotErase : swapIn ∉ (({0, 1, 2} : Finset (Fin 6)).erase baseLabel) :=
    fun hmem => hfree (Finset.mem_of_mem_erase hmem)
  have hcompletionPos : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → probe ≠ 0 →
      0 < probe ⬝ᵥ ((subsetSum design
        (insert swapIn (({0, 1, 2} : Finset (Fin 6)).erase baseLabel)) - 1) *ᵥ probe) := by
    intro probe hperp hne
    exact insertGap_form_pos_of_form_pos design
      (({0, 1, 2} : Finset (Fin 6)).erase baseLabel) swapIn hnotErase probe
      (hpairPos probe hperp hne)
  exact posDef_iff_det_pos_of_unitAxisPlanePositive
    (transpose_subsetSum_sub_one design
      (insert swapIn (({0, 1, 2} : Finset (Fin 6)).erase baseLabel)))
    haxisUnit hcompletionPos

end Gtz
