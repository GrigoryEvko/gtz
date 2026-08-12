import Gtz.Wave.ThreeRowCapturedDichotomy
import Gtz.Wave.StationaryPositiveSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- Canonical ordering of the three-member shared-edge family. -/
def canonicalSharedEdgeSubset : Fin 3 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 4, 5}, {1, 2, 3}]

/-- The private coordinates used for the spectral floor: the first row owns
nothing, the disjoint rows own `{4,5}` and `{3}`. -/
def canonicalSharedEdgePrivateAtomSet : Fin 3 → Finset (Fin 6) :=
  ![∅, {4, 5}, {3}]

variable {projection : Matrix (Fin 6) (Fin 6) ℝ}
variable {weight : Fin 6 → ℝ} {value : ℝ}
variable {activeWeight : Fin 3 → ℝ}
variable {tightDir : Fin 3 → Fin 6 → ℝ}

theorem hasPrivateAtomSystem_canonicalSharedEdge
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir) :
    HasPrivateAtomSystem (Finset.univ : Finset (Fin 3)) tightDir
      canonicalSharedEdgePrivateAtomSet := by
  apply hasPrivateAtomSystem_of_notMem_activeSubset hdata
  intro ownerLabel _ atomIndex hatomMem otherLabel _ hne
  fin_cases ownerLabel <;> fin_cases otherLabel <;>
    simp [canonicalSharedEdgePrivateAtomSet, canonicalSharedEdgeSubset] at hatomMem hne ⊢
  all_goals omega

/-- The two complementary shared-edge rows have disjoint supports. -/
theorem dotProduct_canonicalSharedEdge_disjointRows_eq_zero
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir) :
    tightDir 1 ⬝ᵥ tightDir 2 = 0 := by
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro atomIndex _
  have hdisjoint : Disjoint (canonicalSharedEdgeSubset 1)
      (canonicalSharedEdgeSubset 2) := by
    simp [canonicalSharedEdgeSubset]
  by_cases hfirst : atomIndex ∈ canonicalSharedEdgeSubset 1
  · have hsecond : atomIndex ∉ canonicalSharedEdgeSubset 2 := by
      intro hcontra
      exact Finset.disjoint_left.mp hdisjoint hfirst hcontra
    rw [hdata.tightDir_support 2 (Finset.mem_univ _) atomIndex hsecond, mul_zero]
  · rw [hdata.tightDir_support 1 (Finset.mem_univ _) atomIndex hfirst, zero_mul]

/-- The `{0,4,5}` row has positive multiplier without any extra hypothesis:
coordinate `4` is private and carries stationary diagonal mass `1/6`. -/
theorem canonicalSharedEdge_firstDisjointWeight_pos
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir) :
    0 < activeWeight 1 := by
  have hprivate := hasPrivateAtomSystem_canonicalSharedEdge hdata
  have hmass := activeWeight_mul_sq_mem_privateAtomSet hdata hprivate
    (ownerLabel := (1 : Fin 3)) (atomIndex := (4 : Fin 6))
    (Finset.mem_univ _) (by simp [canonicalSharedEdgePrivateAtomSet])
  have hnonneg := hdata.activeWeight_nonneg 1 (Finset.mem_univ _)
  have hne : activeWeight 1 ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmass
    norm_num at hmass
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The `{1,2,3}` row likewise has positive multiplier because coordinate `3`
is private. -/
theorem canonicalSharedEdge_secondDisjointWeight_pos
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir) :
    0 < activeWeight 2 := by
  have hprivate := hasPrivateAtomSystem_canonicalSharedEdge hdata
  have hmass := activeWeight_mul_sq_mem_privateAtomSet hdata hprivate
    (ownerLabel := (2 : Fin 3)) (atomIndex := (3 : Fin 6))
    (Finset.mem_univ _) (by simp [canonicalSharedEdgePrivateAtomSet])
  have hnonneg := hdata.activeWeight_nonneg 2 (Finset.mem_univ _)
  have hne : activeWeight 2 ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmass
    norm_num at hmass
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The row on `{0,4,5}` has multiplier at least `1/3`, because coordinates
`4` and `5` are both private and each carries stationary mass `1/6`. -/
theorem third_le_canonicalSharedEdge_firstDisjointWeight
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir)
    (hpositive : 0 < activeWeight 1) :
    (1 / 3 : ℝ) ≤ activeWeight 1 := by
  have hprivate := hasPrivateAtomSystem_canonicalSharedEdge hdata
  have hmassFour := activeWeight_mul_sq_mem_privateAtomSet hdata hprivate
    (ownerLabel := (1 : Fin 3)) (atomIndex := (4 : Fin 6))
    (Finset.mem_univ _) (by simp [canonicalSharedEdgePrivateAtomSet])
  have hmassFive := activeWeight_mul_sq_mem_privateAtomSet hdata hprivate
    (ownerLabel := (1 : Fin 3)) (atomIndex := (5 : Fin 6))
    (Finset.mem_univ _) (by simp [canonicalSharedEdgePrivateAtomSet])
  have hunit := hdata.tightDir_unit 1 (Finset.mem_univ _)
  rw [dotProduct, Fin.sum_univ_six] at hunit
  norm_num at hmassFour hmassFive
  nlinarith [sq_nonneg (tightDir 1 0), sq_nonneg (tightDir 1 1),
    sq_nonneg (tightDir 1 2), sq_nonneg (tightDir 1 3),
    sq_nonneg (tightDir 1 4), sq_nonneg (tightDir 1 5)]

/-- The row on `{1,2,3}` has multiplier at least `1/6`, because coordinate
`3` is private. -/
theorem sixth_le_canonicalSharedEdge_secondDisjointWeight
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir)
    (hpositive : 0 < activeWeight 2) :
    (1 / 6 : ℝ) ≤ activeWeight 2 := by
  have hprivate := hasPrivateAtomSystem_canonicalSharedEdge hdata
  have hmassThree := activeWeight_mul_sq_mem_privateAtomSet hdata hprivate
    (ownerLabel := (2 : Fin 3)) (atomIndex := (3 : Fin 6))
    (Finset.mem_univ _) (by simp [canonicalSharedEdgePrivateAtomSet])
  have hunit := hdata.tightDir_unit 2 (Finset.mem_univ _)
  rw [dotProduct, Fin.sum_univ_six] at hunit
  norm_num at hmassThree
  nlinarith [sq_nonneg (tightDir 2 0), sq_nonneg (tightDir 2 1),
    sq_nonneg (tightDir 2 2), sq_nonneg (tightDir 2 3),
    sq_nonneg (tightDir 2 4), sq_nonneg (tightDir 2 5)]

/-- **THE CANONICAL SHARED-EDGE FAMILY IS CLOSED.**  No positive-multiplier
stationary datum on `{{0,1,2},{0,4,5},{1,2,3}}` can have value in
`(-1/6,0)`. -/
theorem zero_le_value_of_canonicalSharedEdgeStationaryData
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir)
    (hvalueFloor : -(1 / 6 : ℝ) < value)
    (hactiveWeightPositive : ∀ activeLabel : Fin 3, 0 < activeWeight activeLabel) :
    0 ≤ value := by
  apply value_nonneg_of_three_active_rows_of_two_orthogonal_floored_rows hdata
  · norm_num
    linarith
  · exact hactiveWeightPositive
  · exact (by
      have := third_le_canonicalSharedEdge_firstDisjointWeight hdata
        (hactiveWeightPositive 1)
      norm_num at this ⊢
      linarith)
  · norm_num
    exact sixth_le_canonicalSharedEdge_secondDisjointWeight hdata
      (hactiveWeightPositive 2)
  · exact dotProduct_canonicalSharedEdge_disjointRows_eq_zero hdata

/-- The first shared-edge row may carry zero multiplier.  In that case the
positive support consists of the two disjoint complementary rows, so the
landed disjoint-subset dichotomy pins the value to `-1/6` or at least `1/3`.
The strict chart floor excludes the endpoint. -/
theorem zero_le_value_of_canonicalSharedEdgeStationaryData_of_disjointRows_positive
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir)
    (hvalueFloor : -(1 / 6 : ℝ) < value)
    (hfirstDisjointPositive : 0 < activeWeight 1)
    (hsecondDisjointPositive : 0 < activeWeight 2) :
    0 ≤ value := by
  rcases eq_or_lt_of_le (hdata.activeWeight_nonneg 0 (Finset.mem_univ _)) with
      hzero | hpositive
  · have hzero' : activeWeight 0 = 0 := hzero.symm
    have hrestricted := hdata.restrict_positiveActiveSet
    have hpositiveSet :
        positiveActiveSet (Finset.univ : Finset (Fin 3)) activeWeight = {1, 2} := by
      ext activeLabel
      fin_cases activeLabel <;>
        simp [positiveActiveSet, hzero', hfirstDisjointPositive, hsecondDisjointPositive]
    rw [hpositiveSet] at hrestricted
    have hdisjoint : ∀ firstLabel ∈ ({1, 2} : Finset (Fin 3)),
        ∀ secondLabel ∈ ({1, 2} : Finset (Fin 3)), firstLabel ≠ secondLabel →
          Disjoint (canonicalSharedEdgeSubset firstLabel)
            (canonicalSharedEdgeSubset secondLabel) := by
      intro firstLabel hfirst secondLabel hsecond hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
      rcases hfirst with rfl | rfl <;> rcases hsecond with rfl | rfl
      · exact (hne rfl).elim
      · simp [canonicalSharedEdgeSubset]
      · simp [canonicalSharedEdgeSubset]
      · exact (hne rfl).elim
    rcases value_eq_neg_inv_size_or_le_of_pairwiseDisjoint_activeSubset
        hrestricted hdisjoint with hendpoint | hlower
    · norm_num at hendpoint
      linarith
    · norm_num at hlower
      linarith
  · exact zero_le_value_of_canonicalSharedEdgeStationaryData hdata hvalueFloor
      (fun activeLabel => by
        fin_cases activeLabel
        · exact hpositive
        · exact hfirstDisjointPositive
        · exact hsecondDisjointPositive)

/-- The canonical shared-edge family admits no stationary value in
`(-1/6,0)`.  Positivity of the two disjoint-row multipliers follows from their
private coordinates, so no multiplier hypothesis remains. -/
theorem zero_le_value_of_canonicalSharedEdgeStationaryData_of_strictFloor
    (hdata : IsChartStationaryData 3 projection weight value
      (Finset.univ : Finset (Fin 3)) canonicalSharedEdgeSubset activeWeight tightDir)
    (hvalueFloor : -(1 / 6 : ℝ) < value) :
    0 ≤ value :=
  zero_le_value_of_canonicalSharedEdgeStationaryData_of_disjointRows_positive hdata
    hvalueFloor (canonicalSharedEdge_firstDisjointWeight_pos hdata)
    (canonicalSharedEdge_secondDisjointWeight_pos hdata)


end Gtz
