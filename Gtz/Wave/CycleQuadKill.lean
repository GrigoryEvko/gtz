import Gtz.Wave.CornerTraceBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The cycle kill — one independent double on a four-cycle exhausts the trace

Four slots on a cycle, with two independent pair atoms on one corner and
one eigen atom on each of the other three corners, exhaust the trace
budget: the double corner reads its trace exactly, the other three
corners obey the trace cap, and the cycle sum gives
`1 <= 5 * value + 1` against the negative value.  This kill closes the
doubled-edge representatives of the dense census branch whenever one
double is independent, under a diagonal Gram.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.false_of_cycle_with_independent_double` — **THE KILL.**

## Vacuity

The statement takes the negative value as a hypothesis, and a crux
supplies it.  It is vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE CYCLE KILL.**  One independent double and three eigen corners on
a four-cycle exhaust the trace budget under a diagonal Gram. -/
theorem false_of_cycle_with_independent_double
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hvalueNeg : value < 0)
    (basisLabel : Fin 4 → activeIndex)
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {gramWeight : Fin 4 → ℝ}
    (hrepresentation : projection * tightBasisColumns tightDir basisLabel
      = tightBasisColumns tightDir basisLabel * M)
    (htrace : Matrix.trace M = 2)
    (hmemAll : ∀ columnIndex, basisLabel columnIndex ∈ activeSet)
    (hgramPos : ∀ slotIndex, 0 < gramWeight slotIndex)
    (hYpsd : (Matrix.diagonal gramWeight
      - M * Matrix.diagonal gramWeight).PosSemidef)
    {slotA slotB slotC slotD : Fin 4}
    (hAB : slotA ≠ slotB) (hCD : slotC ≠ slotD)
    (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    (hBC : slotB ≠ slotC) (hBD : slotB ≠ slotD)
    {doubleOne doubleTwo singleBC singleCD singleDA : Fin size}
    (hOneCarriers : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) doubleOne = 0)
    (hTwoCarriers : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) doubleTwo = 0)
    (hBCcarriers : ∀ columnIndex, columnIndex ≠ slotB → columnIndex ≠ slotC →
      tightDir (basisLabel columnIndex) singleBC = 0)
    (hCDcarriers : ∀ columnIndex, columnIndex ≠ slotC → columnIndex ≠ slotD →
      tightDir (basisLabel columnIndex) singleCD = 0)
    (hDAcarriers : ∀ columnIndex, columnIndex ≠ slotD → columnIndex ≠ slotA →
      tightDir (basisLabel columnIndex) singleDA = 0)
    (hOneBlockA : doubleOne ∈ activeSubset (basisLabel slotA))
    (hOneBlockB : doubleOne ∈ activeSubset (basisLabel slotB))
    (hTwoBlockA : doubleTwo ∈ activeSubset (basisLabel slotA))
    (hTwoBlockB : doubleTwo ∈ activeSubset (basisLabel slotB))
    (hBCblockB : singleBC ∈ activeSubset (basisLabel slotB))
    (hBCblockC : singleBC ∈ activeSubset (basisLabel slotC))
    (hCDblockC : singleCD ∈ activeSubset (basisLabel slotC))
    (hCDblockD : singleCD ∈ activeSubset (basisLabel slotD))
    (hDAblockD : singleDA ∈ activeSubset (basisLabel slotD))
    (hDAblockA : singleDA ∈ activeSubset (basisLabel slotA))
    (hOneDenseA : tightDir (basisLabel slotA) doubleOne ≠ 0)
    (hOneDenseB : tightDir (basisLabel slotB) doubleOne ≠ 0)
    (hTwoDenseA : tightDir (basisLabel slotA) doubleTwo ≠ 0)
    (hTwoDenseB : tightDir (basisLabel slotB) doubleTwo ≠ 0)
    (hBCdenseB : tightDir (basisLabel slotB) singleBC ≠ 0)
    (hCDdenseC : tightDir (basisLabel slotC) singleCD ≠ 0)
    (hDAdenseD : tightDir (basisLabel slotD) singleDA ≠ 0)
    (hdet : tightDir (basisLabel slotA) doubleOne
          * tightDir (basisLabel slotB) doubleTwo
        - tightDir (basisLabel slotB) doubleOne
          * tightDir (basisLabel slotA) doubleTwo ≠ 0) :
    False := by
  classical
  have hcap : ∀ atomIndex : Fin size, value + weight atomIndex < 1 :=
    value_add_weight_lt_one_of_isChartStationaryData_of_neg hdata hvalueNeg
  have hfloor : ∀ atomIndex : Fin size, 0 ≤ value + weight atomIndex := by
    intro atomIndex
    have := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
    linarith
  have hABtrace : M slotA slotA + M slotB slotB
      = (value + weight doubleOne) + (value + weight doubleTwo) :=
    corner_trace_eq_of_two_eigen_atoms
      (two_carrier_row_reading hdata basisLabel hrepresentation hAB
        (hmemAll slotA) hOneBlockA hOneCarriers)
      (two_carrier_row_reading hdata basisLabel hrepresentation hAB
        (hmemAll slotB) hOneBlockB hOneCarriers)
      (two_carrier_row_reading hdata basisLabel hrepresentation hAB
        (hmemAll slotA) hTwoBlockA hTwoCarriers)
      (two_carrier_row_reading hdata basisLabel hrepresentation hAB
        (hmemAll slotB) hTwoBlockB hTwoCarriers)
      hdet
  have hBCtrace : M slotB slotB + M slotC slotC ≤ 1 + (value + weight singleBC) :=
    corner_trace_le_of_eigen_rows
      (two_carrier_row_reading hdata basisLabel hrepresentation hBC
        (hmemAll slotB) hBCblockB hBCcarriers)
      (two_carrier_row_reading hdata basisLabel hrepresentation hBC
        (hmemAll slotC) hBCblockC hBCcarriers)
      (Or.inl hBCdenseB) (hcap singleBC)
      (corner_complement_det_nonneg_of_diagonal_gram hgramPos hYpsd hBC)
  have hCDtrace : M slotC slotC + M slotD slotD ≤ 1 + (value + weight singleCD) :=
    corner_trace_le_of_eigen_rows
      (two_carrier_row_reading hdata basisLabel hrepresentation hCD
        (hmemAll slotC) hCDblockC hCDcarriers)
      (two_carrier_row_reading hdata basisLabel hrepresentation hCD
        (hmemAll slotD) hCDblockD hCDcarriers)
      (Or.inl hCDdenseC) (hcap singleCD)
      (corner_complement_det_nonneg_of_diagonal_gram hgramPos hYpsd hCD)
  have hDA : slotD ≠ slotA := Ne.symm hAD
  have hDAtrace : M slotD slotD + M slotA slotA ≤ 1 + (value + weight singleDA) :=
    corner_trace_le_of_eigen_rows
      (two_carrier_row_reading hdata basisLabel hrepresentation hDA
        (hmemAll slotD) hDAblockD hDAcarriers)
      (two_carrier_row_reading hdata basisLabel hrepresentation hDA
        (hmemAll slotA) hDAblockA hDAcarriers)
      (Or.inl hDAdenseD) (hcap singleDA)
      (corner_complement_det_nonneg_of_diagonal_gram hgramPos hYpsd hDA)
  -- the trace split over the four distinct slots
  have hBnotMem : slotB ∉ ({slotC, slotD} : Finset (Fin 4)) := by
    simp [hBC, hBD]
  have hAnotMem : slotA ∉ ({slotB, slotC, slotD} : Finset (Fin 4)) := by
    simp [hAB, hAC, hAD]
  have hCnotMem : slotC ∉ ({slotD} : Finset (Fin 4)) := by
    simp [hCD]
  have hslotCard : ({slotA, slotB, slotC, slotD} : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_insert_of_notMem hAnotMem,
      Finset.card_insert_of_notMem hBnotMem,
      Finset.card_insert_of_notMem hCnotMem, Finset.card_singleton]
  have huniv : ({slotA, slotB, slotC, slotD} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin, hslotCard]
  have htraceSplit : Matrix.trace M
      = M slotA slotA + (M slotB slotB + (M slotC slotC + M slotD slotD)) := by
    have htraceSum : Matrix.trace M = ∑ slotIndex : Fin 4, M slotIndex slotIndex := rfl
    rw [htraceSum, ← huniv, Finset.sum_insert hAnotMem, Finset.sum_insert hBnotMem,
      Finset.sum_insert hCnotMem, Finset.sum_singleton]
  rw [htraceSplit] at htrace
  -- the five atoms are distinct
  have hOneTwo : doubleOne ≠ doubleTwo := by
    intro hcontra
    apply hdet
    rw [hcontra]
    ring
  have hOneBC : doubleOne ≠ singleBC := by
    intro hcontra
    have hzero := hBCcarriers slotA hAB hAC
    rw [← hcontra] at hzero
    exact hOneDenseA hzero
  have hOneCD : doubleOne ≠ singleCD := by
    intro hcontra
    have hzero := hCDcarriers slotA hAC hAD
    rw [← hcontra] at hzero
    exact hOneDenseA hzero
  have hOneDA : doubleOne ≠ singleDA := by
    intro hcontra
    have hzero := hDAcarriers slotB hBD (Ne.symm hAB)
    rw [← hcontra] at hzero
    exact hOneDenseB hzero
  have hTwoBC : doubleTwo ≠ singleBC := by
    intro hcontra
    have hzero := hBCcarriers slotA hAB hAC
    rw [← hcontra] at hzero
    exact hTwoDenseA hzero
  have hTwoCD : doubleTwo ≠ singleCD := by
    intro hcontra
    have hzero := hCDcarriers slotA hAC hAD
    rw [← hcontra] at hzero
    exact hTwoDenseA hzero
  have hTwoDA : doubleTwo ≠ singleDA := by
    intro hcontra
    have hzero := hDAcarriers slotB hBD (Ne.symm hAB)
    rw [← hcontra] at hzero
    exact hTwoDenseB hzero
  have hBCCD : singleBC ≠ singleCD := by
    intro hcontra
    have hzero := hCDcarriers slotB hBC hBD
    rw [← hcontra] at hzero
    exact hBCdenseB hzero
  have hBCDA : singleBC ≠ singleDA := by
    intro hcontra
    have hzero := hDAcarriers slotB hBD (Ne.symm hAB)
    rw [← hcontra] at hzero
    exact hBCdenseB hzero
  have hCDDA : singleCD ≠ singleDA := by
    intro hcontra
    have hzero := hDAcarriers slotC hCD (Ne.symm hAC)
    rw [← hcontra] at hzero
    exact hCDdenseC hzero
  -- the weight bound over the five atoms
  have hfourthNotMem : singleCD ∉ ({singleDA} : Finset (Fin size)) := by
    simp [hCDDA]
  have hthirdNotMem : singleBC ∉ ({singleCD, singleDA} : Finset (Fin size)) := by
    simp [hBCCD, hBCDA]
  have hsecondNotMem : doubleTwo
      ∉ ({singleBC, singleCD, singleDA} : Finset (Fin size)) := by
    simp [hTwoBC, hTwoCD, hTwoDA]
  have hfirstNotMem : doubleOne
      ∉ ({doubleTwo, singleBC, singleCD, singleDA} : Finset (Fin size)) := by
    simp [hOneTwo, hOneBC, hOneCD, hOneDA]
  have hweightExpand : ∑ atomIndex ∈
      ({doubleOne, doubleTwo, singleBC, singleCD, singleDA} : Finset (Fin size)),
        weight atomIndex
      = weight doubleOne + (weight doubleTwo + (weight singleBC
        + (weight singleCD + weight singleDA))) := by
    rw [Finset.sum_insert hfirstNotMem, Finset.sum_insert hsecondNotMem,
      Finset.sum_insert hthirdNotMem, Finset.sum_insert hfourthNotMem,
      Finset.sum_singleton]
  have hweightBound : ∑ atomIndex ∈
      ({doubleOne, doubleTwo, singleBC, singleCD, singleDA} : Finset (Fin size)),
        weight atomIndex ≤ 1 := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ
        ({doubleOne, doubleTwo, singleBC, singleCD, singleDA} : Finset (Fin size)))
      (fun atomIndex _ _ => le_of_lt (hdata.weight_pos atomIndex))
    rw [hdata.weight_sum_one] at hle
    exact hle
  rw [hweightExpand] at hweightBound
  linarith

end Gtz
