import Gtz.Wave.BothParallelDiagonalKill
import Gtz.Wave.BothParallelCircuitKill
import Gtz.Wave.BothParallelCrossPinCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel cross pin — the datum bridge

The scalar certificate of `Gtz.crossPin_scalar_kill` consumes the folded
entry equations of the all-parallel C4 datum.  This module derives every
one of them from the landed supply and discharges the cross-pin
obligation of closure five.

The bridge has four layers:

1. The collapse readers.  A triple-supported direction reads a projected
   column as three products, and a four-slot sum collapses to its four
   named slots.
2. The entry readers.  The diagonal core prices each commutation entry
   as four multiplier-weighted brackets, and idempotency prices each
   chart entry as a six-term row product.
3. The folds.  The pair sign scalars, the twin weights, the equal pair
   diagonals, and the column ratios rewrite every second-atom quantity
   as a signed multiple of its twin.
4. The branch.  The two scale balances make the two cross-pair products
   equal in square.  The dependent sign dies through the landed
   concentration kill, and the other sign feeds the scalar certificate.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.mulVec_triple_read` — the triple projected-column read.
* `Gtz.four_slot_sum_eq` — the four-slot collapse.
* `Gtz.bothParallel_four_slot_commutation` — **THE COMMUTATION READER.**
* `Gtz.bothParallelCrossPinned_holds` — **THE CROSS PIN.**
* `Gtz.rankFourBothParallelClosed_holds` — **CLOSURE FIVE.**

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## Layer 1 — the collapse readers -/

/-- **THE TRIPLE PROJECTED-COLUMN READ.**  A direction supported on three
atoms reads its projected column as three products. -/
theorem mulVec_triple_read {dir : Fin size → ℝ}
    {atomU atomV atomT : Fin size} (hUV : atomU ≠ atomV) (hUT : atomU ≠ atomT)
    (hVT : atomV ≠ atomT)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomT → dir atomIndex = 0)
    (atomRow : Fin size) :
    (projection *ᵥ dir) atomRow
      = projection atomRow atomU * dir atomU
        + projection atomRow atomV * dir atomV
        + projection atomRow atomT * dir atomT := by
  have hexp : (projection *ᵥ dir) atomRow
      = ∑ atomIndex : Fin size,
          projection atomRow atomIndex * dir atomIndex := rfl
  have hcomm : ∑ atomIndex : Fin size,
        projection atomRow atomIndex * dir atomIndex
      = ∑ atomIndex : Fin size,
          dir atomIndex * projection atomRow atomIndex :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hexp, hcomm, triple_dot_collapse hUV hUT hVT hsupp]
  ring

/-- **THE FOUR-SLOT COLLAPSE.**  A sum over four distinct slots of a
four-element index reads as the four named terms. -/
theorem four_slot_sum_eq {f : Fin 4 → ℝ} {slotA slotB slotC slotD : Fin 4}
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    (hBC : slotB ≠ slotC) (hBD : slotB ≠ slotD) (hCD : slotC ≠ slotD) :
    ∑ slot : Fin 4, f slot
      = f slotA + f slotB + f slotC + f slotD := by
  have hnotA : slotA ∉ ({slotB, slotC, slotD} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hAB heq
    · rcases Finset.mem_insert.mp hmem' with heq | hmem''
      · exact hAC heq
      · exact hAD (Finset.mem_singleton.mp hmem'')
  have hnotB : slotB ∉ ({slotC, slotD} : Finset (Fin 4)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hBC heq
    · exact hBD (Finset.mem_singleton.mp hmem')
  have hnotC : slotC ∉ ({slotD} : Finset (Fin 4)) := fun hmem =>
    hCD (Finset.mem_singleton.mp hmem)
  rw [← slot_quadruple_eq_univ hAB hAC hAD hBC hBD hCD,
    Finset.sum_insert hnotA, Finset.sum_insert hnotB,
    Finset.sum_insert hnotC, Finset.sum_singleton]
  ring

/-! ## Layer 2 — the commutation entry of the diagonal core -/

/-- **THE COMMUTATION READER.**  At an all-parallel datum the diagonal
core prices each commutation entry as four multiplier-weighted brackets
of the projected columns. -/
theorem bothParallel_four_slot_commutation
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    (basisLabel : Fin 4 → activeIndex)
    {leftInv : Matrix (Fin 4) (Fin size) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin 4) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
    {slotA slotB slotC slotD : Fin 4}
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    (hBC : slotB ≠ slotC) (hBD : slotB ≠ slotD) (hCD : slotC ≠ slotD)
    (atomRow atomCol : Fin size) :
    effectiveMultiplier activeSet activeWeight tightDir basisLabel slotA
        * ((projection *ᵥ tightDir (basisLabel slotA)) atomRow
            * tightDir (basisLabel slotA) atomCol
          - tightDir (basisLabel slotA) atomRow
            * (projection *ᵥ tightDir (basisLabel slotA)) atomCol)
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotB
        * ((projection *ᵥ tightDir (basisLabel slotB)) atomRow
            * tightDir (basisLabel slotB) atomCol
          - tightDir (basisLabel slotB) atomRow
            * (projection *ᵥ tightDir (basisLabel slotB)) atomCol)
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotC
        * ((projection *ᵥ tightDir (basisLabel slotC)) atomRow
            * tightDir (basisLabel slotC) atomCol
          - tightDir (basisLabel slotC) atomRow
            * (projection *ᵥ tightDir (basisLabel slotC)) atomCol)
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotD
        * ((projection *ᵥ tightDir (basisLabel slotD)) atomRow
            * tightDir (basisLabel slotD) atomCol
          - tightDir (basisLabel slotD) atomRow
            * (projection *ᵥ tightDir (basisLabel slotD)) atomCol)
      = 0 := by
  have hdecomp := assembly_eq_effective_diagonal hdata basisLabel hleft
    hmemPos hparallel
  have hentry := decomposition_commutation_entry hdata hdecomp atomRow atomCol
  rw [four_slot_sum_eq (f := fun slot =>
    effectiveMultiplier activeSet activeWeight tightDir basisLabel slot
      * ((projection *ᵥ tightDir (basisLabel slot)) atomRow
          * tightDir (basisLabel slot) atomCol
        - tightDir (basisLabel slot) atomRow
          * (projection *ᵥ tightDir (basisLabel slot)) atomCol))
    hAB hAC hAD hBC hBD hCD] at hentry
  linarith [hentry]

/-! ## Layer 3 — the datum bridge -/

set_option maxHeartbeats 12800000 in
/-- **THE CROSS PIN.**  At every both-parallel C4 stationary datum whose
positive labels are all parallel to basis directions, the gap entry of
the two single atoms vanishes. -/
theorem bothParallelCrossPinned_holds : BothParallelCrossPinned := by
  intro crux activeIndex activeSet activeSubset activeWeight tightDir hdata
    basisLabel leftInv hleft gram hHform hpsd hker hmemPos hparallel
    slotA slotB slotC slotD hslots hAB hAC hAD hBC hBDslot hCD
    atomA1 atomA2 atomB atomC1 atomC2 atomD hA12 hA1B hA1C1 hA1C2 hA1D
    hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hC12 hC1D hC2D
    hsuppA hsuppB hsuppC hsuppD hqA1 hqA2 hqAd hqB1 hqB2 hqBb
    hqC1 hqC2 hqCb hqD1 hqD2 hqDd hdetAB hdetCD hvanishA hvanishC
  have hmemA := positiveActiveSet_subset_activeSet (hmemPos slotA)
  have hmemB := positiveActiveSet_subset_activeSet (hmemPos slotB)
  have hmemC := positiveActiveSet_subset_activeSet (hmemPos slotC)
  have hmemD := positiveActiveSet_subset_activeSet (hmemPos slotD)
  have hvalueNeg : chartObjective (chartPointOfDesign crux.design) < 0 :=
    crux.hasNegativeChartValue
  -- Shorthand for the frame quantities.
  have hentryOff : ∀ atomRow atomCol : Fin 6, atomRow ≠ atomCol →
      (chartPointOfDesign crux.design).chart atomRow atomCol
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomRow atomCol := by
    intro atomRow atomCol hne
    rw [chartStationaryGap, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hne, sub_zero]
  -- Layer 1: the equal squares of the four pair restrictions.
  have hannA := bothParallel_pairKernel_annihilated basisLabel hA12 hdetAB
    hvanishA
  have hannC := bothParallel_pairKernel_annihilated basisLabel hC12 hdetCD
    hvanishC
  have hXiA := assembly_mulVec_of_basis_transpose_zero hHform hannA
  have hXiC := assembly_mulVec_of_basis_transpose_zero hHform hannC
  have hsqA : tightDir (basisLabel slotA) atomA1 ^ 2
      = tightDir (basisLabel slotA) atomA2 ^ 2 := by
    rcases pair_coordinate_squares_eq hdata hHform hpsd hA12 hqA1 hqA2 hXiA
      with hcase | hcase
    · rw [hcase]
    · rw [hcase]
      ring
  have hsqC : tightDir (basisLabel slotC) atomC1 ^ 2
      = tightDir (basisLabel slotC) atomC2 ^ 2 := by
    rcases pair_coordinate_squares_eq hdata hHform hpsd hC12 hqC1 hqC2 hXiC
      with hcase | hcase
    · rw [hcase]
    · rw [hcase]
      ring
  have hsqB : tightDir (basisLabel slotB) atomA1 ^ 2
      = tightDir (basisLabel slotB) atomA2 ^ 2 := by
    have hcancel : (tightDir (basisLabel slotB) atomA2 ^ 2
        - tightDir (basisLabel slotB) atomA1 ^ 2)
        * tightDir (basisLabel slotA) atomA1 ^ 2 = 0 := by
      linear_combination (tightDir (basisLabel slotA) atomA1
            * tightDir (basisLabel slotB) atomA2
          + tightDir (basisLabel slotA) atomA2
            * tightDir (basisLabel slotB) atomA1) * hdetAB
        - tightDir (basisLabel slotB) atomA1 ^ 2 * hsqA
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqA1
  have hsqD : tightDir (basisLabel slotD) atomC1 ^ 2
      = tightDir (basisLabel slotD) atomC2 ^ 2 := by
    have hcancel : (tightDir (basisLabel slotD) atomC2 ^ 2
        - tightDir (basisLabel slotD) atomC1 ^ 2)
        * tightDir (basisLabel slotC) atomC1 ^ 2 = 0 := by
      linear_combination (tightDir (basisLabel slotC) atomC1
            * tightDir (basisLabel slotD) atomC2
          + tightDir (basisLabel slotC) atomC2
            * tightDir (basisLabel slotD) atomC1) * hdetCD
        - tightDir (basisLabel slotD) atomC1 ^ 2 * hsqC
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqC1
  -- Layer 2: the kernel rigidity reads of the two gap columns.
  obtain ⟨⟨hkaB, hkaD, hkaBalA, hkaBalC⟩, ⟨hkcB, hkcD, hkcBalA, hkcBalC⟩⟩ :=
    bothParallel_kernel_rigidity hdata basisLabel hleft hHform hker
      hAC.symm hBC.symm hCD hA12 hA1D hA2D hA1B hA2B hC12 hBC1.symm
      hBC2.symm hC1D hC2D hBD hsuppA hsuppB hsuppC hsuppD hdetAB hdetCD
      hvanishA hvanishC hqA1 hqBb hqD1
  -- The gap-entry forms of the four column reads.
  have hgAb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA1
        * tightDir (basisLabel slotA) atomA2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA2
        * tightDir (basisLabel slotA) atomA1 := by
    have h := pair_row_proportional_of_reads hA12 hkaB
    rw [hentryOff atomB atomA1 hA1B.symm, hentryOff atomB atomA2 hA2B.symm]
      at h
    linarith
  have hgAd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomA1
        * tightDir (basisLabel slotA) atomA2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomA2
        * tightDir (basisLabel slotA) atomA1 := by
    have h := pair_row_proportional_of_reads hA12 hkaD
    rw [hentryOff atomD atomA1 hA1D.symm, hentryOff atomD atomA2 hA2D.symm]
      at h
    linarith
  have hgCb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomC1
        * tightDir (basisLabel slotC) atomC2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomC2
        * tightDir (basisLabel slotC) atomC1 := by
    have h := pair_row_proportional_of_reads hC12 hkcB
    rw [hentryOff atomB atomC1 hBC1, hentryOff atomB atomC2 hBC2] at h
    linarith
  have hgCd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC1
        * tightDir (basisLabel slotC) atomC2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC2
        * tightDir (basisLabel slotC) atomC1 := by
    have h := pair_row_proportional_of_reads hC12 hkcD
    rw [hentryOff atomD atomC1 hC1D.symm, hentryOff atomD atomC2 hC2D.symm]
      at h
    linarith
  -- The ratio transfers to the other carrier of each pair.
  have hratioBb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA1
        * tightDir (basisLabel slotB) atomA2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA2
        * tightDir (basisLabel slotB) atomA1 := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1
          * tightDir (basisLabel slotB) atomA2
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA2
          * tightDir (basisLabel slotB) atomA1)
        * tightDir (basisLabel slotA) atomA1 = 0 := by
      linear_combination chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1 * hdetAB
        + tightDir (basisLabel slotB) atomA1 * hgAb
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqA1
  have hratioDd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC1
        * tightDir (basisLabel slotD) atomC2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC2
        * tightDir (basisLabel slotD) atomC1 := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1
          * tightDir (basisLabel slotD) atomC2
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC2
          * tightDir (basisLabel slotD) atomC1)
        * tightDir (basisLabel slotC) atomC1 = 0 := by
      linear_combination chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1 * hdetCD
        + tightDir (basisLabel slotD) atomC1 * hgCd
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqC1
  -- Layer 3: the four row laws.
  have hmemAd : atomD ∈ activeSubset (basisLabel slotA) :=
    datumTightSupport_subset hdata hmemA (mem_datumTightSupport.mpr hqAd)
  have hmemBb : atomB ∈ activeSubset (basisLabel slotB) :=
    datumTightSupport_subset hdata hmemB (mem_datumTightSupport.mpr hqBb)
  have hmemCb : atomB ∈ activeSubset (basisLabel slotC) :=
    datumTightSupport_subset hdata hmemC (mem_datumTightSupport.mpr hqCb)
  have hmemDd : atomD ∈ activeSubset (basisLabel slotD) :=
    datumTightSupport_subset hdata hmemD (mem_datumTightSupport.mpr hqDd)
  have hrowLawA := pair_row_gap_collapse hdata hmemA hA12 hA1D hA2D hmemAd
    hsuppA hqA1 hsqA hgAd
  have hrowLawB := pair_row_gap_collapse hdata hmemB hA12 hA1B hA2B hmemBb
    hsuppB hqB1 hsqB hratioBb
  have hrowLawC := pair_row_gap_collapse hdata hmemC hC12 hBC1.symm hBC2.symm
    hmemCb hsuppC hqC1 hsqC hgCb
  have hrowLawD := pair_row_gap_collapse hdata hmemD hC12 hC1D hC2D hmemDd
    hsuppD hqD1 hsqD hratioDd
  -- Layer 4: the two scale balances.
  have hmemA1a : atomA1 ∈ activeSubset (basisLabel slotA) :=
    datumTightSupport_subset hdata hmemA (mem_datumTightSupport.mpr hqA1)
  have hmemB1a : atomA1 ∈ activeSubset (basisLabel slotB) :=
    datumTightSupport_subset hdata hmemB (mem_datumTightSupport.mpr hqB1)
  have hmemC1c : atomC1 ∈ activeSubset (basisLabel slotC) :=
    datumTightSupport_subset hdata hmemC (mem_datumTightSupport.mpr hqC1)
  have hmemD1c : atomC1 ∈ activeSubset (basisLabel slotD) :=
    datumTightSupport_subset hdata hmemD (mem_datumTightSupport.mpr hqD1)
  have hS4 := bothParallel_scale_balance hdata hmemA hmemB hA12 hA1D hA2D
    hA1B hA2B hmemA1a hmemAd hmemB1a hmemBb hsuppA hsuppB hdetAB hqA1 hqB1
    hsqA hsqB hgAd hratioBb
  have hdetDC : tightDir (basisLabel slotD) atomC1
      * tightDir (basisLabel slotC) atomC2
    - tightDir (basisLabel slotD) atomC2
      * tightDir (basisLabel slotC) atomC1 = 0 := by
    linear_combination -hdetCD
  have hS5 := bothParallel_scale_balance hdata hmemD hmemC hC12 hC1D hC2D
    hBC1.symm hBC2.symm hmemD1c hmemDd hmemC1c hmemCb hsuppD hsuppC hdetDC
    hqD1 hqC1 hsqD hsqC hratioDd hgCb
  -- Layer 5: the four diagonal reads.
  have hDa1 : effectiveMultiplier activeSet activeWeight tightDir basisLabel
        slotA * tightDir (basisLabel slotA) atomA1 ^ 2
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotB
        * tightDir (basisLabel slotB) atomA1 ^ 2 = 1 / 6 := by
    have h := four_slot_diag_read hdata basisLabel hleft hmemPos hparallel
      hAB (atomIndex := atomA1)
      (fun slot h1 h2 => (hvanishA slot h1 h2).1)
    norm_num at h
    linarith [h]
  have hDb : effectiveMultiplier activeSet activeWeight tightDir basisLabel
        slotB * tightDir (basisLabel slotB) atomB ^ 2
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotC
        * tightDir (basisLabel slotC) atomB ^ 2 = 1 / 6 := by
    have h := four_slot_diag_read hdata basisLabel hleft hmemPos hparallel
      hBC (atomIndex := atomB) (fun slot h1 h2 => by
        rcases hslots slot with hcase | hcase | hcase | hcase
        · rw [hcase]
          exact hsuppA atomB hA1B.symm hA2B.symm hBD
        · exact absurd hcase h1
        · exact absurd hcase h2
        · rw [hcase]
          exact hsuppD atomB hBC1 hBC2 hBD)
    norm_num at h
    linarith [h]
  have hDc1 : effectiveMultiplier activeSet activeWeight tightDir basisLabel
        slotC * tightDir (basisLabel slotC) atomC1 ^ 2
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotD
        * tightDir (basisLabel slotD) atomC1 ^ 2 = 1 / 6 := by
    have h := four_slot_diag_read hdata basisLabel hleft hmemPos hparallel
      hCD (atomIndex := atomC1)
      (fun slot h1 h2 => (hvanishC slot h1 h2).1)
    norm_num at h
    linarith [h]
  have hDd : effectiveMultiplier activeSet activeWeight tightDir basisLabel
        slotA * tightDir (basisLabel slotA) atomD ^ 2
      + effectiveMultiplier activeSet activeWeight tightDir basisLabel slotD
        * tightDir (basisLabel slotD) atomD ^ 2 = 1 / 6 := by
    have h := four_slot_diag_read hdata basisLabel hleft hmemPos hparallel
      hAD (atomIndex := atomD) (fun slot h1 h2 => by
        rcases hslots slot with hcase | hcase | hcase | hcase
        · exact absurd hcase h1
        · rw [hcase]
          exact hsuppB atomD hA1D.symm hA2D.symm hBD.symm
        · rw [hcase]
          exact hsuppC atomD hC1D.symm hC2D.symm hBD.symm
        · exact absurd hcase h2)
    norm_num at h
    linarith [h]
  -- Layer 6: the four norms with the equal squares.
  have hnorm : ∀ (slot : Fin 4) (atomU atomV atomT : Fin 6),
      atomU ≠ atomV → atomU ≠ atomT → atomV ≠ atomT →
      (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        atomIndex ≠ atomT → tightDir (basisLabel slot) atomIndex = 0) →
      tightDir (basisLabel slot) atomU * tightDir (basisLabel slot) atomU
        + tightDir (basisLabel slot) atomV * tightDir (basisLabel slot) atomV
        + tightDir (basisLabel slot) atomT * tightDir (basisLabel slot) atomT
        = 1 := by
    intro slot atomU atomV atomT hUV hUT hVT hsupp
    have hunit := hdata.tightDir_unit (basisLabel slot)
      (positiveActiveSet_subset_activeSet (hmemPos slot))
    rw [dotProduct, triple_dot_collapse hUV hUT hVT hsupp] at hunit
    exact hunit
  have hNA : 2 * tightDir (basisLabel slotA) atomA1 ^ 2
      + tightDir (basisLabel slotA) atomD ^ 2 = 1 := by
    have h := hnorm slotA atomA1 atomA2 atomD hA12 hA1D hA2D hsuppA
    linear_combination h + hsqA
  have hNB : 2 * tightDir (basisLabel slotB) atomA1 ^ 2
      + tightDir (basisLabel slotB) atomB ^ 2 = 1 := by
    have h := hnorm slotB atomA1 atomA2 atomB hA12 hA1B hA2B hsuppB
    linear_combination h + hsqB
  have hNC : 2 * tightDir (basisLabel slotC) atomC1 ^ 2
      + tightDir (basisLabel slotC) atomB ^ 2 = 1 := by
    have h := hnorm slotC atomC1 atomC2 atomB hC12 hBC1.symm hBC2.symm hsuppC
    linear_combination h + hsqC
  have hND : 2 * tightDir (basisLabel slotD) atomC1 ^ 2
      + tightDir (basisLabel slotD) atomD ^ 2 = 1 := by
    have h := hnorm slotD atomC1 atomC2 atomD hC12 hC1D hC2D hsuppD
    linear_combination h + hsqD
  -- Layer 7: the two collapse cores.
  have hmPos : 0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomB
      - chartObjective (chartPointOfDesign crux.design) := by
    have := crux.chartGap_diagonal_pos atomB
    linarith
  have hnPos : 0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomD atomD
      - chartObjective (chartPointOfDesign crux.design) := by
    have := crux.chartGap_diagonal_pos atomD
    linarith
  have hS4' : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomD
        - chartObjective (chartPointOfDesign crux.design))
      * tightDir (basisLabel slotA) atomD ^ 2
      * tightDir (basisLabel slotB) atomA1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        * tightDir (basisLabel slotB) atomB ^ 2
        * tightDir (basisLabel slotA) atomA1 ^ 2 := hS4
  have hS5' : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomD
        - chartObjective (chartPointOfDesign crux.design))
      * tightDir (basisLabel slotD) atomD ^ 2
      * tightDir (basisLabel slotC) atomC1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        * tightDir (basisLabel slotC) atomB ^ 2
        * tightDir (basisLabel slotD) atomC1 ^ 2 := hS5
  -- Layer 3b: the chart diagonal reader and the pair sign scalars.
  have hPdiag : ∀ atomIndex : Fin 6,
      (chartPointOfDesign crux.design).chart atomIndex atomIndex
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomIndex atomIndex
          + (chartPointOfDesign crux.design).weight atomIndex := by
    intro atomIndex
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    ring
  have hatomExhaust : ∀ atomIndex : Fin 6, atomIndex = atomA1
      ∨ atomIndex = atomA2 ∨ atomIndex = atomB ∨ atomIndex = atomC1
      ∨ atomIndex = atomC2 ∨ atomIndex = atomD := by
    have hset : (Finset.univ : Finset (Fin 6))
        = {atomA1, atomA2, atomB, atomC1, atomC2, atomD} := by
      symm
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem (by
          simp [hA12, hA1B, hA1C1, hA1C2, hA1D]),
        Finset.card_insert_of_notMem (by simp [hA2B, hA2C1, hA2C2, hA2D]),
        Finset.card_insert_of_notMem (by simp [hBC1, hBC2, hBD]),
        Finset.card_insert_of_notMem (by simp [hC12, hC1D]),
        Finset.card_insert_of_notMem (by simp [hC2D]), Finset.card_singleton]
    intro atomIndex
    have hmem : atomIndex ∈ ({atomA1, atomA2, atomB, atomC1, atomC2,
        atomD} : Finset (Fin 6)) := by
      rw [← hset]
      exact Finset.mem_univ _
    simpa using hmem
  obtain ⟨sa, hsa2, hpA2⟩ := sign_of_sq_eq hsqA
  obtain ⟨sc, hsc2, hpC2⟩ := sign_of_sq_eq hsqC
  have hpB2 : tightDir (basisLabel slotB) atomA2 = sa * tightDir (basisLabel slotB) atomA1 := by
    have hcancel : (tightDir (basisLabel slotB) atomA2 - sa * tightDir (basisLabel slotB) atomA1) * tightDir (basisLabel slotA) atomA1 = 0 := by
      linear_combination hdetAB + tightDir (basisLabel slotB) atomA1 * hpA2
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqA1
  have hpD2 : tightDir (basisLabel slotD) atomC2 = sc * tightDir (basisLabel slotD) atomC1 := by
    have hcancel : (tightDir (basisLabel slotD) atomC2 - sc * tightDir (basisLabel slotD) atomC1) * tightDir (basisLabel slotC) atomC1 = 0 := by
      linear_combination hdetCD + tightDir (basisLabel slotD) atomC1 * hpC2
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqC1
  have hgA2B : chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA2 atomB
      = sa * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomB) := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA2 atomB
        - sa * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomB)) * tightDir (basisLabel slotA) atomA1 = 0 := by
      linear_combination -hgAb + (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomA1) * hpA2
        + tightDir (basisLabel slotA) atomA1 * gap_entry_symm hdata atomA2 atomB
        - sa * tightDir (basisLabel slotA) atomA1
          * gap_entry_symm hdata atomA1 atomB
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqA1
  have hgA2D : chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA2 atomD
      = sa * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomD) := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA2 atomD
        - sa * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomD)) * tightDir (basisLabel slotA) atomA1 = 0 := by
      linear_combination -hgAd + (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomD atomA1) * hpA2
        + tightDir (basisLabel slotA) atomA1 * gap_entry_symm hdata atomA2 atomD
        - sa * tightDir (basisLabel slotA) atomA1
          * gap_entry_symm hdata atomA1 atomD
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqA1
  have hgBC2 : chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomC2
      = sc * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomC1) := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomC2
        - sc * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomC1)) * tightDir (basisLabel slotC) atomC1 = 0 := by
      linear_combination -hgCb + (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomC1) * hpC2
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqC1
  have hgC2D : chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC2 atomD
      = sc * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomD) := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC2 atomD
        - sc * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomD)) * tightDir (basisLabel slotC) atomC1 = 0 := by
      linear_combination -hgCd + (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomD atomC1) * hpC2
        + tightDir (basisLabel slotC) atomC1 * gap_entry_symm hdata atomC2 atomD
        - sc * tightDir (basisLabel slotC) atomC1
          * gap_entry_symm hdata atomC1 atomD
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqC1
  -- Layer 3c: the pair diagonals, the twin weights, and the weight sum.
  have hmemA2a : atomA2 ∈ activeSubset (basisLabel slotA) :=
    datumTightSupport_subset hdata hmemA (mem_datumTightSupport.mpr hqA2)
  have hmemC2c : atomC2 ∈ activeSubset (basisLabel slotC) :=
    datumTightSupport_subset hdata hmemC (mem_datumTightSupport.mpr hqC2)
  have hgaaFold : chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA2 atomA2
      = chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomA1 :=
    (bothParallel_pair_diag_eq hdata hmemA hA12 hA1D hA2D hmemA1a hmemA2a
      hsuppA hqA1 hqA2 hsqA (by linear_combination hgAd)).symm
  have hgccFold : chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC2 atomC2
      = chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomC1 :=
    (bothParallel_pair_diag_eq hdata hmemC hC12 hBC1.symm hBC2.symm hmemC1c
      hmemC2c hsuppC hqC1 hqC2 hsqC (by linear_combination hgCb)).symm
  have hwaFold : (chartPointOfDesign crux.design).weight atomA2 = (chartPointOfDesign crux.design).weight atomA1 := by
    have htw := bothParallel_twin_weights hdata hA12 hqA1 hqA2 hsqA hkaBalA
    linear_combination -hPdiag atomA2 + hPdiag atomA1 - htw - hgaaFold
  have hwcFold : (chartPointOfDesign crux.design).weight atomC2 = (chartPointOfDesign crux.design).weight atomC1 := by
    have htw := bothParallel_twin_weights hdata hC12 hqC1 hqC2 hsqC hkcBalC
    linear_combination -hPdiag atomC2 + hPdiag atomC1 - htw - hgccFold
  have hweightSum := hdata.weight_sum_one
  rw [six_sum_univ_eq (f := fun atomIndex => (chartPointOfDesign crux.design).weight atomIndex)
    hA12 hA1B hA1C1 hA1C2 hA1D hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hC12
    hC1D hC2D] at hweightSum
  -- Layer 3d: the vanishing coordinates off each block.
  have hzAB : tightDir (basisLabel slotA) atomB = 0 := hsuppA atomB hA1B.symm hA2B.symm hBD
  have hzAC1 : tightDir (basisLabel slotA) atomC1 = 0 := hsuppA atomC1 hA1C1.symm hA2C1.symm hC1D
  have hzAC2 : tightDir (basisLabel slotA) atomC2 = 0 := hsuppA atomC2 hA1C2.symm hA2C2.symm hC2D
  have hzBC1 : tightDir (basisLabel slotB) atomC1 = 0 := hsuppB atomC1 hA1C1.symm hA2C1.symm hBC1.symm
  have hzBC2 : tightDir (basisLabel slotB) atomC2 = 0 := hsuppB atomC2 hA1C2.symm hA2C2.symm hBC2.symm
  have hzBD : tightDir (basisLabel slotB) atomD = 0 := hsuppB atomD hA1D.symm hA2D.symm hBD.symm
  have hzCA1 : tightDir (basisLabel slotC) atomA1 = 0 := hsuppC atomA1 hA1C1 hA1C2 hA1B
  have hzCA2 : tightDir (basisLabel slotC) atomA2 = 0 := hsuppC atomA2 hA2C1 hA2C2 hA2B
  have hzCD : tightDir (basisLabel slotC) atomD = 0 := hsuppC atomD hC1D.symm hC2D.symm hBD.symm
  have hzDA1 : tightDir (basisLabel slotD) atomA1 = 0 := hsuppD atomA1 hA1C1 hA1C2 hA1D
  have hzDA2 : tightDir (basisLabel slotD) atomA2 = 0 := hsuppD atomA2 hA2C1 hA2C2 hA2D
  have hzDB : tightDir (basisLabel slotD) atomB = 0 := hsuppD atomB hBC1 hBC2 hBD
  -- Layer 3e: the chart entry dictionary in the folded frame.
  have hPA1A1 : (chartPointOfDesign crux.design).chart atomA1 atomA1
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomA1)
          + (chartPointOfDesign crux.design).weight atomA1 := by
    linear_combination hPdiag atomA1
  have hPA1A2 : (chartPointOfDesign crux.design).chart atomA1 atomA2
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomA2 := by
    linear_combination hentryOff atomA1 atomA2 hA12
  have hPA1B : (chartPointOfDesign crux.design).chart atomA1 atomB
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomB := by
    linear_combination hentryOff atomA1 atomB hA1B
  have hPA1C1 : (chartPointOfDesign crux.design).chart atomA1 atomC1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomC1 := by
    linear_combination hentryOff atomA1 atomC1 hA1C1
  have hPA1C2 : (chartPointOfDesign crux.design).chart atomA1 atomC2
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomC2 := by
    linear_combination hentryOff atomA1 atomC2 hA1C2
  have hPA1D : (chartPointOfDesign crux.design).chart atomA1 atomD
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomD := by
    linear_combination hentryOff atomA1 atomD hA1D
  have hPA2A1 : (chartPointOfDesign crux.design).chart atomA2 atomA1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomA2 := by
    linear_combination hentryOff atomA2 atomA1 hA12.symm + gap_entry_symm hdata atomA2 atomA1
  have hPA2A2 : (chartPointOfDesign crux.design).chart atomA2 atomA2
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomA1)
          + (chartPointOfDesign crux.design).weight atomA1 := by
    linear_combination hPdiag atomA2 + hgaaFold + hwaFold
  have hPA2B : (chartPointOfDesign crux.design).chart atomA2 atomB
        = sa * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomB) := by
    linear_combination hentryOff atomA2 atomB hA2B + hgA2B
  have hPA2C1 : (chartPointOfDesign crux.design).chart atomA2 atomC1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA2 atomC1 := by
    linear_combination hentryOff atomA2 atomC1 hA2C1
  have hPA2C2 : (chartPointOfDesign crux.design).chart atomA2 atomC2
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA2 atomC2 := by
    linear_combination hentryOff atomA2 atomC2 hA2C2
  have hPA2D : (chartPointOfDesign crux.design).chart atomA2 atomD
        = sa * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomD) := by
    linear_combination hentryOff atomA2 atomD hA2D + hgA2D
  have hPBA1 : (chartPointOfDesign crux.design).chart atomB atomA1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomB := by
    linear_combination hentryOff atomB atomA1 hA1B.symm + gap_entry_symm hdata atomB atomA1
  have hPBA2 : (chartPointOfDesign crux.design).chart atomB atomA2
        = sa * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomB) := by
    linear_combination hentryOff atomB atomA2 hA2B.symm + gap_entry_symm hdata atomB atomA2 + hgA2B
  have hPBB : (chartPointOfDesign crux.design).chart atomB atomB
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB)
          + (chartPointOfDesign crux.design).weight atomB := by
    linear_combination hPdiag atomB
  have hPBC1 : (chartPointOfDesign crux.design).chart atomB atomC1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomC1 := by
    linear_combination hentryOff atomB atomC1 hBC1
  have hPBC2 : (chartPointOfDesign crux.design).chart atomB atomC2
        = sc * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomC1) := by
    linear_combination hentryOff atomB atomC2 hBC2 + hgBC2
  have hPBD : (chartPointOfDesign crux.design).chart atomB atomD
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomD := by
    linear_combination hentryOff atomB atomD hBD
  have hPC1A1 : (chartPointOfDesign crux.design).chart atomC1 atomA1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomC1 := by
    linear_combination hentryOff atomC1 atomA1 hA1C1.symm + gap_entry_symm hdata atomC1 atomA1
  have hPC1A2 : (chartPointOfDesign crux.design).chart atomC1 atomA2
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA2 atomC1 := by
    linear_combination hentryOff atomC1 atomA2 hA2C1.symm + gap_entry_symm hdata atomC1 atomA2
  have hPC1B : (chartPointOfDesign crux.design).chart atomC1 atomB
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomC1 := by
    linear_combination hentryOff atomC1 atomB hBC1.symm + gap_entry_symm hdata atomC1 atomB
  have hPC1C1 : (chartPointOfDesign crux.design).chart atomC1 atomC1
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomC1)
          + (chartPointOfDesign crux.design).weight atomC1 := by
    linear_combination hPdiag atomC1
  have hPC1C2 : (chartPointOfDesign crux.design).chart atomC1 atomC2
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomC2 := by
    linear_combination hentryOff atomC1 atomC2 hC12
  have hPC1D : (chartPointOfDesign crux.design).chart atomC1 atomD
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomD := by
    linear_combination hentryOff atomC1 atomD hC1D
  have hPC2A1 : (chartPointOfDesign crux.design).chart atomC2 atomA1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomC2 := by
    linear_combination hentryOff atomC2 atomA1 hA1C2.symm + gap_entry_symm hdata atomC2 atomA1
  have hPC2A2 : (chartPointOfDesign crux.design).chart atomC2 atomA2
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA2 atomC2 := by
    linear_combination hentryOff atomC2 atomA2 hA2C2.symm + gap_entry_symm hdata atomC2 atomA2
  have hPC2B : (chartPointOfDesign crux.design).chart atomC2 atomB
        = sc * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomC1) := by
    linear_combination hentryOff atomC2 atomB hBC2.symm + gap_entry_symm hdata atomC2 atomB + hgBC2
  have hPC2C1 : (chartPointOfDesign crux.design).chart atomC2 atomC1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomC2 := by
    linear_combination hentryOff atomC2 atomC1 hC12.symm + gap_entry_symm hdata atomC2 atomC1
  have hPC2C2 : (chartPointOfDesign crux.design).chart atomC2 atomC2
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomC1)
          + (chartPointOfDesign crux.design).weight atomC1 := by
    linear_combination hPdiag atomC2 + hgccFold + hwcFold
  have hPC2D : (chartPointOfDesign crux.design).chart atomC2 atomD
        = sc * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomD) := by
    linear_combination hentryOff atomC2 atomD hC2D + hgC2D
  have hPDA1 : (chartPointOfDesign crux.design).chart atomD atomA1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomD := by
    linear_combination hentryOff atomD atomA1 hA1D.symm + gap_entry_symm hdata atomD atomA1
  have hPDA2 : (chartPointOfDesign crux.design).chart atomD atomA2
        = sa * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomA1 atomD) := by
    linear_combination hentryOff atomD atomA2 hA2D.symm + gap_entry_symm hdata atomD atomA2 + hgA2D
  have hPDB : (chartPointOfDesign crux.design).chart atomD atomB
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomD := by
    linear_combination hentryOff atomD atomB hBD.symm + gap_entry_symm hdata atomD atomB
  have hPDC1 : (chartPointOfDesign crux.design).chart atomD atomC1
        = chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomD := by
    linear_combination hentryOff atomD atomC1 hC1D.symm + gap_entry_symm hdata atomD atomC1
  have hPDC2 : (chartPointOfDesign crux.design).chart atomD atomC2
        = sc * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomC1 atomD) := by
    linear_combination hentryOff atomD atomC2 hC2D.symm + gap_entry_symm hdata atomD atomC2 + hgC2D
  have hPDD : (chartPointOfDesign crux.design).chart atomD atomD
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD)
          + (chartPointOfDesign crux.design).weight atomD := by
    linear_combination hPdiag atomD
  -- Layer 3f: the four row laws and the two tight pair pins.
  have hROW1 : tightDir (basisLabel slotB) atomB
        * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomB - chartObjective (chartPointOfDesign crux.design))
      + 2 * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomB) * tightDir (basisLabel slotB) atomA1 = 0 := by
    linear_combination hrowLawB
      + 2 * tightDir (basisLabel slotB) atomA1 * gap_entry_symm hdata atomA1 atomB
  have hROW2 : tightDir (basisLabel slotA) atomD
        * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomD atomD - chartObjective (chartPointOfDesign crux.design))
      + 2 * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomD) * tightDir (basisLabel slotA) atomA1 = 0 := by
    linear_combination hrowLawA
      + 2 * tightDir (basisLabel slotA) atomA1 * gap_entry_symm hdata atomA1 atomD
  have hROW3 : 2 * tightDir (basisLabel slotC) atomC1 * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomC1)
      + tightDir (basisLabel slotC) atomB
        * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomB - chartObjective (chartPointOfDesign crux.design)) = 0 := by
    linear_combination hrowLawC
  have hROW4 : 2 * tightDir (basisLabel slotD) atomC1 * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomD)
      + tightDir (basisLabel slotD) atomD
        * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomD atomD - chartObjective (chartPointOfDesign crux.design)) = 0 := by
    linear_combination hrowLawD
      + 2 * tightDir (basisLabel slotD) atomC1 * gap_entry_symm hdata atomC1 atomD
  have htightB := gap_row_eigen_triple hdata hmemB hmemB1a hA12 hA1B hA2B
    hsuppB
  have htightC := gap_row_eigen_triple hdata hmemC hmemC1c hC12 hBC1.symm
    hBC2.symm hsuppC
  have hTA : 2 * tightDir (basisLabel slotB) atomA1 ^ 2
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomA1)
          + sa * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomA2) - chartObjective (chartPointOfDesign crux.design))
      - (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomB - chartObjective (chartPointOfDesign crux.design))
        * tightDir (basisLabel slotB) atomB ^ 2 = 0 := by
    linear_combination 2 * tightDir (basisLabel slotB) atomA1 * htightB
      - 2 * tightDir (basisLabel slotB) atomA1 * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomA2) * hpB2
      - tightDir (basisLabel slotB) atomB * hROW1
  have hTC : 2 * tightDir (basisLabel slotC) atomC1 ^ 2
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomC1)
          + sc * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomC2) - chartObjective (chartPointOfDesign crux.design))
      - (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomB - chartObjective (chartPointOfDesign crux.design))
        * tightDir (basisLabel slotC) atomB ^ 2 = 0 := by
    linear_combination 2 * tightDir (basisLabel slotC) atomC1 * htightC
      - 2 * tightDir (basisLabel slotC) atomC1 * (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomC2) * hpC2
      - tightDir (basisLabel slotC) atomB * hROW3
      - 2 * tightDir (basisLabel slotC) atomC1 * tightDir (basisLabel slotC) atomB
        * gap_entry_symm hdata atomC1 atomB
  -- Layer 3g: the projected columns of the four basis directions.
  have hmvA : ∀ atomRow : Fin 6,
      ((chartPointOfDesign crux.design).chart *ᵥ tightDir (basisLabel slotA)) atomRow
      = (chartPointOfDesign crux.design).chart atomRow atomA1 * tightDir (basisLabel slotA) atomA1
        + (chartPointOfDesign crux.design).chart atomRow atomA2 * tightDir (basisLabel slotA) atomA2
        + (chartPointOfDesign crux.design).chart atomRow atomD * tightDir (basisLabel slotA) atomD :=
    fun atomRow => mulVec_triple_read hA12 hA1D hA2D hsuppA atomRow
  have hmvB : ∀ atomRow : Fin 6,
      ((chartPointOfDesign crux.design).chart *ᵥ tightDir (basisLabel slotB)) atomRow
      = (chartPointOfDesign crux.design).chart atomRow atomA1 * tightDir (basisLabel slotB) atomA1
        + (chartPointOfDesign crux.design).chart atomRow atomA2 * tightDir (basisLabel slotB) atomA2
        + (chartPointOfDesign crux.design).chart atomRow atomB * tightDir (basisLabel slotB) atomB :=
    fun atomRow => mulVec_triple_read hA12 hA1B hA2B hsuppB atomRow
  have hmvC : ∀ atomRow : Fin 6,
      ((chartPointOfDesign crux.design).chart *ᵥ tightDir (basisLabel slotC)) atomRow
      = (chartPointOfDesign crux.design).chart atomRow atomC1 * tightDir (basisLabel slotC) atomC1
        + (chartPointOfDesign crux.design).chart atomRow atomC2 * tightDir (basisLabel slotC) atomC2
        + (chartPointOfDesign crux.design).chart atomRow atomB * tightDir (basisLabel slotC) atomB :=
    fun atomRow => mulVec_triple_read hC12 hBC1.symm hBC2.symm hsuppC atomRow
  have hmvD : ∀ atomRow : Fin 6,
      ((chartPointOfDesign crux.design).chart *ᵥ tightDir (basisLabel slotD)) atomRow
      = (chartPointOfDesign crux.design).chart atomRow atomC1 * tightDir (basisLabel slotD) atomC1
        + (chartPointOfDesign crux.design).chart atomRow atomC2 * tightDir (basisLabel slotD) atomC2
        + (chartPointOfDesign crux.design).chart atomRow atomD * tightDir (basisLabel slotD) atomD :=
    fun atomRow => mulVec_triple_read hC12 hC1D hC2D hsuppD atomRow
  -- Layer 3h: the eight folded commutation entries.
  have hcomA1B := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomA1 atomB
  rw [hmvA atomA1, hmvA atomB, hmvB atomA1, hmvB atomB, hmvC atomA1,
    hmvC atomB, hmvD atomA1, hmvD atomB] at hcomA1B
  simp only [hpA2, hpB2, hpC2, hpD2, hzCA1, hzDA1, hzAB, hzDB, hPA1A1,
    hPBA1, hPA1A2, hPBA2, hPA1B, hPBB, hPA1C1, hPBC1, hPA1C2, hPBC2,
    hPA1D, hPBD] at hcomA1B
  have hcomA2B := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomA2 atomB
  rw [hmvA atomA2, hmvA atomB, hmvB atomA2, hmvB atomB, hmvC atomA2,
    hmvC atomB, hmvD atomA2, hmvD atomB] at hcomA2B
  simp only [hpA2, hpB2, hpC2, hpD2, hzCA2, hzDA2, hzAB, hzDB, hPA2A1,
    hPBA1, hPA2A2, hPBA2, hPA2B, hPBB, hPA2C1, hPBC1, hPA2C2, hPBC2,
    hPA2D, hPBD] at hcomA2B
  have hcomBC1 := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomB atomC1
  rw [hmvA atomB, hmvA atomC1, hmvB atomB, hmvB atomC1, hmvC atomB,
    hmvC atomC1, hmvD atomB, hmvD atomC1] at hcomBC1
  simp only [hpA2, hpB2, hpC2, hpD2, hzAB, hzDB, hzAC1, hzBC1, hPBA1,
    hPC1A1, hPBA2, hPC1A2, hPBB, hPC1B, hPBC1, hPC1C1, hPBC2, hPC1C2,
    hPBD, hPC1D] at hcomBC1
  have hcomBC2 := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomB atomC2
  rw [hmvA atomB, hmvA atomC2, hmvB atomB, hmvB atomC2, hmvC atomB,
    hmvC atomC2, hmvD atomB, hmvD atomC2] at hcomBC2
  simp only [hpA2, hpB2, hpC2, hpD2, hzAB, hzDB, hzAC2, hzBC2, hPBA1,
    hPC2A1, hPBA2, hPC2A2, hPBB, hPC2B, hPBC1, hPC2C1, hPBC2, hPC2C2,
    hPBD, hPC2D] at hcomBC2
  have hcomA1C1 := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomA1 atomC1
  rw [hmvA atomA1, hmvA atomC1, hmvB atomA1, hmvB atomC1, hmvC atomA1,
    hmvC atomC1, hmvD atomA1, hmvD atomC1] at hcomA1C1
  simp only [hpA2, hpB2, hpC2, hpD2, hzCA1, hzDA1, hzAC1, hzBC1, hPA1A1,
    hPC1A1, hPA1A2, hPC1A2, hPA1B, hPC1B, hPA1C1, hPC1C1, hPA1C2, hPC1C2,
    hPA1D, hPC1D] at hcomA1C1
  have hcomA1C2 := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomA1 atomC2
  rw [hmvA atomA1, hmvA atomC2, hmvB atomA1, hmvB atomC2, hmvC atomA1,
    hmvC atomC2, hmvD atomA1, hmvD atomC2] at hcomA1C2
  simp only [hpA2, hpB2, hpC2, hpD2, hzCA1, hzDA1, hzAC2, hzBC2, hPA1A1,
    hPC2A1, hPA1A2, hPC2A2, hPA1B, hPC2B, hPA1C1, hPC2C1, hPA1C2, hPC2C2,
    hPA1D, hPC2D] at hcomA1C2
  have hcomA2C1 := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomA2 atomC1
  rw [hmvA atomA2, hmvA atomC1, hmvB atomA2, hmvB atomC1, hmvC atomA2,
    hmvC atomC1, hmvD atomA2, hmvD atomC1] at hcomA2C1
  simp only [hpA2, hpB2, hpC2, hpD2, hzCA2, hzDA2, hzAC1, hzBC1, hPA2A1,
    hPC1A1, hPA2A2, hPC1A2, hPA2B, hPC1B, hPA2C1, hPC1C1, hPA2C2, hPC1C2,
    hPA2D, hPC1D] at hcomA2C1
  have hcomA2C2 := bothParallel_four_slot_commutation hdata basisLabel
    hleft hmemPos hparallel hAB hAC hAD hBC hBDslot hCD atomA2 atomC2
  rw [hmvA atomA2, hmvA atomC2, hmvB atomA2, hmvB atomC2, hmvC atomA2,
    hmvC atomC2, hmvD atomA2, hmvD atomC2] at hcomA2C2
  simp only [hpA2, hpB2, hpC2, hpD2, hzCA2, hzDA2, hzAC2, hzBC2, hPA2A1,
    hPC2A1, hPA2A2, hPC2A2, hPA2B, hPC2B, hPA2C1, hPC2C1, hPA2C2, hPC2C2,
    hPA2D, hPC2D] at hcomA2C2
  -- Layer 3i: the three folded idempotency entries.
  have hidmEntry : ∀ atomRow atomCol : Fin 6,
      (chartPointOfDesign crux.design).chart atomRow atomA1 * (chartPointOfDesign crux.design).chart atomA1 atomCol
      + (chartPointOfDesign crux.design).chart atomRow atomA2 * (chartPointOfDesign crux.design).chart atomA2 atomCol
      + (chartPointOfDesign crux.design).chart atomRow atomB * (chartPointOfDesign crux.design).chart atomB atomCol
      + (chartPointOfDesign crux.design).chart atomRow atomC1 * (chartPointOfDesign crux.design).chart atomC1 atomCol
      + (chartPointOfDesign crux.design).chart atomRow atomC2 * (chartPointOfDesign crux.design).chart atomC2 atomCol
      + (chartPointOfDesign crux.design).chart atomRow atomD * (chartPointOfDesign crux.design).chart atomD atomCol
      = (chartPointOfDesign crux.design).chart atomRow atomCol := by
    intro atomRow atomCol
    have hmul : ((chartPointOfDesign crux.design).chart * (chartPointOfDesign crux.design).chart) atomRow atomCol
        = (chartPointOfDesign crux.design).chart atomRow atomCol := by
      rw [hdata.isIdempotent]
    rw [Matrix.mul_apply] at hmul
    rw [six_sum_univ_eq (f := fun atomMid =>
      (chartPointOfDesign crux.design).chart atomRow atomMid * (chartPointOfDesign crux.design).chart atomMid atomCol)
      hA12 hA1B hA1C1 hA1C2 hA1D hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hC12
      hC1D hC2D] at hmul
    exact hmul
  have hidmA1B := hidmEntry atomA1 atomB
  simp only [hPA1A1, hPA1B, hPA1A2, hPA2B, hPBB, hPA1C1, hPC1B, hPA1C2,
    hPC2B, hPA1D, hPDB] at hidmA1B
  have hidmA1D := hidmEntry atomA1 atomD
  simp only [hPA1A1, hPA1D, hPA1A2, hPA2D, hPA1B, hPBD, hPA1C1, hPC1D,
    hPA1C2, hPC2D, hPDD] at hidmA1D
  have hidmBC1 := hidmEntry atomB atomC1
  simp only [hPBA1, hPA1C1, hPBA2, hPA2C1, hPBB, hPBC1, hPC1C1, hPBC2,
    hPC2C1, hPBD, hPDC1] at hidmBC1
  -- Layer 3j: the branch dichotomy of the two cross-pair products.
  have hnuBne : effectiveMultiplier activeSet activeWeight tightDir basisLabel slotB ≠ 0 :=
    ne_of_gt (effectiveMultiplier_pos (tightDir := tightDir)
      basisLabel slotB (hmemPos slotB))
  have hnuCne : effectiveMultiplier activeSet activeWeight tightDir basisLabel slotC ≠ 0 :=
    ne_of_gt (effectiveMultiplier_pos (tightDir := tightDir)
      basisLabel slotC (hmemPos slotC))
  have hsplit : ((tightDir (basisLabel slotA) atomD * tightDir (basisLabel slotC) atomB * tightDir (basisLabel slotB) atomA1 * tightDir (basisLabel slotD) atomC1) - (tightDir (basisLabel slotB) atomB * tightDir (basisLabel slotD) atomD * tightDir (basisLabel slotA) atomA1 * tightDir (basisLabel slotC) atomC1))
      * ((tightDir (basisLabel slotA) atomD * tightDir (basisLabel slotC) atomB * tightDir (basisLabel slotB) atomA1 * tightDir (basisLabel slotD) atomC1) + (tightDir (basisLabel slotB) atomB * tightDir (basisLabel slotD) atomD * tightDir (basisLabel slotA) atomA1 * tightDir (basisLabel slotC) atomC1)) = 0 := by
    have hprod : (chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomD atomD - chartObjective (chartPointOfDesign crux.design))
        * (((tightDir (basisLabel slotA) atomD * tightDir (basisLabel slotC) atomB * tightDir (basisLabel slotB) atomA1 * tightDir (basisLabel slotD) atomC1) - (tightDir (basisLabel slotB) atomB * tightDir (basisLabel slotD) atomD * tightDir (basisLabel slotA) atomA1 * tightDir (basisLabel slotC) atomC1))
          * ((tightDir (basisLabel slotA) atomD * tightDir (basisLabel slotC) atomB * tightDir (basisLabel slotB) atomA1 * tightDir (basisLabel slotD) atomC1) + (tightDir (basisLabel slotB) atomB * tightDir (basisLabel slotD) atomD * tightDir (basisLabel slotA) atomA1 * tightDir (basisLabel slotC) atomC1))) = 0 := by
      linear_combination tightDir (basisLabel slotC) atomB ^ 2 * tightDir (basisLabel slotD) atomC1 ^ 2 * hS4'
        - tightDir (basisLabel slotB) atomB ^ 2 * tightDir (basisLabel slotA) atomA1 ^ 2 * hS5'
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hnPos)
  rcases mul_eq_zero.mp hsplit with hcase | hcase
  · -- The dependent sign: the two concentrations are proportional.
    refine (false_of_bothParallel_concentrations_dependent basisLabel hleft
      hAC.symm hBC.symm hCD (atomB := atomB) (atomD := atomD)
      (concentration := tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1 • tightDir (basisLabel slotB))
      (concentration' := tightDir (basisLabel slotD) atomC1 • tightDir (basisLabel slotC)
        - tightDir (basisLabel slotC) atomC1 • tightDir (basisLabel slotD))
      rfl rfl ?_ ?_ ?_ ?_ hqD1).elim
    · intro atomIndex hneB hneD
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases hatomExhaust atomIndex with heq | heq | heq | heq | heq | heq
      · rw [heq]
        ring
      · rw [heq]
        linear_combination tightDir (basisLabel slotB) atomA1 * hpA2 - tightDir (basisLabel slotA) atomA1 * hpB2
      · exact absurd heq hneB
      · rw [heq, hzAC1, hzBC1]
        ring
      · rw [heq, hzAC2, hzBC2]
        ring
      · exact absurd heq hneD
    · intro atomIndex hneB hneD
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rcases hatomExhaust atomIndex with heq | heq | heq | heq | heq | heq
      · rw [heq, hzCA1, hzDA1]
        ring
      · rw [heq, hzCA2, hzDA2]
        ring
      · exact absurd heq hneB
      · rw [heq]
        ring
      · rw [heq]
        linear_combination tightDir (basisLabel slotD) atomC1 * hpC2 - tightDir (basisLabel slotC) atomC1 * hpD2
      · exact absurd heq hneD
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hzAB, hzCD, hzBD, hzDB]
      linear_combination -hcase
    · have hval : (tightDir (basisLabel slotB) atomA1 • tightDir (basisLabel slotA)
        - tightDir (basisLabel slotA) atomA1 • tightDir (basisLabel slotB)) atomB
          = -(tightDir (basisLabel slotA) atomA1 * tightDir (basisLabel slotB) atomB) := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination tightDir (basisLabel slotB) atomA1 * hzAB
      rw [hval]
      exact neg_ne_zero.mpr (mul_ne_zero hqA1 hqBb)
  · -- The independent sign: the scalar certificate closes the pin.
    exact crossPin_scalar_kill
      (p1 := tightDir (basisLabel slotA) atomA1) (r1 := tightDir (basisLabel slotB) atomA1)
      (c1 := tightDir (basisLabel slotC) atomC1) (d1 := tightDir (basisLabel slotD) atomC1)
      (aD := tightDir (basisLabel slotA) atomD) (bB := tightDir (basisLabel slotB) atomB)
      (cB := tightDir (basisLabel slotC) atomB) (dD := tightDir (basisLabel slotD) atomD)
      (sa := sa) (sc := sc)
      (m := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomB - chartObjective (chartPointOfDesign crux.design))
      (n := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomD atomD - chartObjective (chartPointOfDesign crux.design))
      (Gv := chartObjective (chartPointOfDesign crux.design))
      (nuA := effectiveMultiplier activeSet activeWeight tightDir basisLabel slotA) (nuB := effectiveMultiplier activeSet activeWeight tightDir basisLabel slotB)
      (nuC := effectiveMultiplier activeSet activeWeight tightDir basisLabel slotC) (nuD := effectiveMultiplier activeSet activeWeight tightDir basisLabel slotD)
      (gbd := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomD)
      (gaa1 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomA1)
      (ga12 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomA2)
      (gcc1 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomC1)
      (gc12 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomC2)
      (X11 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomC1)
      (X12 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomC2)
      (X21 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA2 atomC1)
      (X22 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA2 atomC2)
      (g1 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomB) (g2 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomA1 atomD)
      (h1 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomB atomC1) (h2 := chartStationaryGap (chartPointOfDesign crux.design).chart (chartPointOfDesign crux.design).weight atomC1 atomD)
      (w0 := (chartPointOfDesign crux.design).weight atomA1) (wb := (chartPointOfDesign crux.design).weight atomB)
      (w3 := (chartPointOfDesign crux.design).weight atomC1) (wd := (chartPointOfDesign crux.design).weight atomD)
      hqA1 hqB1 hqC1 hqD1 hqAd hqBb hqCb hqDd
      (ne_of_gt hmPos) (ne_of_gt hnPos) hnuBne hnuCne
      (by linear_combination hsa2) (by linear_combination hsc2)
      (by linear_combination hDa1) (by linear_combination hDb)
      (by linear_combination hDc1) (by linear_combination hDd)
      (by linear_combination hNA) (by linear_combination hNB)
      (by linear_combination hND) (by linear_combination hS4')
      (by linear_combination hcase)
      (by linear_combination hweightSum - hwaFold - hwcFold)
      (by linear_combination hROW1) (by linear_combination hROW2)
      (by linear_combination hROW3) (by linear_combination hROW4)
      (by linear_combination hTA) (by linear_combination hTC)
      (by linear_combination hcomA1B) (by linear_combination hcomA2B)
      (by linear_combination hcomBC1) (by linear_combination hcomBC2)
      (by linear_combination hcomA1C1) (by linear_combination hcomA1C2)
      (by linear_combination hcomA2C1) (by linear_combination hcomA2C2)
      (by linear_combination hidmA1B) (by linear_combination hidmA1D)
      (by linear_combination hidmBC1)

/-! ## Layer 4 — closure five -/

/-- **CLOSURE FIVE.**  The rank-four both-parallel closure holds
unconditionally.  The cross pin and the landed circuit kill discharge
the two named obligations of the discharge theorem. -/
theorem rankFourBothParallelClosed_holds : RankFourBothParallelClosed :=
  rankFourBothParallelClosed_of_pins bothParallelCrossPinned_holds
    bothParallelCircuitClosed_holds

end Gtz
