import Gtz.Wave.BothParallelSchurFinale
import Gtz.Wave.BothParallelKernelRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel diagonal kill — branch one dies at the finale

The trichotomy's parallel branch carries the diagonal core.  This module
derives every input of the Schur finale from the landed supply: the
equal squares, the kernel reads, the row laws, the scale balances, the
diagonal reads, the collapse masses, and the pinned cross entry.  The
finale then refuses the negative value.

The chain:

1. The pair kernel vectors are annihilated, and the equal-squares law
   prices the pair coordinates.
2. The kernel rigidity reads both gap columns of the single pair at
   every row, and the row laws collapse the four carrier rows.
3. The scale balances and the diagonal reads feed the two collapse
   cores: the two off-row square masses are polynomial in the shifted
   diagonals.
4. The commutation and idempotency entries pin the cross entry to zero.
5. The finale composes.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.SixThreeCrux.false_of_bothParallel_parallel_branch` — **THE
  BRANCH-ONE KILL.**

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

variable {activeIndex : Type}

/-- **THE CROSS-PIN OBLIGATION.**  At every both-parallel C4 stationary
datum whose positive labels are all parallel to basis directions, the
gap entry of the two single atoms vanishes.  The linear commutation
layer pins this entry at first order with a short support, and the
certificate lives in the thirteen entry equations.  The elimination
artifacts sit in the scratchpad (`c5fin_t1e*.pkl`). -/
def BothParallelCrossPinned : Prop :=
  ∀ (crux : SixThreeCrux) {activeIndex : Type}
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)},
    IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir →
    ∀ (basisLabel : Fin 4 → activeIndex)
      {leftInv : Matrix (Fin 4) (Fin 6) ℝ},
    leftInv * tightBasisColumns tightDir basisLabel = 1 →
    ∀ {gram : Matrix (Fin 4) (Fin 4) ℝ},
    tightBasisColumns tightDir basisLabel * gram
        * (tightBasisColumns tightDir basisLabel)ᵀ
      = chartMultiplierAssembly activeSet activeWeight tightDir →
    gram.PosSemidef →
    (∀ coeffVec : Fin 4 → ℝ, gram *ᵥ coeffVec = 0 → coeffVec = 0) →
    (∀ slot, basisLabel slot ∈ positiveActiveSet activeSet activeWeight) →
    (∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin 4) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot)) →
    ∀ {slotA slotB slotC slotD : Fin 4},
    (∀ slot : Fin 4, slot = slotA ∨ slot = slotB ∨ slot = slotC
      ∨ slot = slotD) →
    slotA ≠ slotB → slotA ≠ slotC → slotA ≠ slotD →
    slotB ≠ slotC → slotB ≠ slotD → slotC ≠ slotD →
    ∀ {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin 6},
    atomA1 ≠ atomA2 → atomA1 ≠ atomB → atomA1 ≠ atomC1 →
    atomA1 ≠ atomC2 → atomA1 ≠ atomD →
    atomA2 ≠ atomB → atomA2 ≠ atomC1 → atomA2 ≠ atomC2 → atomA2 ≠ atomD →
    atomB ≠ atomC1 → atomB ≠ atomC2 → atomB ≠ atomD →
    atomC1 ≠ atomC2 → atomC1 ≠ atomD → atomC2 ≠ atomD →
    (∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0) →
    (∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0) →
    (∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0) →
    (∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0) →
    tightDir (basisLabel slotA) atomA1 ≠ 0 →
    tightDir (basisLabel slotA) atomA2 ≠ 0 →
    tightDir (basisLabel slotA) atomD ≠ 0 →
    tightDir (basisLabel slotB) atomA1 ≠ 0 →
    tightDir (basisLabel slotB) atomA2 ≠ 0 →
    tightDir (basisLabel slotB) atomB ≠ 0 →
    tightDir (basisLabel slotC) atomC1 ≠ 0 →
    tightDir (basisLabel slotC) atomC2 ≠ 0 →
    tightDir (basisLabel slotC) atomB ≠ 0 →
    tightDir (basisLabel slotD) atomC1 ≠ 0 →
    tightDir (basisLabel slotD) atomC2 ≠ 0 →
    tightDir (basisLabel slotD) atomD ≠ 0 →
    tightDir (basisLabel slotA) atomA1 * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0 →
    tightDir (basisLabel slotC) atomC1 * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0 →
    (∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomA1 = 0
        ∧ tightDir (basisLabel columnIndex) atomA2 = 0) →
    (∀ columnIndex, columnIndex ≠ slotC → columnIndex ≠ slotD →
      tightDir (basisLabel columnIndex) atomC1 = 0
        ∧ tightDir (basisLabel columnIndex) atomC2 = 0) →
    chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomD = 0

set_option maxHeartbeats 3200000 in
/-- **THE BRANCH-ONE KILL.**  At a both-parallel C4 frame datum whose
positive labels are all parallel to basis directions, the diagonal core
collapses and the Schur finale refuses the negative value. -/
theorem SixThreeCrux.false_of_bothParallel_parallel_branch
    (crux : SixThreeCrux) (hpin : BothParallelCrossPinned)
    {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin 6 → ℝ)}
    (hdata : IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (basisLabel : Fin 4 → activeIndex)
    {leftInv : Matrix (Fin 4) (Fin 6) ℝ}
    (hleft : leftInv * tightBasisColumns tightDir basisLabel = 1)
    {gram : Matrix (Fin 4) (Fin 4) ℝ}
    (hHform : tightBasisColumns tightDir basisLabel * gram
          * (tightBasisColumns tightDir basisLabel)ᵀ
        = chartMultiplierAssembly activeSet activeWeight tightDir)
    (hpsd : gram.PosSemidef)
    (hker : ∀ coeffVec : Fin 4 → ℝ, gram *ᵥ coeffVec = 0 → coeffVec = 0)
    (hmemPos : ∀ slot, basisLabel slot
      ∈ positiveActiveSet activeSet activeWeight)
    (hparallel : ∀ label ∈ positiveActiveSet activeSet activeWeight,
      ∃ (slot : Fin 4) (scal : ℝ),
        tightDir label = scal • tightDir (basisLabel slot))
    {slotA slotB slotC slotD : Fin 4}
    (hslots : ∀ slot : Fin 4, slot = slotA ∨ slot = slotB ∨ slot = slotC
      ∨ slot = slotD)
    (hAB : slotA ≠ slotB) (hAC : slotA ≠ slotC) (hAD : slotA ≠ slotD)
    (hBC : slotB ≠ slotC) (hBDslot : slotB ≠ slotD) (hCD : slotC ≠ slotD)
    {atomA1 atomA2 atomB atomC1 atomC2 atomD : Fin 6}
    (hA12 : atomA1 ≠ atomA2) (hA1B : atomA1 ≠ atomB) (hA1C1 : atomA1 ≠ atomC1)
    (hA1C2 : atomA1 ≠ atomC2) (hA1D : atomA1 ≠ atomD)
    (hA2B : atomA2 ≠ atomB) (hA2C1 : atomA2 ≠ atomC1)
    (hA2C2 : atomA2 ≠ atomC2) (hA2D : atomA2 ≠ atomD)
    (hBC1 : atomB ≠ atomC1) (hBC2 : atomB ≠ atomC2) (hBD : atomB ≠ atomD)
    (hC12 : atomC1 ≠ atomC2) (hC1D : atomC1 ≠ atomD) (hC2D : atomC2 ≠ atomD)
    (hsuppA : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotA) atomIndex = 0)
    (hsuppB : ∀ atomIndex, atomIndex ≠ atomA1 → atomIndex ≠ atomA2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotB) atomIndex = 0)
    (hsuppC : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomB → tightDir (basisLabel slotC) atomIndex = 0)
    (hsuppD : ∀ atomIndex, atomIndex ≠ atomC1 → atomIndex ≠ atomC2 →
      atomIndex ≠ atomD → tightDir (basisLabel slotD) atomIndex = 0)
    (hqA1 : tightDir (basisLabel slotA) atomA1 ≠ 0)
    (hqA2 : tightDir (basisLabel slotA) atomA2 ≠ 0)
    (hqAd : tightDir (basisLabel slotA) atomD ≠ 0)
    (hqB1 : tightDir (basisLabel slotB) atomA1 ≠ 0)
    (hqB2 : tightDir (basisLabel slotB) atomA2 ≠ 0)
    (hqBb : tightDir (basisLabel slotB) atomB ≠ 0)
    (hqC1 : tightDir (basisLabel slotC) atomC1 ≠ 0)
    (hqC2 : tightDir (basisLabel slotC) atomC2 ≠ 0)
    (hqCb : tightDir (basisLabel slotC) atomB ≠ 0)
    (hqD1 : tightDir (basisLabel slotD) atomC1 ≠ 0)
    (hqD2 : tightDir (basisLabel slotD) atomC2 ≠ 0)
    (hqDd : tightDir (basisLabel slotD) atomD ≠ 0)
    (hdetAB : tightDir (basisLabel slotA) atomA1
        * tightDir (basisLabel slotB) atomA2
      - tightDir (basisLabel slotA) atomA2
        * tightDir (basisLabel slotB) atomA1 = 0)
    (hdetCD : tightDir (basisLabel slotC) atomC1
        * tightDir (basisLabel slotD) atomC2
      - tightDir (basisLabel slotC) atomC2
        * tightDir (basisLabel slotD) atomC1 = 0)
    (hvanishA : ∀ columnIndex, columnIndex ≠ slotA → columnIndex ≠ slotB →
      tightDir (basisLabel columnIndex) atomA1 = 0
        ∧ tightDir (basisLabel columnIndex) atomA2 = 0)
    (hvanishC : ∀ columnIndex, columnIndex ≠ slotC → columnIndex ≠ slotD →
      tightDir (basisLabel columnIndex) atomC1 = 0
        ∧ tightDir (basisLabel columnIndex) atomC2 = 0) :
    False := by
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
  have hcolB := collapse_core_b
    (x := tightDir (basisLabel slotA) atomA1 ^ 2)
    (X := tightDir (basisLabel slotA) atomD ^ 2)
    (W := tightDir (basisLabel slotB) atomA1 ^ 2)
    (B := tightDir (basisLabel slotB) atomB ^ 2)
    (y := tightDir (basisLabel slotC) atomC1 ^ 2)
    (C := tightDir (basisLabel slotC) atomB ^ 2)
    (V := tightDir (basisLabel slotD) atomC1 ^ 2)
    (Y := tightDir (basisLabel slotD) atomD ^ 2)
    (m := chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomB
      - chartObjective (chartPointOfDesign crux.design))
    (n := chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomD atomD
      - chartObjective (chartPointOfDesign crux.design))
    (nuA := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotA)
    (nuB := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotB)
    (nuC := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotC)
    (nuD := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotD)
    (pow_ne_zero 2 hqA1) (pow_ne_zero 2 hqC1) hmPos hnPos
    (by linarith [hNA]) (by linarith [hNB]) (by linarith [hNC])
    (by linarith [hND]) hS4' hS5' hDa1 hDb hDc1 hDd
  have hcolD := collapse_core_d
    (x := tightDir (basisLabel slotA) atomA1 ^ 2)
    (X := tightDir (basisLabel slotA) atomD ^ 2)
    (W := tightDir (basisLabel slotB) atomA1 ^ 2)
    (B := tightDir (basisLabel slotB) atomB ^ 2)
    (y := tightDir (basisLabel slotC) atomC1 ^ 2)
    (C := tightDir (basisLabel slotC) atomB ^ 2)
    (V := tightDir (basisLabel slotD) atomC1 ^ 2)
    (Y := tightDir (basisLabel slotD) atomD ^ 2)
    (m := chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomB
      - chartObjective (chartPointOfDesign crux.design))
    (n := chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomD atomD
      - chartObjective (chartPointOfDesign crux.design))
    (nuA := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotA)
    (nuB := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotB)
    (nuC := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotC)
    (nuD := effectiveMultiplier activeSet activeWeight tightDir basisLabel
      slotD)
    (pow_ne_zero 2 hqA1) (pow_ne_zero 2 hqC1) hmPos hnPos
    (by linarith [hNA]) (by linarith [hNB]) (by linarith [hNC])
    (by linarith [hND]) hS4' hS5' hDa1 hDb hDc1 hDd
  -- Layer 8: the pinned cross entry through the named obligation.
  have hcross : chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight atomB atomD = 0 :=
    hpin crux hdata basisLabel hleft hHform hpsd hker hmemPos hparallel
      hslots hAB hAC hAD hBC hBDslot hCD hA12 hA1B hA1C1 hA1C2 hA1D
      hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hC12 hC1D hC2D
      hsuppA hsuppB hsuppC hsuppD hqA1 hqA2 hqAd hqB1 hqB2 hqBb
      hqC1 hqC2 hqCb hqD1 hqD2 hqDd hdetAB hdetCD hvanishA hvanishC
  -- Layer 9: the entry squares and the two collapse masses.
  have hsqEntryAb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA2 ^ 2 := by
    have h2 : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1
          * tightDir (basisLabel slotA) atomA2) ^ 2
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA2
          * tightDir (basisLabel slotA) atomA1) ^ 2 := by
      rw [hgAb]
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA2 ^ 2)
        * tightDir (basisLabel slotA) atomA1 ^ 2 = 0 := by
      linear_combination h2 + chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2 * hsqA
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqA1
  have hsqEntryAd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomA2 ^ 2 := by
    have h2 : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA1
          * tightDir (basisLabel slotA) atomA2) ^ 2
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA2
          * tightDir (basisLabel slotA) atomA1) ^ 2 := by
      rw [hgAd]
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA2 ^ 2)
        * tightDir (basisLabel slotA) atomA1 ^ 2 = 0 := by
      linear_combination h2 + chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2 * hsqA
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqA1
  have hsqEntryCb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomC2 ^ 2 := by
    have h2 : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC1
          * tightDir (basisLabel slotC) atomC2) ^ 2
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC2
          * tightDir (basisLabel slotC) atomC1) ^ 2 := by
      rw [hgCb]
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC2 ^ 2)
        * tightDir (basisLabel slotC) atomC1 ^ 2 = 0 := by
      linear_combination h2 + chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2 * hsqC
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqC1
  have hsqEntryCd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC2 ^ 2 := by
    have h2 : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1
          * tightDir (basisLabel slotC) atomC2) ^ 2
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC2
          * tightDir (basisLabel slotC) atomC1) ^ 2 := by
      rw [hgCd]
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC2 ^ 2)
        * tightDir (basisLabel slotC) atomC1 ^ 2 = 0 := by
      linear_combination h2 + chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2 * hsqC
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqC1
  -- The squared row laws.
  have h4WB : 4 * tightDir (basisLabel slotB) atomA1 ^ 2
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design)) ^ 2
        * tightDir (basisLabel slotB) atomB ^ 2 := by
    linear_combination (2 * tightDir (basisLabel slotB) atomA1
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1
      + (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB)
        * tightDir (basisLabel slotB) atomB) * hrowLawB
  have h4yC : 4 * tightDir (basisLabel slotC) atomC1 ^ 2
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design)) ^ 2
        * tightDir (basisLabel slotC) atomB ^ 2 := by
    linear_combination (2 * tightDir (basisLabel slotC) atomC1
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC1
      + (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB)
        * tightDir (basisLabel slotC) atomB) * hrowLawC
  have h4xA : 4 * tightDir (basisLabel slotA) atomA1 ^ 2
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design)) ^ 2
        * tightDir (basisLabel slotA) atomD ^ 2 := by
    linear_combination (2 * tightDir (basisLabel slotA) atomA1
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA1
      + (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD)
        * tightDir (basisLabel slotA) atomD) * hrowLawA
  have h4VD : 4 * tightDir (basisLabel slotD) atomC1 ^ 2
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design)) ^ 2
        * tightDir (basisLabel slotD) atomD ^ 2 := by
    linear_combination (2 * tightDir (basisLabel slotD) atomC1
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1
      + (chartObjective (chartPointOfDesign crux.design)
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD)
        * tightDir (basisLabel slotD) atomD) * hrowLawD
  -- The two collapse masses.
  have hWpos : 0 < tightDir (basisLabel slotB) atomA1 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hqB1))
  have hypos : 0 < tightDir (basisLabel slotC) atomC1 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hqC1))
  have hxpos : 0 < tightDir (basisLabel slotA) atomA1 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hqA1))
  have hVpos : 0 < tightDir (basisLabel slotD) atomC1 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hqD1))
  have hSbHalf : 2 * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2
      + 2 * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design))) / 2 := by
    have hcancel : (2 * chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomA1 ^ 2
        + 2 * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomB atomC1 ^ 2
        - (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
              - chartObjective (chartPointOfDesign crux.design))
            + (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomD
              - chartObjective (chartPointOfDesign crux.design))) / 2)
        * (4 * (tightDir (basisLabel slotB) atomA1 ^ 2
          * tightDir (basisLabel slotC) atomC1 ^ 2)) = 0 := by
      linear_combination 2 * tightDir (basisLabel slotC) atomC1 ^ 2 * h4WB
        + 2 * tightDir (basisLabel slotB) atomA1 ^ 2 * h4yC
        + 2 * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
          - chartObjective (chartPointOfDesign crux.design)) * hcolB
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase (ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 4)
        (mul_pos hWpos hypos)))
  have hSdHalf : 2 * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2
      + 2 * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design))
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomB atomB
            - chartObjective (chartPointOfDesign crux.design))
          + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design))) / 2 := by
    have hcancel : (2 * chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomA1 ^ 2
        + 2 * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomD atomC1 ^ 2
        - (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
            - chartObjective (chartPointOfDesign crux.design))
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomB atomB
              - chartObjective (chartPointOfDesign crux.design))
            + (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomD atomD
              - chartObjective (chartPointOfDesign crux.design))) / 2)
        * (4 * (tightDir (basisLabel slotA) atomA1 ^ 2
          * tightDir (basisLabel slotD) atomC1 ^ 2)) = 0 := by
      linear_combination 2 * tightDir (basisLabel slotD) atomC1 ^ 2 * h4xA
        + 2 * tightDir (basisLabel slotA) atomA1 ^ 2 * h4VD
        + 2 * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomD atomD
          - chartObjective (chartPointOfDesign crux.design)) * hcolD
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase (ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 4)
        (mul_pos hxpos hVpos)))
  -- Layer 10: the finale.
  refine crux.false_of_bothParallel_finale hdata hA12 hA1B hA1C1 hA1C2 hA1D
    hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hC12 hC1D hC2D hvalueNeg hcross
    ?_ ?_
  · linarith [hsqEntryAb, hsqEntryCb, hSbHalf]
  · linarith [hsqEntryAd, hsqEntryCd, hSdHalf]

end Gtz
