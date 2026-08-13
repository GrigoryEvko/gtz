import Gtz.Wave.BothParallelCircuitCore
import Gtz.Wave.BothParallelDischarge
import Gtz.Wave.SupportTwoRayleighKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel circuit kill — pin two holds

The circuit obligation of closure five dies.  This module derives every
hypothesis of the scalar capstone from the landed projection laws and
consumes the capstone twice: once on the pair side and once on the
co-pair side through the mirror.  The zero-leak exit assembles the
projected kernel vector and fires the parallel-pair kill.

The chain:

1. The intake names the alive coordinates, the supports, and the
   distinctions from the share and support equations.
2. The kernel rigidity reads the two single columns, and the signed
   components collapse the pair coordinates.
3. The idempotency entries, the tight rows, the row laws, and the scale
   balances feed the scalar capstone.
4. The capstone refuses, or exits with a projected kernel vector that
   the parallel-pair kill refuses.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.bothParallelCircuitClosed_holds` — **PIN TWO.**

## Vacuity

The statement is vacuous if `Gtz.GtzWeighted 6 3` holds: no crux, no
frame.
-/

namespace Gtz

open Matrix

set_option maxHeartbeats 3200000 in
/-- **PIN TWO.**  At every both-parallel C4 frame datum, a positive label
alive at exactly the two single atoms dies. -/
theorem bothParallelCircuitClosed_holds : BothParallelCircuitClosed := by
  intro crux frame slotK slotL slotM slotN pairAtomOne pairAtomTwo
    coAtomOne coAtomTwo singleKM singleLN hmult hKL hMN hKM hKN hLM hLN
    hp12 hc12 hshareKL hshareMN hshareKM hshareLN hsuppSetK hsuppSetL
    hsuppSetM hsuppSetN hdetKL hdetMN label hmemP hb0 hd0 hsupp0 hthird
  -- The memberships and the negative value.
  have hmemA := positiveActiveSet_subset_activeSet (frame.hmem slotL)
  have hmemB := positiveActiveSet_subset_activeSet (frame.hmem slotK)
  have hmemC := positiveActiveSet_subset_activeSet (frame.hmem slotM)
  have hmemD := positiveActiveSet_subset_activeSet (frame.hmem slotN)
  have hmemE := positiveActiveSet_subset_activeSet hmemP
  have hG : chartObjective (chartPointOfDesign crux.design) < 0 :=
    crux.hasNegativeChartValue
  -- The entry dictionaries.
  have hentryOff : ∀ atomRow atomCol : Fin 6, atomRow ≠ atomCol →
      (chartPointOfDesign crux.design).chart atomRow atomCol
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomRow atomCol := by
    intro atomRow atomCol hne
    rw [chartStationaryGap, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hne, sub_zero]
  have hPdiag : ∀ atomRow : Fin 6,
      (chartPointOfDesign crux.design).chart atomRow atomRow
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomRow atomRow
          + (chartPointOfDesign crux.design).weight atomRow := by
    intro atomRow
    rw [chartStationaryGap, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    ring
  -- The alive coordinates from the support equations.
  have hmemSuppOf : ∀ (slot : Fin 4) (atomIndex : Fin 6),
      atomIndex ∈ datumTightSupport frame.tightDir (frame.basisLabel slot) →
      frame.tightDir (frame.basisLabel slot) atomIndex ≠ 0 := fun slot atom h =>
    mem_datumTightSupport.mp h
  have hqK1 : frame.tightDir (frame.basisLabel slotK) pairAtomOne ≠ 0 :=
    hmemSuppOf slotK pairAtomOne (by
      rw [hsuppSetK]
      exact Finset.mem_insert_self _ _)
  have hqK2 : frame.tightDir (frame.basisLabel slotK) pairAtomTwo ≠ 0 :=
    hmemSuppOf slotK pairAtomTwo (by
      rw [hsuppSetK]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hqKb : frame.tightDir (frame.basisLabel slotK) singleKM ≠ 0 :=
    hmemSuppOf slotK singleKM (by
      rw [hsuppSetK]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
  have hqL1 : frame.tightDir (frame.basisLabel slotL) pairAtomOne ≠ 0 :=
    hmemSuppOf slotL pairAtomOne (by
      rw [hsuppSetL]
      exact Finset.mem_insert_self _ _)
  have hqL2 : frame.tightDir (frame.basisLabel slotL) pairAtomTwo ≠ 0 :=
    hmemSuppOf slotL pairAtomTwo (by
      rw [hsuppSetL]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hqLd : frame.tightDir (frame.basisLabel slotL) singleLN ≠ 0 :=
    hmemSuppOf slotL singleLN (by
      rw [hsuppSetL]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
  have hqM1 : frame.tightDir (frame.basisLabel slotM) coAtomOne ≠ 0 :=
    hmemSuppOf slotM coAtomOne (by
      rw [hsuppSetM]
      exact Finset.mem_insert_self _ _)
  have hqM2 : frame.tightDir (frame.basisLabel slotM) coAtomTwo ≠ 0 :=
    hmemSuppOf slotM coAtomTwo (by
      rw [hsuppSetM]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hqMb : frame.tightDir (frame.basisLabel slotM) singleKM ≠ 0 :=
    hmemSuppOf slotM singleKM (by
      rw [hsuppSetM]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
  have hqN1 : frame.tightDir (frame.basisLabel slotN) coAtomOne ≠ 0 :=
    hmemSuppOf slotN coAtomOne (by
      rw [hsuppSetN]
      exact Finset.mem_insert_self _ _)
  have hqN2 : frame.tightDir (frame.basisLabel slotN) coAtomTwo ≠ 0 :=
    hmemSuppOf slotN coAtomTwo (by
      rw [hsuppSetN]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hqNd : frame.tightDir (frame.basisLabel slotN) singleLN ≠ 0 :=
    hmemSuppOf slotN singleLN (by
      rw [hsuppSetN]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
  -- The support complements.
  have hcompl : ∀ (slot : Fin 4) (atomU atomV atomT : Fin 6),
      datumTightSupport frame.tightDir (frame.basisLabel slot)
        = {atomU, atomV, atomT} →
      ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        atomIndex ≠ atomT →
        frame.tightDir (frame.basisLabel slot) atomIndex = 0 := by
    intro slot atomU atomV atomT hset atomIndex h1 h2 h3
    by_contra hne
    have hmem : atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel slot) := mem_datumTightSupport.mpr hne
    rw [hset] at hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact h1 heq
    rcases Finset.mem_insert.mp hmem' with heq | hmem''
    · exact h2 heq
    · exact h3 (Finset.mem_singleton.mp hmem'')
  have hsuppK := hcompl slotK pairAtomOne pairAtomTwo singleKM hsuppSetK
  have hsuppL := hcompl slotL pairAtomOne pairAtomTwo singleLN hsuppSetL
  have hsuppM := hcompl slotM coAtomOne coAtomTwo singleKM hsuppSetM
  have hsuppN := hcompl slotN coAtomOne coAtomTwo singleLN hsuppSetN
  -- The share memberships.
  have hbShareK : singleKM ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotK) := mem_datumTightSupport.mpr hqKb
  have hbShareM : singleKM ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotM) := mem_datumTightSupport.mpr hqMb
  have hdShareL : singleLN ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotL) := mem_datumTightSupport.mpr hqLd
  have hdShareN : singleLN ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotN) := mem_datumTightSupport.mpr hqNd
  have hp1K : pairAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotK) := mem_datumTightSupport.mpr hqK1
  have hp1L : pairAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotL) := mem_datumTightSupport.mpr hqL1
  have hp2K : pairAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotK) := mem_datumTightSupport.mpr hqK2
  have hp2L : pairAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotL) := mem_datumTightSupport.mpr hqL2
  have hc1M : coAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotM) := mem_datumTightSupport.mpr hqM1
  have hc1N : coAtomOne ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotN) := mem_datumTightSupport.mpr hqN1
  have hc2M : coAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotM) := mem_datumTightSupport.mpr hqM2
  have hc2N : coAtomTwo ∈ datumTightSupport frame.tightDir
      (frame.basisLabel slotN) := mem_datumTightSupport.mpr hqN2
  -- The atom distinctions through the exclusive carriers.
  have hA1B : pairAtomOne ≠ singleKM :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm hp1K hp1L
      hbShareM
  have hA2B : pairAtomTwo ≠ singleKM :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm hp2K hp2L
      hbShareM
  have hA1C1 : pairAtomOne ≠ coAtomOne :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm hp1K hp1L hc1M
  have hA1C2 : pairAtomOne ≠ coAtomTwo :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm hp1K hp1L hc2M
  have hA2C1 : pairAtomTwo ≠ coAtomOne :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm hp2K hp2L hc1M
  have hA2C2 : pairAtomTwo ≠ coAtomTwo :=
    atom_ne_of_exclusive_carriers hmult hKL hKM.symm hLM.symm hp2K hp2L hc2M
  have hA1D : pairAtomOne ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hKL hKN.symm hLN.symm hp1K hp1L
      hdShareN
  have hA2D : pairAtomTwo ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hKL hKN.symm hLN.symm hp2K hp2L
      hdShareN
  have hBD : singleKM ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hKM hKN.symm hMN.symm hbShareK
      hbShareM hdShareN
  have hBC1 : singleKM ≠ coAtomOne :=
    atom_ne_of_exclusive_carriers hmult hKM hKN.symm hMN.symm hbShareK
      hbShareM hc1N
  have hBC2 : singleKM ≠ coAtomTwo :=
    atom_ne_of_exclusive_carriers hmult hKM hKN.symm hMN.symm hbShareK
      hbShareM hc2N
  have hC1D : coAtomOne ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hMN hLM hLN hc1M hc1N hdShareL
  have hC2D : coAtomTwo ≠ singleLN :=
    atom_ne_of_exclusive_carriers hmult hMN hLM hLN hc2M hc2N hdShareL
  -- The slot exhaustion and the atom exhaustion.
  have hslotCases : ∀ col : Fin 4, col = slotK ∨ col = slotL ∨ col = slotM
      ∨ col = slotN := by
    intro col
    have huniv := slot_quadruple_eq_univ hKL hKM hKN hLM hLN hMN
    have hmemCol : col ∈ ({slotK, slotL, slotM, slotN} : Finset (Fin 4)) := by
      rw [huniv]
      exact Finset.mem_univ col
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmemCol
  have hsix : ∀ z : Fin 6, z = pairAtomOne ∨ z = pairAtomTwo ∨ z = singleKM
      ∨ z = coAtomOne ∨ z = coAtomTwo ∨ z = singleLN := by
    intro z
    have hm2 := hmult z
    rw [basisSupportMultiplicity] at hm2
    have hpos : 0 < (Finset.univ.filter fun col =>
        z ∈ datumTightSupport frame.tightDir (frame.basisLabel col)).card := by
      rw [hm2]
      norm_num
    obtain ⟨col, hcolMem⟩ := Finset.card_pos.mp hpos
    have hzin := (Finset.mem_filter.mp hcolMem).2
    rcases hslotCases col with h | h | h | h
    · rw [h, hsuppSetK] at hzin
      rcases Finset.mem_insert.mp hzin with he | hzin'
      · exact Or.inl he
      rcases Finset.mem_insert.mp hzin' with he | hzin''
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp hzin'')))
    · rw [h, hsuppSetL] at hzin
      rcases Finset.mem_insert.mp hzin with he | hzin'
      · exact Or.inl he
      rcases Finset.mem_insert.mp hzin' with he | hzin''
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Finset.mem_singleton.mp hzin'')))))
    · rw [h, hsuppSetM] at hzin
      rcases Finset.mem_insert.mp hzin with he | hzin'
      · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
      rcases Finset.mem_insert.mp hzin' with he | hzin''
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp hzin'')))
    · rw [h, hsuppSetN] at hzin
      rcases Finset.mem_insert.mp hzin with he | hzin'
      · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
      rcases Finset.mem_insert.mp hzin' with he | hzin''
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Finset.mem_singleton.mp hzin'')))))
  -- The pair vanishings of the other columns.
  have hvanishA : ∀ columnIndex, columnIndex ≠ slotL →
      columnIndex ≠ slotK →
      frame.tightDir (frame.basisLabel columnIndex) pairAtomOne = 0
        ∧ frame.tightDir (frame.basisLabel columnIndex) pairAtomTwo = 0 :=
    fun columnIndex h1 h2 =>
      ⟨shared_atom_exclusive_carriers frame.basisLabel hmult hKL hp1K hp1L
        h2 h1,
      shared_atom_exclusive_carriers frame.basisLabel hmult hKL hp2K hp2L
        h2 h1⟩
  have hvanishC : ∀ columnIndex, columnIndex ≠ slotM →
      columnIndex ≠ slotN →
      frame.tightDir (frame.basisLabel columnIndex) coAtomOne = 0
        ∧ frame.tightDir (frame.basisLabel columnIndex) coAtomTwo = 0 :=
    fun columnIndex h1 h2 =>
      ⟨shared_atom_exclusive_carriers frame.basisLabel hmult hMN hc1M hc1N
        h1 h2,
      shared_atom_exclusive_carriers frame.basisLabel hmult hMN hc2M hc2N
        h1 h2⟩
  -- The oriented determinants.
  have hdetAB : frame.tightDir (frame.basisLabel slotL) pairAtomOne
      * frame.tightDir (frame.basisLabel slotK) pairAtomTwo
    - frame.tightDir (frame.basisLabel slotL) pairAtomTwo
      * frame.tightDir (frame.basisLabel slotK) pairAtomOne = 0 := by
    linear_combination -hdetKL
  have hdetCD : frame.tightDir (frame.basisLabel slotM) coAtomOne
      * frame.tightDir (frame.basisLabel slotN) coAtomTwo
    - frame.tightDir (frame.basisLabel slotM) coAtomTwo
      * frame.tightDir (frame.basisLabel slotN) coAtomOne = 0 := hdetMN
  -- Layer 1: the equal squares of the four pair restrictions.
  have hannA := bothParallel_pairKernel_annihilated frame.basisLabel hp12
    hdetAB hvanishA
  have hannC := bothParallel_pairKernel_annihilated frame.basisLabel hc12
    hdetCD hvanishC
  have hXiA := assembly_mulVec_of_basis_transpose_zero frame.hHform hannA
  have hXiC := assembly_mulVec_of_basis_transpose_zero frame.hHform hannC
  have hsqA : frame.tightDir (frame.basisLabel slotL) pairAtomOne ^ 2
      = frame.tightDir (frame.basisLabel slotL) pairAtomTwo ^ 2 := by
    rcases pair_coordinate_squares_eq frame.hdata frame.hHform frame.hpsd
      hp12 hqL1 hqL2 hXiA with hcase | hcase
    · rw [hcase]
    · rw [hcase]
      ring
  have hsqC : frame.tightDir (frame.basisLabel slotM) coAtomOne ^ 2
      = frame.tightDir (frame.basisLabel slotM) coAtomTwo ^ 2 := by
    rcases pair_coordinate_squares_eq frame.hdata frame.hHform frame.hpsd
      hc12 hqM1 hqM2 hXiC with hcase | hcase
    · rw [hcase]
    · rw [hcase]
      ring
  have hsqB : frame.tightDir (frame.basisLabel slotK) pairAtomOne ^ 2
      = frame.tightDir (frame.basisLabel slotK) pairAtomTwo ^ 2 := by
    have hcancel : (frame.tightDir (frame.basisLabel slotK) pairAtomTwo ^ 2
        - frame.tightDir (frame.basisLabel slotK) pairAtomOne ^ 2)
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne ^ 2 = 0 := by
      linear_combination (frame.tightDir (frame.basisLabel slotL) pairAtomOne
            * frame.tightDir (frame.basisLabel slotK) pairAtomTwo
          + frame.tightDir (frame.basisLabel slotL) pairAtomTwo
            * frame.tightDir (frame.basisLabel slotK) pairAtomOne) * hdetAB
        - frame.tightDir (frame.basisLabel slotK) pairAtomOne ^ 2 * hsqA
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqL1
  have hsqD : frame.tightDir (frame.basisLabel slotN) coAtomOne ^ 2
      = frame.tightDir (frame.basisLabel slotN) coAtomTwo ^ 2 := by
    have hcancel : (frame.tightDir (frame.basisLabel slotN) coAtomTwo ^ 2
        - frame.tightDir (frame.basisLabel slotN) coAtomOne ^ 2)
        * frame.tightDir (frame.basisLabel slotM) coAtomOne ^ 2 = 0 := by
      linear_combination (frame.tightDir (frame.basisLabel slotM) coAtomOne
            * frame.tightDir (frame.basisLabel slotN) coAtomTwo
          + frame.tightDir (frame.basisLabel slotM) coAtomTwo
            * frame.tightDir (frame.basisLabel slotN) coAtomOne) * hdetCD
        - frame.tightDir (frame.basisLabel slotN) coAtomOne ^ 2 * hsqC
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hcase) hqM1
  -- Layer 2: the kernel rigidity reads of the two gap columns.
  obtain ⟨⟨hkaB, hkaD, hkaBalA, hkaBalC⟩, ⟨hkcB, hkcD, hkcBalA, hkcBalC⟩⟩ :=
    bothParallel_kernel_rigidity frame.hdata frame.basisLabel frame.hleft
      frame.hHform frame.hker hLM.symm hKM.symm hMN hp12 hA1D hA2D hA1B hA2B
      hc12 hBC1.symm hBC2.symm hC1D hC2D hBD hsuppL hsuppK hsuppM hsuppN
      hdetAB hdetCD hvanishA hvanishC hqL1 hqKb hqN1
  -- The gap-entry forms of the four column reads.
  have hgAb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM pairAtomOne
        * frame.tightDir (frame.basisLabel slotL) pairAtomTwo
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM pairAtomTwo
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne := by
    have h := pair_row_proportional_of_reads hp12 hkaB
    rw [hentryOff singleKM pairAtomOne hA1B.symm,
      hentryOff singleKM pairAtomTwo hA2B.symm] at h
    linarith
  have hgAd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN pairAtomOne
        * frame.tightDir (frame.basisLabel slotL) pairAtomTwo
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN pairAtomTwo
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne := by
    have h := pair_row_proportional_of_reads hp12 hkaD
    rw [hentryOff singleLN pairAtomOne hA1D.symm,
      hentryOff singleLN pairAtomTwo hA2D.symm] at h
    linarith
  have hgCb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne
        * frame.tightDir (frame.basisLabel slotM) coAtomTwo
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        * frame.tightDir (frame.basisLabel slotM) coAtomOne := by
    have h := pair_row_proportional_of_reads hc12 hkcB
    rw [hentryOff singleKM coAtomOne hBC1, hentryOff singleKM coAtomTwo hBC2]
      at h
    linarith
  have hgCd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN coAtomOne
        * frame.tightDir (frame.basisLabel slotM) coAtomTwo
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN coAtomTwo
        * frame.tightDir (frame.basisLabel slotM) coAtomOne := by
    have h := pair_row_proportional_of_reads hc12 hkcD
    rw [hentryOff singleLN coAtomOne hC1D.symm,
      hentryOff singleLN coAtomTwo hC2D.symm] at h
    linarith
  -- The ratio transfers to the other carrier of each pair.
  have hratioBb : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM pairAtomOne
        * frame.tightDir (frame.basisLabel slotK) pairAtomTwo
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM pairAtomTwo
        * frame.tightDir (frame.basisLabel slotK) pairAtomOne := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM pairAtomOne
          * frame.tightDir (frame.basisLabel slotK) pairAtomTwo
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM pairAtomTwo
          * frame.tightDir (frame.basisLabel slotK) pairAtomOne)
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne = 0 := by
      linear_combination chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM pairAtomOne
          * hdetAB
        + frame.tightDir (frame.basisLabel slotK) pairAtomOne * hgAb
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqL1
  have hratioDd : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN coAtomOne
        * frame.tightDir (frame.basisLabel slotN) coAtomTwo
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN coAtomTwo
        * frame.tightDir (frame.basisLabel slotN) coAtomOne := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleLN coAtomOne
          * frame.tightDir (frame.basisLabel slotN) coAtomTwo
        - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleLN coAtomTwo
          * frame.tightDir (frame.basisLabel slotN) coAtomOne)
        * frame.tightDir (frame.basisLabel slotM) coAtomOne = 0 := by
      linear_combination chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleLN coAtomOne
          * hdetCD
        + frame.tightDir (frame.basisLabel slotN) coAtomOne * hgCd
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith [hcase]
    · exact absurd hcase hqM1
  -- Layer 3: the block memberships and the four row laws.
  have hmemAd : singleLN ∈ frame.activeSubset (frame.basisLabel slotL) :=
    datumTightSupport_subset frame.hdata hmemA
      (mem_datumTightSupport.mpr hqLd)
  have hmemBb : singleKM ∈ frame.activeSubset (frame.basisLabel slotK) :=
    datumTightSupport_subset frame.hdata hmemB
      (mem_datumTightSupport.mpr hqKb)
  have hmemCb : singleKM ∈ frame.activeSubset (frame.basisLabel slotM) :=
    datumTightSupport_subset frame.hdata hmemC
      (mem_datumTightSupport.mpr hqMb)
  have hmemDd : singleLN ∈ frame.activeSubset (frame.basisLabel slotN) :=
    datumTightSupport_subset frame.hdata hmemD
      (mem_datumTightSupport.mpr hqNd)
  have hmemA1a : pairAtomOne ∈ frame.activeSubset (frame.basisLabel slotL) :=
    datumTightSupport_subset frame.hdata hmemA
      (mem_datumTightSupport.mpr hqL1)
  have hmemA2a : pairAtomTwo ∈ frame.activeSubset (frame.basisLabel slotL) :=
    datumTightSupport_subset frame.hdata hmemA
      (mem_datumTightSupport.mpr hqL2)
  have hmemB1a : pairAtomOne ∈ frame.activeSubset (frame.basisLabel slotK) :=
    datumTightSupport_subset frame.hdata hmemB
      (mem_datumTightSupport.mpr hqK1)
  have hmemC1c : coAtomOne ∈ frame.activeSubset (frame.basisLabel slotM) :=
    datumTightSupport_subset frame.hdata hmemC
      (mem_datumTightSupport.mpr hqM1)
  have hmemC2c : coAtomTwo ∈ frame.activeSubset (frame.basisLabel slotM) :=
    datumTightSupport_subset frame.hdata hmemC
      (mem_datumTightSupport.mpr hqM2)
  have hmemD1c : coAtomOne ∈ frame.activeSubset (frame.basisLabel slotN) :=
    datumTightSupport_subset frame.hdata hmemD
      (mem_datumTightSupport.mpr hqN1)
  have hrowLawA := pair_row_gap_collapse frame.hdata hmemA hp12 hA1D hA2D
    hmemAd hsuppL hqL1 hsqA hgAd
  have hrowLawB := pair_row_gap_collapse frame.hdata hmemB hp12 hA1B hA2B
    hmemBb hsuppK hqK1 hsqB hratioBb
  have hrowLawC := pair_row_gap_collapse frame.hdata hmemC hc12 hBC1.symm
    hBC2.symm hmemCb hsuppM hqM1 hsqC hgCb
  have hrowLawD := pair_row_gap_collapse frame.hdata hmemD hc12 hC1D hC2D
    hmemDd hsuppN hqN1 hsqD hratioDd
  -- The gap symmetry instances.
  have hsyBA1 := gap_entry_symm frame.hdata singleKM pairAtomOne
  have hsyBA2 := gap_entry_symm frame.hdata singleKM pairAtomTwo
  have hsyDB := gap_entry_symm frame.hdata singleLN singleKM
  have hsyDA1 := gap_entry_symm frame.hdata singleLN pairAtomOne
  have hsyDA2 := gap_entry_symm frame.hdata singleLN pairAtomTwo
  have hsyC1B := gap_entry_symm frame.hdata coAtomOne singleKM
  have hsyC2B := gap_entry_symm frame.hdata coAtomTwo singleKM
  have hsyDC1 := gap_entry_symm frame.hdata singleLN coAtomOne
  have hsyDC2 := gap_entry_symm frame.hdata singleLN coAtomTwo
  have hsyC2C1 := gap_entry_symm frame.hdata coAtomTwo coAtomOne
  have hsyC1A1 := gap_entry_symm frame.hdata coAtomOne pairAtomOne
  have hsyC1A2 := gap_entry_symm frame.hdata coAtomOne pairAtomTwo
  -- The canonical row laws.
  have hRowB : 2 * frame.tightDir (frame.basisLabel slotK) pairAtomOne
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM
    = -((chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleKM
        - chartObjective (chartPointOfDesign crux.design))
      * frame.tightDir (frame.basisLabel slotK) singleKM) := by
    linear_combination hrowLawB
      - 2 * frame.tightDir (frame.basisLabel slotK) pairAtomOne * hsyBA1
  have hRowA : 2 * frame.tightDir (frame.basisLabel slotL) pairAtomOne
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN
    = -((chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN singleLN
        - chartObjective (chartPointOfDesign crux.design))
      * frame.tightDir (frame.basisLabel slotL) singleLN) := by
    linear_combination hrowLawA
      - 2 * frame.tightDir (frame.basisLabel slotL) pairAtomOne * hsyDA1
  have hRowC : 2 * frame.tightDir (frame.basisLabel slotM) coAtomOne
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne
    = -((chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleKM
        - chartObjective (chartPointOfDesign crux.design))
      * frame.tightDir (frame.basisLabel slotM) singleKM) := by
    linear_combination hrowLawC
  have hRowD : 2 * frame.tightDir (frame.basisLabel slotN) coAtomOne
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne singleLN
    = -((chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN singleLN
        - chartObjective (chartPointOfDesign crux.design))
      * frame.tightDir (frame.basisLabel slotN) singleLN) := by
    linear_combination hrowLawD
      - 2 * frame.tightDir (frame.basisLabel slotN) coAtomOne * hsyDC1
  -- Layer 4: the two scale balances.
  have hS4 := bothParallel_scale_balance frame.hdata hmemA hmemB hp12 hA1D
    hA2D hA1B hA2B hmemA1a hmemAd hmemB1a hmemBb hsuppL hsuppK hdetAB hqL1
    hqK1 hsqA hsqB hgAd hratioBb
  have hdetDC : frame.tightDir (frame.basisLabel slotN) coAtomOne
      * frame.tightDir (frame.basisLabel slotM) coAtomTwo
    - frame.tightDir (frame.basisLabel slotN) coAtomTwo
      * frame.tightDir (frame.basisLabel slotM) coAtomOne = 0 := by
    linear_combination -hdetCD
  have hS5 := bothParallel_scale_balance frame.hdata hmemD hmemC hc12 hC1D
    hC2D hBC1.symm hBC2.symm hmemD1c hmemDd hmemC1c hmemCb hsuppN hsuppM
    hdetDC hqN1 hqM1 hsqD hsqC hratioDd hgCb
  -- The twin weights of the two doubled pairs.
  have htwinPA := bothParallel_twin_weights frame.hdata hp12 hqL1 hqL2 hsqA
    hkaBalA
  have htwinGA := bothParallel_pair_diag_eq frame.hdata hmemA hp12 hA1D hA2D
    hmemA1a hmemA2a hsuppL hqL1 hqL2 hsqA (by linear_combination hgAd)
  have htwinA : (chartPointOfDesign crux.design).weight pairAtomOne
      = (chartPointOfDesign crux.design).weight pairAtomTwo := by
    have h1 := hPdiag pairAtomOne
    have h2 := hPdiag pairAtomTwo
    linarith [htwinPA, htwinGA]
  have htwinPC := bothParallel_twin_weights frame.hdata hc12 hqM1 hqM2 hsqC
    hkcBalC
  have htwinGC := bothParallel_pair_diag_eq frame.hdata hmemC hc12
    hBC1.symm hBC2.symm hmemC1c hmemC2c hsuppM hqM1 hqM2 hsqC
    (by linear_combination hgCb)
  have htwinC : (chartPointOfDesign crux.design).weight coAtomOne
      = (chartPointOfDesign crux.design).weight coAtomTwo := by
    have h1 := hPdiag coAtomOne
    have h2 := hPdiag coAtomTwo
    linarith [htwinPC, htwinGC]
  -- The four carrier tight rows.
  have hTightB1 := gap_row_eigen_triple frame.hdata hmemB hmemB1a hp12 hA1B
    hA2B hsuppK
  have hTightA1 := gap_row_eigen_triple frame.hdata hmemA hmemA1a hp12 hA1D
    hA2D hsuppL
  have hTightC1raw := gap_row_eigen_triple frame.hdata hmemC hmemC1c hc12
    hBC1.symm hBC2.symm hsuppM
  have hTightC1 : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne
        * frame.tightDir (frame.basisLabel slotM) singleKM
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne coAtomOne
        * frame.tightDir (frame.basisLabel slotM) coAtomOne
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne coAtomTwo
        * frame.tightDir (frame.basisLabel slotM) coAtomTwo
      = chartObjective (chartPointOfDesign crux.design)
        * frame.tightDir (frame.basisLabel slotM) coAtomOne := by
    linear_combination hTightC1raw
      - frame.tightDir (frame.basisLabel slotM) singleKM * hsyC1B
  have hTightD1 := gap_row_eigen_triple frame.hdata hmemD hmemD1c hc12 hC1D
    hC2D hsuppN
  -- The shifted diagonals are positive, the floors, and the weight facts.
  have hmPos : 0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight singleKM singleKM
      - chartObjective (chartPointOfDesign crux.design) := by
    have := crux.chartGap_diagonal_pos singleKM
    linarith
  have hnPos : 0 < chartStationaryGap (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight singleLN singleLN
      - chartObjective (chartPointOfDesign crux.design) := by
    have := crux.chartGap_diagonal_pos singleLN
    linarith
  have hdbFloor := capture_diagonal_nonneg_of_isChartStationaryData
    frame.hdata singleKM
  have hddFloor := capture_diagonal_nonneg_of_isChartStationaryData
    frame.hdata singleLN
  have hWS : (chartPointOfDesign crux.design).weight pairAtomOne
      + (chartPointOfDesign crux.design).weight pairAtomTwo
      + (chartPointOfDesign crux.design).weight singleKM
      + (chartPointOfDesign crux.design).weight coAtomOne
      + (chartPointOfDesign crux.design).weight coAtomTwo
      + (chartPointOfDesign crux.design).weight singleLN = 1 := by
    have hsum := frame.hdata.weight_sum_one
    rw [six_sum_univ_eq (f := (chartPointOfDesign crux.design).weight)
      hp12 hA1B hA1C1 hA1C2 hA1D hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hc12
      hC1D hC2D] at hsum
    exact hsum
  have hwa1 := frame.hdata.weight_pos pairAtomOne
  have hwc1 := frame.hdata.weight_pos coAtomOne
  -- The circuit tight rows at the two single atoms.
  have hmemEb : singleKM ∈ frame.activeSubset label :=
    datumTightSupport_subset frame.hdata hmemE
      (mem_datumTightSupport.mpr hb0)
  have hmemEd : singleLN ∈ frame.activeSubset label :=
    datumTightSupport_subset frame.hdata hmemE
      (mem_datumTightSupport.mpr hd0)
  have hR1 : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleKM
        - chartObjective (chartPointOfDesign crux.design))
        * frame.tightDir label singleKM
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleLN
        * frame.tightDir label singleLN = 0 := by
    have h := gap_row_eigen_pair frame.hdata hmemE hmemEb hBD hsupp0
    linear_combination h
  have hR2 : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleLN
        * frame.tightDir label singleKM
      + (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleLN singleLN
        - chartObjective (chartPointOfDesign crux.design))
        * frame.tightDir label singleLN = 0 := by
    have h := gap_row_eigen_pair frame.hdata hmemE hmemEd hBD hsupp0
    linear_combination h - frame.tightDir label singleKM * hsyDB
  -- The signed components of the two parallel pairs.
  obtain ⟨sa, hsa, hp2⟩ := sign_of_sq_eq hsqA
  obtain ⟨sc, hsc, hc2⟩ := sign_of_sq_eq hsqC
  have hsaNe : sa ≠ 0 := by
    intro h
    rw [h] at hsa
    norm_num at hsa
  have hscNe : sc ≠ 0 := by
    intro h
    rw [h] at hsc
    norm_num at hsc
  have hr2 : frame.tightDir (frame.basisLabel slotK) pairAtomTwo
      = sa * frame.tightDir (frame.basisLabel slotK) pairAtomOne := by
    have hcancel : (frame.tightDir (frame.basisLabel slotK) pairAtomTwo
        - sa * frame.tightDir (frame.basisLabel slotK) pairAtomOne)
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne = 0 := by
      linear_combination hdetAB
        + frame.tightDir (frame.basisLabel slotK) pairAtomOne * hp2
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith
    · exact absurd hcase hqL1
  have hd2 : frame.tightDir (frame.basisLabel slotN) coAtomTwo
      = sc * frame.tightDir (frame.basisLabel slotN) coAtomOne := by
    have hcancel : (frame.tightDir (frame.basisLabel slotN) coAtomTwo
        - sc * frame.tightDir (frame.basisLabel slotN) coAtomOne)
        * frame.tightDir (frame.basisLabel slotM) coAtomOne = 0 := by
      linear_combination hdetCD
        + frame.tightDir (frame.basisLabel slotN) coAtomOne * hc2
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith
    · exact absurd hcase hqM1
  have hgb2c : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
      = sa * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
        - sa * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleKM)
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne = 0 := by
      linear_combination chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleKM
            * hp2
        - hgAb - hsyBA2 * frame.tightDir (frame.basisLabel slotL) pairAtomOne
        + frame.tightDir (frame.basisLabel slotL) pairAtomTwo * hsyBA1
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith
    · exact absurd hcase hqL1
  have hgd2c : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
      = sa * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
        - sa * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN)
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne = 0 := by
      linear_combination chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleLN
            * hp2
        - hgAd - hsyDA2 * frame.tightDir (frame.basisLabel slotL) pairAtomOne
        + frame.tightDir (frame.basisLabel slotL) pairAtomTwo * hsyDA1
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith
    · exact absurd hcase hqL1
  have hhb2c : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomTwo
      = sc * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        - sc * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne)
        * frame.tightDir (frame.basisLabel slotM) coAtomOne = 0 := by
      linear_combination chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM coAtomOne
            * hc2
        - hgCb
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith
    · exact absurd hcase hqM1
  have hhd2c : chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomTwo singleLN
      = sc * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne singleLN := by
    have hcancel : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN
        - sc * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN)
        * frame.tightDir (frame.basisLabel slotM) coAtomOne = 0 := by
      linear_combination chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight coAtomOne singleLN
            * hc2
        - hgCd - hsyDC2 * frame.tightDir (frame.basisLabel slotM) coAtomOne
        + frame.tightDir (frame.basisLabel slotM) coAtomTwo * hsyDC1
    rcases mul_eq_zero.mp hcancel with hcase | hcase
    · linarith
    · exact absurd hcase hqM1
  -- The idempotency entries over the six named atoms.
  have hidmEntry : ∀ atomRow atomCol : Fin 6,
      (chartPointOfDesign crux.design).chart atomRow pairAtomOne
        * (chartPointOfDesign crux.design).chart pairAtomOne atomCol
      + (chartPointOfDesign crux.design).chart atomRow pairAtomTwo
        * (chartPointOfDesign crux.design).chart pairAtomTwo atomCol
      + (chartPointOfDesign crux.design).chart atomRow singleKM
        * (chartPointOfDesign crux.design).chart singleKM atomCol
      + (chartPointOfDesign crux.design).chart atomRow coAtomOne
        * (chartPointOfDesign crux.design).chart coAtomOne atomCol
      + (chartPointOfDesign crux.design).chart atomRow coAtomTwo
        * (chartPointOfDesign crux.design).chart coAtomTwo atomCol
      + (chartPointOfDesign crux.design).chart atomRow singleLN
        * (chartPointOfDesign crux.design).chart singleLN atomCol
      = (chartPointOfDesign crux.design).chart atomRow atomCol := by
    intro atomRow atomCol
    have hmul : ((chartPointOfDesign crux.design).chart
        * (chartPointOfDesign crux.design).chart) atomRow atomCol
        = (chartPointOfDesign crux.design).chart atomRow atomCol := by
      rw [frame.hdata.isIdempotent]
    rw [Matrix.mul_apply] at hmul
    rw [six_sum_univ_eq (f := fun k =>
      (chartPointOfDesign crux.design).chart atomRow k
        * (chartPointOfDesign crux.design).chart k atomCol)
      hp12 hA1B hA1C1 hA1C2 hA1D hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD hc12
      hC1D hC2D] at hmul
    exact hmul
  have hIdmA1B : ((chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne pairAtomOne
        + (chartPointOfDesign crux.design).weight pairAtomOne)
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne pairAtomTwo
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleKM
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleKM)
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne coAtomTwo
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomTwo
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN)
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM := by
    have h := hidmEntry pairAtomOne singleKM
    rw [hPdiag pairAtomOne, hPdiag singleKM,
      hentryOff pairAtomOne singleKM hA1B,
      hentryOff pairAtomOne pairAtomTwo hp12,
      hentryOff pairAtomTwo singleKM hA2B,
      hentryOff pairAtomOne coAtomOne hA1C1,
      hentryOff coAtomOne singleKM hBC1.symm,
      hentryOff pairAtomOne coAtomTwo hA1C2,
      hentryOff coAtomTwo singleKM hBC2.symm,
      hentryOff pairAtomOne singleLN hA1D,
      hentryOff singleLN singleKM hBD.symm] at h
    linear_combination h
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
        * hsyC1B
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomTwo
        * hsyC2B
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        * hsyDB
  have hIdmA1D : ((chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne pairAtomOne
        + (chartPointOfDesign crux.design).weight pairAtomOne)
      * chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne pairAtomTwo
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne coAtomTwo
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleLN singleLN
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleLN))
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN := by
    have h := hidmEntry pairAtomOne singleLN
    rw [hPdiag pairAtomOne, hPdiag singleLN,
      hentryOff pairAtomOne singleLN hA1D,
      hentryOff pairAtomOne pairAtomTwo hp12,
      hentryOff pairAtomTwo singleLN hA2D,
      hentryOff pairAtomOne singleKM hA1B,
      hentryOff singleKM singleLN hBD,
      hentryOff pairAtomOne coAtomOne hA1C1,
      hentryOff coAtomOne singleLN hC1D,
      hentryOff pairAtomOne coAtomTwo hA1C2,
      hentryOff coAtomTwo singleLN hC2D] at h
    linear_combination h
  have hIdmBC1 : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo coAtomOne
      + ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleKM
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleKM)
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight coAtomOne coAtomOne
          + (chartPointOfDesign crux.design).weight coAtomOne)
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne coAtomTwo
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleLN
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN)
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne := by
    have h := hidmEntry singleKM coAtomOne
    rw [hPdiag singleKM, hPdiag coAtomOne,
      hentryOff singleKM coAtomOne hBC1,
      hentryOff singleKM pairAtomOne hA1B.symm,
      hentryOff pairAtomOne coAtomOne hA1C1,
      hentryOff singleKM pairAtomTwo hA2B.symm,
      hentryOff pairAtomTwo coAtomOne hA2C1,
      hentryOff singleKM coAtomTwo hBC2,
      hentryOff coAtomTwo coAtomOne hc12.symm,
      hentryOff singleKM singleLN hBD,
      hentryOff singleLN coAtomOne hC1D.symm] at h
    linear_combination h
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
        * hsyBA1
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo coAtomOne
        * hsyBA2
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        * hsyC2C1
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
        * hsyDC1
  have hIdmC1D : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomTwo coAtomOne
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
      + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne coAtomOne
          + (chartPointOfDesign crux.design).weight coAtomOne)
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne coAtomTwo
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne singleLN
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleLN singleLN
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleLN))
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne singleLN := by
    have h := hidmEntry coAtomOne singleLN
    rw [hPdiag coAtomOne, hPdiag singleLN,
      hentryOff coAtomOne singleLN hC1D,
      hentryOff coAtomOne pairAtomOne hA1C1.symm,
      hentryOff pairAtomOne singleLN hA1D,
      hentryOff coAtomOne pairAtomTwo hA2C1.symm,
      hentryOff pairAtomTwo singleLN hA2D,
      hentryOff coAtomOne singleKM hBC1.symm,
      hentryOff singleKM singleLN hBD,
      hentryOff coAtomOne coAtomTwo hc12,
      hentryOff coAtomTwo singleLN hC2D] at h
    linear_combination h
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        * hsyC1A1
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
        * hsyC1A2
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
        * hsyC1B
  have hIdmBB : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomTwo singleKM ^ 2
      + ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleKM
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleKM) ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomTwo ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleLN ^ 2)
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleKM
        - chartObjective (chartPointOfDesign crux.design))
        + chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight singleKM := by
    have h := hidmEntry singleKM singleKM
    rw [hPdiag singleKM,
      hentryOff singleKM pairAtomOne hA1B.symm,
      hentryOff pairAtomOne singleKM hA1B,
      hentryOff singleKM pairAtomTwo hA2B.symm,
      hentryOff pairAtomTwo singleKM hA2B,
      hentryOff singleKM coAtomOne hBC1,
      hentryOff coAtomOne singleKM hBC1.symm,
      hentryOff singleKM coAtomTwo hBC2,
      hentryOff coAtomTwo singleKM hBC2.symm,
      hentryOff singleKM singleLN hBD,
      hentryOff singleLN singleKM hBD.symm] at h
    linear_combination h
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleKM * hsyBA1
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleKM * hsyBA2
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne * hsyC1B
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomTwo * hsyC2B
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN * hsyDB
  have hIdmDD : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomTwo singleLN ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleLN ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne singleLN ^ 2
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomTwo singleLN ^ 2
      + ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleLN singleLN
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleLN) ^ 2)
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleLN singleLN
        - chartObjective (chartPointOfDesign crux.design))
        + chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight singleLN := by
    have h := hidmEntry singleLN singleLN
    rw [hPdiag singleLN,
      hentryOff singleLN pairAtomOne hA1D.symm,
      hentryOff pairAtomOne singleLN hA1D,
      hentryOff singleLN pairAtomTwo hA2D.symm,
      hentryOff pairAtomTwo singleLN hA2D,
      hentryOff singleLN singleKM hBD.symm,
      hentryOff singleKM singleLN hBD,
      hentryOff singleLN coAtomOne hC1D.symm,
      hentryOff coAtomOne singleLN hC1D,
      hentryOff singleLN coAtomTwo hC2D.symm,
      hentryOff coAtomTwo singleLN hC2D] at h
    linear_combination h
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN * hsyDA1
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN * hsyDA2
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN * hsyDB
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN * hsyDC1
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN * hsyDC2
  have hIdmBD : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
      + ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleKM
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleKM)
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleLN
        * ((chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleLN singleLN
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleLN))
      = chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM singleLN := by
    have h := hidmEntry singleKM singleLN
    rw [hPdiag singleKM, hPdiag singleLN,
      hentryOff singleKM singleLN hBD,
      hentryOff singleKM pairAtomOne hA1B.symm,
      hentryOff pairAtomOne singleLN hA1D,
      hentryOff singleKM pairAtomTwo hA2B.symm,
      hentryOff pairAtomTwo singleLN hA2D,
      hentryOff singleKM coAtomOne hBC1,
      hentryOff coAtomOne singleLN hC1D,
      hentryOff singleKM coAtomTwo hBC2,
      hentryOff coAtomTwo singleLN hC2D] at h
    linear_combination h
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        * hsyBA1
      - chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
        * hsyBA2
  -- The kernel exit: all leaks zero force the parallel-pair kill.
  have hkill : (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight singleKM = 0) →
      (chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight singleLN = 0) →
      (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleKM
          * frame.tightDir label singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
          * frame.tightDir label singleLN = 0) →
      (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne
          * frame.tightDir label singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
          * frame.tightDir label singleLN = 0) →
      False := by
    intro hdbz hddz hZa hZcLeak
    have hproj : (chartPointOfDesign crux.design).chart
        *ᵥ pairKernelVec (-(frame.tightDir label singleLN))
          (frame.tightDir label singleKM) singleKM singleLN = 0 := by
      funext atomRow
      rw [assembly_row_pairKernelVec hBD]
      show (chartPointOfDesign crux.design).chart atomRow singleKM
          * frame.tightDir label singleKM
        - (chartPointOfDesign crux.design).chart atomRow singleLN
          * -(frame.tightDir label singleLN) = 0
      rcases hsix atomRow with hy | hy | hy | hy | hy | hy
      · rw [hy]
        rw [hentryOff pairAtomOne singleKM hA1B,
          hentryOff pairAtomOne singleLN hA1D]
        linear_combination hZa
      · rw [hy]
        rw [hentryOff pairAtomTwo singleKM hA2B,
          hentryOff pairAtomTwo singleLN hA2D]
        linear_combination sa * hZa
          + frame.tightDir label singleKM * hgb2c
          + frame.tightDir label singleLN * hgd2c
      · rw [hy]
        rw [hPdiag singleKM, hentryOff singleKM singleLN hBD]
        linear_combination hR1
          + frame.tightDir label singleKM * hdbz
      · rw [hy]
        rw [hentryOff coAtomOne singleKM hBC1.symm,
          hentryOff coAtomOne singleLN hC1D]
        linear_combination hZcLeak
          + frame.tightDir label singleKM * hsyC1B
      · rw [hy]
        rw [hentryOff coAtomTwo singleKM hBC2.symm,
          hentryOff coAtomTwo singleLN hC2D]
        linear_combination sc * hZcLeak
          + frame.tightDir label singleKM * hsyC2B
          + frame.tightDir label singleKM * hhb2c
          + frame.tightDir label singleLN * hhd2c
      · rw [hy]
        rw [hentryOff singleLN singleKM hBD.symm, hPdiag singleLN]
        linear_combination hR2
          + frame.tightDir label singleLN * hddz
          + frame.tightDir label singleKM * hsyDB
    exact crux.false_of_projection_kernel_pair hBD hb0 hproj
  -- The third-row dichotomy: the annihilated row sits on one side.
  obtain ⟨atomThird, hzmem, hzb, hzd, hzrow⟩ := hthird
  have hmain : (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        * frame.tightDir label singleKM
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        * frame.tightDir label singleLN = 0)
      ∨ (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight singleKM coAtomOne
        * frame.tightDir label singleKM
      + chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight coAtomOne singleLN
        * frame.tightDir label singleLN = 0) := by
    rcases hsix atomThird with hz | hz | hz | hz | hz | hz
    · subst hz
      exact Or.inl hzrow
    · subst hz
      left
      have hlift : sa * (chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleKM
            * frame.tightDir label singleKM
          + chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleLN
            * frame.tightDir label singleLN) = 0 := by
        linear_combination hzrow
          - frame.tightDir label singleKM * hgb2c
          - frame.tightDir label singleLN * hgd2c
      rcases mul_eq_zero.mp hlift with hcase | hcase
      · exact absurd hcase hsaNe
      · exact hcase
    · exact absurd hz hzb
    · subst hz
      right
      linear_combination hzrow
        - frame.tightDir label singleKM * hsyC1B
    · subst hz
      right
      have hlift : sc * (chartStationaryGap
            (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM coAtomOne
            * frame.tightDir label singleKM
          + chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight coAtomOne singleLN
            * frame.tightDir label singleLN) = 0 := by
        linear_combination hzrow
          - frame.tightDir label singleKM * hsyC2B
          - frame.tightDir label singleKM * hhb2c
          - frame.tightDir label singleLN * hhd2c
      rcases mul_eq_zero.mp hlift with hcase | hcase
      · exact absurd hcase hscNe
      · exact hcase
    · exact absurd hz hzd
  rcases hmain with hZa | hZcRow
  · -- The pair side: the capstone at the direct orientation.
    obtain ⟨hdbz, hddz, htau0⟩ := circuit_scalar_kill hR1 hR2 hZa hRowB
      hRowA hRowC hRowD hsa hsc hgb2c hgd2c hhb2c hhd2c hr2 hc2 hTightB1
      hTightC1 hIdmA1B hIdmA1D hIdmBC1 hIdmC1D hIdmBB hIdmDD hIdmBD hS5
      hWS htwinA htwinC hwa1 hwc1 hmPos hnPos hG hdbFloor hddFloor hqL1
      hqK1 hqM1 hqN1 hqKb hqMb hb0 hd0
    exact hkill hdbz hddz hZa htau0
  · -- The co-pair side: the capstone through the mirror.
    have hR1m : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleLN singleLN
          - chartObjective (chartPointOfDesign crux.design))
          * frame.tightDir label singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
          * frame.tightDir label singleKM = 0 := by
      linear_combination hR2
    have hR2m : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
          * frame.tightDir label singleLN
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleKM
          - chartObjective (chartPointOfDesign crux.design))
          * frame.tightDir label singleKM = 0 := by
      linear_combination hR1
    have hZm : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
          * frame.tightDir label singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne
          * frame.tightDir label singleKM = 0 := by
      linear_combination hZcRow
    have hTightC1m : chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
          * frame.tightDir (frame.basisLabel slotL) singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne pairAtomOne
          * frame.tightDir (frame.basisLabel slotL) pairAtomOne
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne pairAtomTwo
          * frame.tightDir (frame.basisLabel slotL) pairAtomTwo
        = chartObjective (chartPointOfDesign crux.design)
          * frame.tightDir (frame.basisLabel slotL) pairAtomOne := by
      linear_combination hTightA1
    have hIdmA1Bm : ((chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne coAtomOne
          + (chartPointOfDesign crux.design).weight coAtomOne)
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne coAtomTwo
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight coAtomTwo singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleLN singleLN
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleLN)
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo coAtomOne
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleLN)
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN := by
      linear_combination hIdmC1D
    have hIdmA1Dm : ((chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne coAtomOne
          + (chartPointOfDesign crux.design).weight coAtomOne)
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne coAtomTwo
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo coAtomOne
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleKM singleKM
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleKM))
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne := by
      linear_combination hIdmBC1
    have hIdmBC1m : (chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne coAtomTwo
        + ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleLN singleLN
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleLN)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
          * (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight pairAtomOne pairAtomOne
            + (chartPointOfDesign crux.design).weight pairAtomOne)
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne pairAtomTwo
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleKM)
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN := by
      linear_combination hIdmA1D
    have hIdmC1Dm : (chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomOne
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM coAtomOne
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne coAtomTwo
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleLN
        + (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne pairAtomOne
          + (chartPointOfDesign crux.design).weight pairAtomOne)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne pairAtomTwo
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleKM
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleKM singleKM
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleKM))
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleKM := by
      linear_combination hIdmA1B
    have hIdmBBm : (chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN ^ 2
        + ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleLN singleLN
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleLN) ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN ^ 2)
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleLN singleLN
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleLN := by
      linear_combination hIdmDD
    have hIdmDDm : (chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomOne ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM coAtomTwo ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleKM ^ 2
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleKM ^ 2
        + ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleKM singleKM
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleKM) ^ 2)
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleKM
          - chartObjective (chartPointOfDesign crux.design))
          + chartObjective (chartPointOfDesign crux.design)
          + (chartPointOfDesign crux.design).weight singleKM := by
      linear_combination hIdmBB
    have hIdmBDm : (chartStationaryGap
          (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomOne singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM coAtomOne
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight coAtomTwo singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM coAtomTwo
        + ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleLN singleLN
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleLN)
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleLN
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomOne singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomTwo singleLN
          * chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight pairAtomTwo singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN
          * ((chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleKM singleKM
            - chartObjective (chartPointOfDesign crux.design))
            + chartObjective (chartPointOfDesign crux.design)
            + (chartPointOfDesign crux.design).weight singleKM))
        = chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleLN := by
      linear_combination hIdmBD
    have hS5m : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight singleKM singleKM
        - chartObjective (chartPointOfDesign crux.design))
        * frame.tightDir (frame.basisLabel slotK) singleKM ^ 2
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne ^ 2
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleLN singleLN
          - chartObjective (chartPointOfDesign crux.design))
          * frame.tightDir (frame.basisLabel slotL) singleLN ^ 2
          * frame.tightDir (frame.basisLabel slotK) pairAtomOne ^ 2 := by
      linear_combination -hS4
    have hWSm : (chartPointOfDesign crux.design).weight coAtomOne
        + (chartPointOfDesign crux.design).weight coAtomTwo
        + (chartPointOfDesign crux.design).weight singleLN
        + (chartPointOfDesign crux.design).weight pairAtomOne
        + (chartPointOfDesign crux.design).weight pairAtomTwo
        + (chartPointOfDesign crux.design).weight singleKM = 1 := by
      linear_combination hWS
    obtain ⟨hddz, hdbz, htau0⟩ := circuit_scalar_kill hR1m hR2m hZm hRowD
      hRowC hRowA hRowB hsc hsa hhd2c hhb2c hgd2c hgb2c hd2 hp2 hTightD1
      hTightC1m hIdmA1Bm hIdmA1Dm hIdmBC1m hIdmC1Dm hIdmBBm hIdmDDm
      hIdmBDm hS5m hWSm htwinC htwinA hwc1 hwa1 hnPos hmPos hG hddFloor
      hdbFloor hqM1 hqN1 hqL1 hqK1 hqNd hqLd hd0 hb0
    have hZa : chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleKM
          * frame.tightDir label singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight pairAtomOne singleLN
          * frame.tightDir label singleLN = 0 := by
      linear_combination htau0
    exact hkill hdbz hddz hZa hZcRow

end Gtz
