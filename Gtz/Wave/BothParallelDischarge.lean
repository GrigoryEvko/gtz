import Gtz.Wave.BothParallelDiagonalKill
import Gtz.Wave.RankFourRungAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The both-parallel discharge — closure five holds

The labeled both-parallel cycle dies.  This module derives the C4
normal-form facts from the closure hypotheses, dispatches the extra
labels through the trichotomy, and routes the two branches: the
parallel branch to the diagonal kill, and the circuit branch to the
circuit kill.

The chain:

1. The share equations and the multiplicity name the six atoms, their
   distinctness, and the exhaustion of the atom universe.
2. The support equations give the complements and the alive
   coordinates.
3. The trichotomy classifies every positive label.
4. The parallel branch dies at the Schur finale.  The circuit branch
   dies at the sign clash.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.rankFourBothParallelClosed_holds` — **CLOSURE FIVE.**

## Vacuity

The statement is vacuous if `Gtz.GtzWeighted 6 3` holds: no crux, no
frame.
-/

namespace Gtz

open Matrix

/-- **THE CIRCUIT OBLIGATION.**  At every both-parallel C4 frame datum, a
positive label alive at exactly the two single atoms dies: the circuit
tight rows, the third-row annihilation, and the commutation entries
clash in sign.  The kill chain is banked: the third-atom row pins the
cross entry against one pair product, the opposite-side pin flips the
sign through the parallel branch relation, and the scale balance
refuses.  The elimination artifacts sit in the scratchpad
(`c5fin_circ.py`). -/
def BothParallelCircuitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux)
    (slotK slotL slotM slotN : Fin 4)
    (pairAtomOne pairAtomTwo coAtomOne coAtomTwo singleKM singleLN : Fin 6),
    (∀ atomIndex, basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex = 2) →
    slotK ≠ slotL → slotM ≠ slotN → slotK ≠ slotM → slotK ≠ slotN →
    slotL ≠ slotM → slotL ≠ slotN →
    pairAtomOne ≠ pairAtomTwo → coAtomOne ≠ coAtomTwo →
    shareSet frame.tightDir frame.basisLabel slotK slotL
      = {pairAtomOne, pairAtomTwo} →
    shareSet frame.tightDir frame.basisLabel slotM slotN
      = {coAtomOne, coAtomTwo} →
    shareSet frame.tightDir frame.basisLabel slotK slotM = {singleKM} →
    shareSet frame.tightDir frame.basisLabel slotL slotN = {singleLN} →
    datumTightSupport frame.tightDir (frame.basisLabel slotK)
      = {pairAtomOne, pairAtomTwo, singleKM} →
    datumTightSupport frame.tightDir (frame.basisLabel slotL)
      = {pairAtomOne, pairAtomTwo, singleLN} →
    datumTightSupport frame.tightDir (frame.basisLabel slotM)
      = {coAtomOne, coAtomTwo, singleKM} →
    datumTightSupport frame.tightDir (frame.basisLabel slotN)
      = {coAtomOne, coAtomTwo, singleLN} →
    frame.tightDir (frame.basisLabel slotK) pairAtomOne
        * frame.tightDir (frame.basisLabel slotL) pairAtomTwo
      - frame.tightDir (frame.basisLabel slotK) pairAtomTwo
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne = 0 →
    frame.tightDir (frame.basisLabel slotM) coAtomOne
        * frame.tightDir (frame.basisLabel slotN) coAtomTwo
      - frame.tightDir (frame.basisLabel slotM) coAtomTwo
        * frame.tightDir (frame.basisLabel slotN) coAtomOne = 0 →
    ∀ label ∈ positiveActiveSet frame.activeSet frame.reducedWeight,
    frame.tightDir label singleKM ≠ 0 →
    frame.tightDir label singleLN ≠ 0 →
    (∀ atomIndex, atomIndex ≠ singleKM → atomIndex ≠ singleLN →
      frame.tightDir label atomIndex = 0) →
    (∃ atomThird, atomThird ∈ frame.activeSubset label
      ∧ atomThird ≠ singleKM ∧ atomThird ≠ singleLN
      ∧ chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomThird singleKM
          * frame.tightDir label singleKM
        + chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomThird singleLN
          * frame.tightDir label singleLN = 0) →
    False

set_option maxHeartbeats 1600000 in
/-- **CLOSURE FIVE MODULO THE TWO PINS.**  The labeled cycle with both cross determinants
The labeled cycle with both cross determinants
zero dies at every rank-four frame, given the cross pin and the circuit
closure. -/
theorem rankFourBothParallelClosed_of_pins
    (hpin : BothParallelCrossPinned)
    (hcircuitClosed : BothParallelCircuitClosed) :
    RankFourBothParallelClosed := by
  intro crux frame slotK slotL slotM slotN pairAtomOne pairAtomTwo
    coAtomOne coAtomTwo singleKM singleLN hmult hKL hMN hKM hKN hLM hLN
    hp12 hc12 hshareKL hshareMN hshareKM hshareLN hsuppSetK hsuppSetL
    hsuppSetM hsuppSetN hdetKL hdetMN
  -- The supports and alive coordinates from the support equations.
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
  -- The fifteen atom distinctions through the exclusive carriers.
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
  have hvanishPairA : ∀ columnIndex, columnIndex ≠ slotL →
      columnIndex ≠ slotK →
      frame.tightDir (frame.basisLabel columnIndex) pairAtomOne = 0
        ∧ frame.tightDir (frame.basisLabel columnIndex) pairAtomTwo = 0 :=
    fun columnIndex h1 h2 =>
      ⟨shared_atom_exclusive_carriers frame.basisLabel hmult hKL hp1K hp1L
        h2 h1,
      shared_atom_exclusive_carriers frame.basisLabel hmult hKL hp2K hp2L
        h2 h1⟩
  have hvanishPairC : ∀ columnIndex, columnIndex ≠ slotM →
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
  -- The trichotomy over the positive labels.
  have hdiagNonneg : ∀ atomIndex : Fin 6,
      0 ≤ chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomIndex atomIndex :=
    fun atomIndex => (crux.chartGap_diagonal_pos atomIndex).le
  have htri : ∀ label ∈ positiveActiveSet frame.activeSet
      frame.reducedWeight,
      (∃ (slot : Fin 4) (scal : ℝ), frame.tightDir label
        = scal • frame.tightDir (frame.basisLabel slot))
      ∨ (frame.tightDir label singleKM ≠ 0
        ∧ frame.tightDir label singleLN ≠ 0
        ∧ (∀ atomIndex, atomIndex ≠ singleKM → atomIndex ≠ singleLN →
            frame.tightDir label atomIndex = 0)
        ∧ chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight singleKM singleLN ≠ 0
        ∧ (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleKM singleKM
            - chartObjective (chartPointOfDesign crux.design))
            * (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleLN singleLN
            - chartObjective (chartPointOfDesign crux.design))
          = chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight singleKM singleLN ^ 2
        ∧ ∃ atomThird, atomThird ∈ frame.activeSubset label
          ∧ atomThird ≠ singleKM ∧ atomThird ≠ singleLN
          ∧ chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomThird singleKM
              * frame.tightDir label singleKM
            + chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomThird singleLN
              * frame.tightDir label singleLN = 0) := by
    intro label hmemP
    exact bothParallel_extra_label_trichotomy frame.hdata frame.basisLabel
      rfl frame.hspan hKL.symm hMN (frame.hmemAll slotL)
      (frame.hmemAll slotK) (frame.hmemAll slotM) (frame.hmemAll slotN)
      hp12 hA1D hA2D hA1B hA2B hc12 hBC1.symm hBC2.symm hC1D hC2D hBD
      hA1C1 hA1C2 hA2C1 hA2C2 hsuppL hsuppK hsuppM hsuppN
      hqL1 hqL2 hqLd hqK1 hqK2 hqKb hqM1 hqM2 hqMb hqN1 hqN2 hqNd
      hdetAB hdetCD hvanishPairA hvanishPairC hsix frame.hvalueNeg
      hdiagNonneg (positiveActiveSet_subset_activeSet hmemP)
      (mem_positiveActiveSet.mp hmemP).2
  -- The branch split.
  have hslotsOrdered : ∀ slot : Fin 4, slot = slotL ∨ slot = slotK
      ∨ slot = slotM ∨ slot = slotN := by
    intro slot
    rcases hslotCases slot with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  by_cases hall : ∀ label ∈ positiveActiveSet frame.activeSet
      frame.reducedWeight,
      ∃ (slot : Fin 4) (scal : ℝ), frame.tightDir label
        = scal • frame.tightDir (frame.basisLabel slot)
  · -- Branch one: the diagonal kill.
    exact crux.false_of_bothParallel_parallel_branch hpin frame.hdata
      frame.basisLabel frame.hleft frame.hHform frame.hpsd frame.hker
      frame.hmem hall hslotsOrdered hKL.symm hLM hLN hKM hKN hMN
      hp12 hA1B hA1C1 hA1C2 hA1D hA2B hA2C1 hA2C2 hA2D hBC1 hBC2 hBD
      hc12 hC1D hC2D hsuppL hsuppK hsuppM hsuppN
      hqL1 hqL2 hqLd hqK1 hqK2 hqKb hqM1 hqM2 hqMb hqN1 hqN2 hqNd
      hdetAB hdetCD hvanishPairA hvanishPairC
  · -- Branch two: the circuit kill.
    push Not at hall
    obtain ⟨label, hmemP, hnotpar⟩ := hall
    rcases htri label hmemP with hpar | hcircuit
    · obtain ⟨slot, scal, hpar⟩ := hpar
      exact absurd hpar (hnotpar slot scal)
    · obtain ⟨hb0, hd0, hsupp0, hcrossNe, hproductLaw, hthird⟩ := hcircuit
      exact hcircuitClosed crux frame slotK slotL slotM slotN pairAtomOne
        pairAtomTwo coAtomOne coAtomTwo singleKM singleLN hmult hKL hMN
        hKM hKN hLM hLN hp12 hc12 hshareKL hshareMN hshareKM hshareLN
        hsuppSetK hsuppSetL hsuppSetM hsuppSetN hdetKL hdetMN label hmemP
        hb0 hd0 hsupp0 hthird

end Gtz
