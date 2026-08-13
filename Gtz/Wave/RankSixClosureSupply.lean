import Gtz.Wave.RankSixRungAssembly
import Gtz.Wave.RankFiveClosureSupply

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The rank-six closure supply — the pair reduction and the dense laws

Three payloads narrow the rank-six closures.  The first payload applies
THE SHARED-BLOCK CAP at the third rung: the landed rank-generic law
`false_of_spanning_tight_directions` gives the frame corollary that no
block carries three basis slots, and with the dense support law it also
refuses three equal supports.

The second payload ports the closure-one reduction.  The private-pair
kill, the same-pair kill, and the two bridges consume only rank-generic
supply, thus the rank-six closure one narrows to the SAME residual as the
rank-four and rank-five ones: the outer sharer, where some other basis
label carries a nonzero atom outside the pair.  One outer-sharer
certificate at the generic datum level discharges the support-two
closures of all three rungs through the parallel bridges.

The third payload lands the dense structure at rank six.  A full support
is its block.  Two doubled pairs leave at most two outside atoms, and
every outside atom is carried by BOTH remaining slots — the rank-six
weakening of the rank-five doubled-cover law, because six slots leave two
free carriers where five left one.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.RankSixFrame.false_of_three_slots_share_block` — the frame
  corollary of the shared-block cap.
* `Gtz.RankSixFrame.false_of_supportTwo_private_pair` — **THE
  PRIVATE-PAIR KILL** at rank six.
* `Gtz.rankSixSupportTwoClosed_of_shared_pair_kill` — the first bridge.
* `Gtz.RankSixFrame.false_of_samePair_columns` — **THE SAME-PAIR KILL**
  at rank six.
* `Gtz.rankSixSupportTwoClosed_of_outer_shared_kill` — **THE REFINED
  BRIDGE.**  Closure one at rank six is the outer sharer only.
* `Gtz.RankSixFrame.dense_support_eq_block` — a full support is its
  block.
* `Gtz.RankSixFrame.false_of_three_supports_equal` — no three equal
  card-3 supports.
* `Gtz.RankSixFrame.dense_two_doubled_pairs_cover` — **THE DOUBLED-PAIRS
  LAW.**  An atom outside two doubled supports is carried by both
  remaining slots.

## Vacuity

The frame statements are vacuous if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## The shared-block cap at rank six -/

/-- **THE RANK-SIX BLOCK CAP.**  No block of a rank-six frame carries
three basis slots: three independent directions would fill the block's
coordinate space and price the gap diagonal at the negative value. -/
theorem RankSixFrame.false_of_three_slots_share_block {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {slotOne slotTwo slotThree : Fin 6}
    (h12 : slotOne ≠ slotTwo) (h13 : slotOne ≠ slotThree)
    (h23 : slotTwo ≠ slotThree)
    (hblockTwo : frame.activeSubset (frame.basisLabel slotTwo)
      = frame.activeSubset (frame.basisLabel slotOne))
    (hblockThree : frame.activeSubset (frame.basisLabel slotThree)
      = frame.activeSubset (frame.basisLabel slotOne)) : False := by
  classical
  have hcard : (frame.activeSubset (frame.basisLabel slotOne)).card = 3 :=
    frame.hdata.activeSubset_card _ (frame.hmemAll slotOne)
  have hinjTriple : Function.Injective ![slotOne, slotTwo, slotThree] := by
    intro firstIndex secondIndex hcollide
    fin_cases firstIndex <;> fin_cases secondIndex
    · rfl
    · exact absurd hcollide h12
    · exact absurd hcollide h13
    · exact absurd hcollide.symm h12
    · rfl
    · exact absurd hcollide h23
    · exact absurd hcollide.symm h13
    · exact absurd hcollide.symm h23
    · rfl
  have hblockAll : ∀ tripleIndex : Fin 3,
      frame.activeSubset (frame.basisLabel (![slotOne, slotTwo, slotThree]
        tripleIndex)) = frame.activeSubset (frame.basisLabel slotOne) := by
    intro tripleIndex
    fin_cases tripleIndex
    · rfl
    · exact hblockTwo
    · exact hblockThree
  obtain ⟨floorAtom, hfloorMem⟩ : ∃ floorAtom,
      floorAtom ∈ frame.activeSubset (frame.basisLabel slotOne) :=
    Finset.card_pos.mp (by omega)
  refine false_of_spanning_tight_directions frame.hdata (by norm_num)
    (fun tripleIndex => frame.basisLabel (![slotOne, slotTwo, slotThree]
      tripleIndex))
    (fun tripleIndex => frame.hmemAll _)
    (frame.hindep.comp ![slotOne, slotTwo, slotThree] hinjTriple)
    hcard ?_ ?_ hfloorMem
    (crux.gap_diagonal_pos_of_allHeavy floorAtom) frame.hvalueNeg
  · intro tripleIndex atomIndex hnonzero
    have hmemBlock : atomIndex ∈ frame.activeSubset (frame.basisLabel
        (![slotOne, slotTwo, slotThree] tripleIndex)) := by
      by_contra hout
      exact hnonzero (frame.hdata.tightDir_support _ (frame.hmemAll _)
        atomIndex hout)
    rwa [hblockAll tripleIndex] at hmemBlock
  · intro tripleIndex
    rw [hblockAll tripleIndex]

/-! ## The rank-six private-pair kill -/

/-- **THE PRIVATE-PAIR KILL.**  A basis direction on a two-atom support
that no other basis label touches dies at every rank-six frame.  The
pair-kernel collapse aligns the capture on the pair, the squeeze zeroes
the two shifted weights, and the vanishing projected direction makes the
two design atoms parallel. -/
theorem RankSixFrame.false_of_supportTwo_private_pair {crux : SixThreeCrux}
    (frame : RankSixFrame crux) (columnIndex : Fin 6)
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hneU : frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0)
    (hneV : frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0)
    (hprivU : ∀ otherIndex, otherIndex ≠ columnIndex →
      frame.tightDir (frame.basisLabel otherIndex) atomU = 0)
    (hprivV : ∀ otherIndex, otherIndex ≠ columnIndex →
      frame.tightDir (frame.basisLabel otherIndex) atomV = 0) :
    False := by
  classical
  have hdata := frame.hdata
  have hmem := frame.hmemAll columnIndex
  have hvalueNeg := frame.hvalueNeg
  set pairDir := frame.tightDir (frame.basisLabel columnIndex) with hdirDef
  have hbasisKernel : (tightBasisColumns frame.tightDir frame.basisLabel)ᵀ
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 := by
    apply basis_transpose_mulVec_pairKernelVec hUV
    intro slotIndex
    by_cases hslot : slotIndex = columnIndex
    · subst hslot
      ring
    · rw [hprivU slotIndex hslot, hprivV slotIndex hslot]
      ring
  have hassemblyKernel : chartMultiplierAssembly frame.activeSet frame.reducedWeight
      frame.tightDir *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV
      = 0 :=
    assembly_mulVec_of_basis_transpose_zero frame.hHform hbasisKernel
  have hcaptureKernel : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir)
      *ᵥ pairKernelVec (pairDir atomU) (pairDir atomV) atomU atomV = 0 := by
    rw [← Matrix.mulVec_mulVec, hassemblyKernel, Matrix.mulVec_zero]
  have halignU : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomU * pairDir atomV
      - ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomV * pairDir atomU = 0 := by
    have hentry := congrFun hcaptureKernel atomU
    rwa [mulVec_pairKernelVec_apply ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) hUV (pairDir atomU)
      (pairDir atomV) atomU, Pi.zero_apply] at hentry
  have halignV : ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomU * pairDir atomV
      - ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomV * pairDir atomU = 0 := by
    have hentry := congrFun hcaptureKernel atomV
    rwa [mulVec_pairKernelVec_apply ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) hUV (pairDir atomU)
      (pairDir atomV) atomV, Pi.zero_apply] at hentry
  have hunit : pairDir atomU ^ 2 + pairDir atomV ^ 2 = 1 :=
    pair_support_unit_read hdata hmem hUV hsupp
  have hquadRead : pairDir ⬝ᵥ (((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) *ᵥ pairDir)
      = ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomU + ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomV := by
    rw [dotProduct_mulVec_of_pair_support ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) hUV hsupp]
    linear_combination (-(pairDir atomV)) * halignU + (pairDir atomU) * halignV
      + (((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomU atomU + ((chartPointOfDesign crux.design).chart
        * chartMultiplierAssembly frame.activeSet frame.reducedWeight frame.tightDir) atomV atomV) * hunit
  have hdiagU := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomU
  have hdiagV := diagonal_projection_mul_multiplier_of_isChartStationaryData
    hdata atomV
  have hrayleigh := capture_quadratic_le_of_isChartStationaryData hdata pairDir
  have henergy : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = chartObjective (chartPointOfDesign crux.design)
        + ((chartPointOfDesign crux.design).weight atomU * pairDir atomU ^ 2
          + (chartPointOfDesign crux.design).weight atomV * pairDir atomV ^ 2) := by
    have hread := tight_energy_read hdata hmem
    rw [hread, pair_support_energy_read hUV hsupp]
  have hfloorU := capture_diagonal_nonneg_of_isChartStationaryData hdata atomU
  have hfloorV := capture_diagonal_nonneg_of_isChartStationaryData hdata atomV
  have htraceFloor := capture_trace_nonneg_of_isChartStationaryData hdata
  have hinv : (0 : ℝ) < (((6 : ℕ) : ℝ))⁻¹ := by norm_num
  have hsqU : (0 : ℝ) < pairDir atomU ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneU))
  have hsqV : (0 : ℝ) < pairDir atomV ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hneV))
  have hbothZero : chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomU = 0
      ∧ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomV = 0 := by
    rcases le_total ((chartPointOfDesign crux.design).weight atomU)
      ((chartPointOfDesign crux.design).weight atomV) with horder | horder
    · exact support_two_capture_squeeze hvalueNeg hinv htraceFloor hfloorU
        hfloorV hsqU.le hsqV hunit henergy
        (by rw [hquadRead, hdiagU, hdiagV]; ring) hrayleigh horder
    · have hswap := support_two_capture_squeeze hvalueNeg hinv htraceFloor
        hfloorV hfloorU hsqV.le hsqU (by linarith [hunit])
        (by rw [henergy]; ring)
        (by rw [hquadRead, hdiagU, hdiagV]; ring) hrayleigh horder
      exact ⟨hswap.2, hswap.1⟩
  have henergyZero : pairDir ⬝ᵥ ((chartPointOfDesign crux.design).chart *ᵥ pairDir)
      = 0 := by
    rw [henergy]
    nlinarith [hbothZero.1, hbothZero.2, hunit]
  have hprojZero : (chartPointOfDesign crux.design).chart *ᵥ pairDir = 0 :=
    projection_mulVec_eq_zero_of_energy_eq_zero hdata henergyZero
  have hdirForm : pairDir
      = pairKernelVec (-(pairDir atomV)) (pairDir atomU) atomU atomV := by
    funext atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU
      rw [pairKernelVec_apply_one]
    by_cases hV : atomIndex = atomV
    · subst hV
      rw [pairKernelVec_apply_two hUV, neg_neg]
    · rw [hsupp atomIndex hU hV, pairKernelVec_apply_off hU hV]
  have hkernel : (chartPointOfDesign crux.design).chart
      *ᵥ pairKernelVec (-(pairDir atomV)) (pairDir atomU) atomU atomV = 0 := by
    rw [← hdirForm]
    exact hprojZero
  exact crux.false_of_projection_kernel_pair hUV hneU hkernel

/-- **THE FIRST BRIDGE.**  The rank-six support-two closure follows from
the shared-pair kill: the pair is private and dies here, or some other
basis label carries a pair atom. -/
theorem rankSixSupportTwoClosed_of_shared_pair_kill
    (killShared : ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux)
      (columnIndex otherIndex : Fin 6) (atomU atomV : Fin 6),
      (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
      atomU ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0 →
      frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0 →
      (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) →
      otherIndex ≠ columnIndex →
      (frame.tightDir (frame.basisLabel otherIndex) atomU ≠ 0
        ∨ frame.tightDir (frame.basisLabel otherIndex) atomV ≠ 0) →
      False) :
    RankSixSupportTwoClosed := by
  intro crux frame columnIndex hcard
  obtain ⟨atomU, atomV, hUV, hneU, hneV, hsupp⟩ :=
    exists_pair_of_support_card_two hcard
  by_cases hshared : ∃ otherIndex, otherIndex ≠ columnIndex ∧
      (frame.tightDir (frame.basisLabel otherIndex) atomU ≠ 0
        ∨ frame.tightDir (frame.basisLabel otherIndex) atomV ≠ 0)
  · obtain ⟨otherIndex, hne, hcarry⟩ := hshared
    exact killShared crux frame columnIndex otherIndex atomU atomV hcard hUV
      hneU hneV hsupp hne hcarry
  · push Not at hshared
    exact frame.false_of_supportTwo_private_pair columnIndex hUV hneU hneV hsupp
      (fun otherIndex hne => (hshared otherIndex hne).1)
      (fun otherIndex hne => (hshared otherIndex hne).2)

/-! ## The rank-six same-pair kill -/

/-- **THE SAME-PAIR KILL.**  Two distinct basis columns supported inside
one pair of atoms are impossible at a rank-six frame.  A zero column
breaks the unit norm.  A singleton column dies at the floor.  Two genuine
pair columns are independent through the left inverse, thus the two-atom
gap block is the value times the identity, and the floor kills the
diagonal. -/
theorem RankSixFrame.false_of_samePair_columns {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {colA colB : Fin 6} (hne : colB ≠ colA)
    {atomU atomV : Fin 6} (hUV : atomU ≠ atomV)
    (hAU : frame.tightDir (frame.basisLabel colA) atomU ≠ 0)
    (hAV : frame.tightDir (frame.basisLabel colA) atomV ≠ 0)
    (hAsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel colA) atomIndex = 0)
    (hBsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel colB) atomIndex = 0) : False := by
  by_cases hBU : frame.tightDir (frame.basisLabel colB) atomU = 0
  · by_cases hBV : frame.tightDir (frame.basisLabel colB) atomV = 0
    · have hzero : ∀ atomIndex, frame.tightDir (frame.basisLabel colB) atomIndex = 0 := by
        intro atomIndex
        by_cases hU : atomIndex = atomU
        · rw [hU]; exact hBU
        by_cases hV : atomIndex = atomV
        · rw [hV]; exact hBV
        · exact hBsupp atomIndex hU hV
      have hunit := frame.hdata.tightDir_unit _ (frame.hmemAll colB)
      have hsum : frame.tightDir (frame.basisLabel colB)
          ⬝ᵥ frame.tightDir (frame.basisLabel colB) = 0 := by
        show (∑ atomIndex : Fin 6, _ * _) = 0
        refine Finset.sum_eq_zero fun atomIndex _ => ?_
        rw [hzero atomIndex, mul_zero]
      rw [hsum] at hunit
      exact zero_ne_one hunit
    · refine false_of_singleton_tight_direction frame.hdata (frame.hmemAll colB)
        hBV (fun atomIndex hV => ?_)
        (crux.gap_diagonal_pos_of_allHeavy atomV) frame.hvalueNeg
      by_cases hU : atomIndex = atomU
      · rw [hU]; exact hBU
      · exact hBsupp atomIndex hU hV
  · by_cases hBV : frame.tightDir (frame.basisLabel colB) atomV = 0
    · refine false_of_singleton_tight_direction frame.hdata (frame.hmemAll colB)
        hBU (fun atomIndex hU => ?_)
        (crux.gap_diagonal_pos_of_allHeavy atomU) frame.hvalueNeg
      by_cases hV : atomIndex = atomV
      · rw [hV]; exact hBV
      · exact hBsupp atomIndex hU hV
    · have hmemAU : atomU ∈ frame.activeSubset (frame.basisLabel colA) := by
        by_contra hout
        exact hAU (frame.hdata.tightDir_support _ (frame.hmemAll colA) atomU hout)
      have hmemBU : atomU ∈ frame.activeSubset (frame.basisLabel colB) := by
        by_contra hout
        exact hBU (frame.hdata.tightDir_support _ (frame.hmemAll colB) atomU hout)
      have hrowAU := frame.hdata.tightDir_isTight _ (frame.hmemAll colA) atomU hmemAU
      have hrowBU := frame.hdata.tightDir_isTight _ (frame.hmemAll colB) atomU hmemBU
      rw [mulVec_apply_of_pair_support _ hUV hAsupp atomU] at hrowAU
      rw [mulVec_apply_of_pair_support _ hUV hBsupp atomU] at hrowBU
      by_cases hD : frame.tightDir (frame.basisLabel colA) atomU
            * frame.tightDir (frame.basisLabel colB) atomV
          - frame.tightDir (frame.basisLabel colA) atomV
            * frame.tightDir (frame.basisLabel colB) atomU = 0
      · have hratio : frame.tightDir (frame.basisLabel colB)
            = (frame.tightDir (frame.basisLabel colB) atomU
                / frame.tightDir (frame.basisLabel colA) atomU)
              • frame.tightDir (frame.basisLabel colA) := by
          funext atomIndex
          by_cases hU : atomIndex = atomU
          · subst hU
            rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hAU]
          by_cases hV : atomIndex = atomV
          · subst hV
            rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div,
              eq_div_iff hAU]
            linear_combination hD
          · rw [hBsupp atomIndex hU hV, Pi.smul_apply, smul_eq_mul,
              hAsupp atomIndex hU hV, mul_zero]
        have hentryB : (frame.leftInv
            * tightBasisColumns frame.tightDir frame.basisLabel) colB colB = 1 := by
          rw [frame.hleft, Matrix.one_apply_eq]
        have hentryA : (frame.leftInv
            * tightBasisColumns frame.tightDir frame.basisLabel) colB colA = 0 := by
          rw [frame.hleft]
          exact Matrix.one_apply_ne hne
        have hexpB : (frame.leftInv
              * tightBasisColumns frame.tightDir frame.basisLabel) colB colB
            = ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
                * frame.tightDir (frame.basisLabel colB) atomIndex := rfl
        have hexpA : (frame.leftInv
              * tightBasisColumns frame.tightDir frame.basisLabel) colB colA
            = ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
                * frame.tightDir (frame.basisLabel colA) atomIndex := rfl
        rw [hexpB] at hentryB
        rw [hexpA] at hentryA
        have hscaled : ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
              * frame.tightDir (frame.basisLabel colB) atomIndex
            = (frame.tightDir (frame.basisLabel colB) atomU
                / frame.tightDir (frame.basisLabel colA) atomU)
              * ∑ atomIndex : Fin 6, frame.leftInv colB atomIndex
                  * frame.tightDir (frame.basisLabel colA) atomIndex := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun atomIndex _ => ?_
          rw [congrFun hratio atomIndex, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hscaled, hentryA, mul_zero] at hentryB
        exact zero_ne_one hentryB
      · have helim : (chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomU atomU
              - chartObjective (chartPointOfDesign crux.design))
            * (frame.tightDir (frame.basisLabel colA) atomU
                * frame.tightDir (frame.basisLabel colB) atomV
              - frame.tightDir (frame.basisLabel colA) atomV
                * frame.tightDir (frame.basisLabel colB) atomU) = 0 := by
          linear_combination frame.tightDir (frame.basisLabel colB) atomV * hrowAU
            - frame.tightDir (frame.basisLabel colA) atomV * hrowBU
        rcases mul_eq_zero.mp helim with hzero | hzero
        · have hgap := sub_eq_zero.mp hzero
          have hfloor := crux.gap_diagonal_pos_of_allHeavy atomU
          rw [hgap] at hfloor
          exact absurd frame.hvalueNeg (by linarith)
        · exact hD hzero

/-- **THE REFINED BRIDGE.**  The rank-six support-two closure follows
from one residual: the outer sharer kill, where some other basis label
carries a nonzero atom outside the pair.  The inner sharers die here. -/
theorem rankSixSupportTwoClosed_of_outer_shared_kill
    (killOuter : ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux)
      (columnIndex otherIndex : Fin 6) (atomU atomV atomT : Fin 6),
      (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
      atomU ≠ atomV →
      frame.tightDir (frame.basisLabel columnIndex) atomU ≠ 0 →
      frame.tightDir (frame.basisLabel columnIndex) atomV ≠ 0 →
      (∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
        frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0) →
      otherIndex ≠ columnIndex →
      atomT ≠ atomU → atomT ≠ atomV →
      frame.tightDir (frame.basisLabel otherIndex) atomT ≠ 0 →
      False) :
    RankSixSupportTwoClosed := by
  refine rankSixSupportTwoClosed_of_shared_pair_kill ?_
  intro crux frame columnIndex otherIndex atomU atomV hcard hUV hneU hneV hsupp
    hneCol _hcarry
  by_cases houter : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      frame.tightDir (frame.basisLabel otherIndex) atomIndex = 0
  · exact frame.false_of_samePair_columns hneCol hUV hneU hneV hsupp houter
  · push Not at houter
    obtain ⟨atomT, hTU, hTV, hneT⟩ := houter
    exact killOuter crux frame columnIndex otherIndex atomU atomV atomT hcard
      hUV hneU hneV hsupp hneCol hTU hTV hneT

/-! ## The rank-six dense structure -/

/-- A full support of a rank-six frame is its block. -/
theorem RankSixFrame.dense_support_eq_block {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {columnIndex : Fin 6}
    (hcard : (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) :
    datumTightSupport frame.tightDir (frame.basisLabel columnIndex)
      = frame.activeSubset (frame.basisLabel columnIndex) :=
  datumTightSupport_eq_activeSubset_of_card_eq_rank frame.hdata
    (frame.hmemAll columnIndex) hcard

/-- **NO TRIPLED SUPPORT.**  Three distinct slots with one card-3 support
die at a rank-six frame: the support is the shared block, and the block
cap refuses three slots. -/
theorem RankSixFrame.false_of_three_supports_equal {crux : SixThreeCrux}
    (frame : RankSixFrame crux) {slotOne slotTwo slotThree : Fin 6}
    (h12 : slotOne ≠ slotTwo) (h13 : slotOne ≠ slotThree)
    (h23 : slotTwo ≠ slotThree)
    (hcardOne : (datumTightSupport frame.tightDir
      (frame.basisLabel slotOne)).card = 3)
    (hsuppTwo : datumTightSupport frame.tightDir (frame.basisLabel slotTwo)
      = datumTightSupport frame.tightDir (frame.basisLabel slotOne))
    (hsuppThree : datumTightSupport frame.tightDir (frame.basisLabel slotThree)
      = datumTightSupport frame.tightDir (frame.basisLabel slotOne)) : False := by
  have hcardTwo : (datumTightSupport frame.tightDir
      (frame.basisLabel slotTwo)).card = 3 := by rw [hsuppTwo]; exact hcardOne
  have hcardThree : (datumTightSupport frame.tightDir
      (frame.basisLabel slotThree)).card = 3 := by rw [hsuppThree]; exact hcardOne
  refine frame.false_of_three_slots_share_block h12 h13 h23 ?_ ?_
  · rw [← frame.dense_support_eq_block hcardTwo,
      ← frame.dense_support_eq_block hcardOne]
    exact hsuppTwo
  · rw [← frame.dense_support_eq_block hcardThree,
      ← frame.dense_support_eq_block hcardOne]
    exact hsuppThree

/-- **THE DOUBLED-PAIRS LAW.**  At a dense rank-six frame with two doubled
pairs, an atom outside the two doubled supports is carried by BOTH
remaining slots: only two carriers stay available, and the dense floor
demands two.  This is the rank-six weakening of the rank-five
doubled-cover law. -/
theorem RankSixFrame.dense_two_doubled_pairs_cover {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    (hmultTwo : ∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex)
    {slotA slotB slotC slotD slotE slotF : Fin 6}
    (hquad : ({slotA, slotB, slotC, slotD, slotE, slotF} : Finset (Fin 6)).card
      = 6)
    (hdoubledAB : datumTightSupport frame.tightDir (frame.basisLabel slotB)
      = datumTightSupport frame.tightDir (frame.basisLabel slotA))
    (hdoubledCD : datumTightSupport frame.tightDir (frame.basisLabel slotD)
      = datumTightSupport frame.tightDir (frame.basisLabel slotC))
    {atomIndex : Fin 6}
    (houtA : atomIndex ∉ datumTightSupport frame.tightDir
      (frame.basisLabel slotA))
    (houtC : atomIndex ∉ datumTightSupport frame.tightDir
      (frame.basisLabel slotC)) :
    atomIndex ∈ datumTightSupport frame.tightDir (frame.basisLabel slotE)
      ∧ atomIndex ∈ datumTightSupport frame.tightDir (frame.basisLabel slotF) := by
  classical
  have hsix : ({slotA, slotB, slotC, slotD, slotE, slotF} : Finset (Fin 6))
      = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hquad, Fintype.card_fin])
  have hEF : slotE ≠ slotF := by
    intro hcontra
    rw [hcontra] at hquad
    have hdup : ({slotA, slotB, slotC, slotD, slotF, slotF} : Finset (Fin 6))
        = {slotA, slotB, slotC, slotD, slotF} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hdup] at hquad
    have h1 := Finset.card_insert_le slotA
      ({slotB, slotC, slotD, slotF} : Finset (Fin 6))
    have h2 := Finset.card_insert_le slotB
      ({slotC, slotD, slotF} : Finset (Fin 6))
    have h3 := Finset.card_insert_le slotC ({slotD, slotF} : Finset (Fin 6))
    have h4 := Finset.card_insert_le slotD ({slotF} : Finset (Fin 6))
    rw [Finset.card_singleton] at h4
    omega
  have hfilterSub : Finset.univ.filter (fun columnIndex =>
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex)) ⊆ ({slotE, slotF} : Finset (Fin 6)) := by
    intro columnIndex hmemFilter
    have hcarry := (Finset.mem_filter.mp hmemFilter).2
    have hmemSix : columnIndex ∈ ({slotA, slotB, slotC, slotD, slotE, slotF}
        : Finset (Fin 6)) := by
      rw [hsix]
      exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemSix ⊢
    rcases hmemSix with hA | hB | hC | hD | hE | hF
    · rw [hA] at hcarry
      exact absurd hcarry houtA
    · rw [hB, hdoubledAB] at hcarry
      exact absurd hcarry houtA
    · rw [hC] at hcarry
      exact absurd hcarry houtC
    · rw [hD, hdoubledCD] at hcarry
      exact absurd hcarry houtC
    · exact Or.inl hE
    · exact Or.inr hF
  have hfloor := hmultTwo atomIndex
  rw [basisSupportMultiplicity] at hfloor
  have hcardPair : ({slotE, slotF} : Finset (Fin 6)).card = 2 := by
    rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hEF),
      Finset.card_singleton]
  have hfilterEq : Finset.univ.filter (fun columnIndex =>
      atomIndex ∈ datumTightSupport frame.tightDir
        (frame.basisLabel columnIndex)) = ({slotE, slotF} : Finset (Fin 6)) := by
    refine Finset.eq_of_subset_of_card_le hfilterSub ?_
    rw [hcardPair]
    exact hfloor
  constructor
  · have hmemE : slotE ∈ Finset.univ.filter (fun columnIndex =>
        atomIndex ∈ datumTightSupport frame.tightDir
          (frame.basisLabel columnIndex)) := by
      rw [hfilterEq]
      exact Finset.mem_insert_self _ _
    exact (Finset.mem_filter.mp hmemE).2
  · have hmemF : slotF ∈ Finset.univ.filter (fun columnIndex =>
        atomIndex ∈ datumTightSupport frame.tightDir
          (frame.basisLabel columnIndex)) := by
      rw [hfilterEq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_filter.mp hmemF).2

end Gtz
