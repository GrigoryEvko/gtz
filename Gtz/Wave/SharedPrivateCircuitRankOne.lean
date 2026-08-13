import Gtz.Wave.SharedPrivateCaptureLeak
import Gtz.Wave.OuterComplementNullKill
import Gtz.Wave.SharedPrivateConfinement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The circuit rank-one link — the shared triple dies and the pair residue splits

The extras stratum of the shared-private kill is one residue: a positive
label parallel to no basis column.  The width of its coefficient vector
splits that residue in two, and the landed pair narrowing gives the
geometry for free: the two supports of a pair circuit share two atoms or
three.  This module reads the two branches.

The common triple.  Two basis columns with the SAME support of three
atoms are two independent directions in one three-dimensional space, and
both are tight there.  Thus the shifted gap block on that triple
annihilates a plane, thus it is a rank-one square.  That is the shape of
the outer fork, and this module consumes the outer solver verbatim: the
six two-by-two minors of the block vanish.

The triple kill.  A rank-one block has a two-dimensional kernel, thus a
THIRD basis column on the same triple is a third independent direction
in a plane.  Such a column cannot exist.  This is unconditional: it needs
no circuit, no width and no trace.

The split branch.  When the two supports share two atoms, each column is
tight at the foreign atom of the other, because the chart annihilates it
there.  Thus both columns are tight on the union of four atoms, and every
combination that drops one shared atom is tight on a triple of that
union.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.triple_tight_corner_rows` — the three corner rows of a tight
  direction on a triple.
* `Gtz.wedge_ne_zero_of_common_triple` — **THE WEDGE LAW**: two
  independent tight directions on one triple have a live wedge on the
  first pair.
* `Gtz.gapBlockRankOne_of_common_triple` — **THE CROSS-FORK LINK**: the
  shifted gap block on a shared triple is a rank-one square.
* `Gtz.false_of_triple_common_triple` — **THE TRIPLE KILL**: three
  independent tight directions cannot share one triple.
* `Gtz.SharedPrivateData.basisLabel_mem_activeSet`,
  `Gtz.SharedPrivateData.basisBlock_eq_support`,
  `Gtz.SharedPrivateData.basis_live_of_mem_support`,
  `Gtz.SharedPrivateData.basis_dead_of_notMem_support` — the basis block
  law.
* `Gtz.SharedPrivateData.leftInv_read`,
  `Gtz.SharedPrivateData.pair_coeff_eq_zero`,
  `Gtz.SharedPrivateData.triple_coeff_eq_zero` — the basis independence.
* `Gtz.SharedPrivateData.shiftedGap_diag_pos` — the corner floor.
* `Gtz.SharedPrivateData.gapBlockRankOne_of_identical_support` — the
  datum reading of the cross-fork link.
* `Gtz.SharedPrivateData.false_of_triple_identical_support` — **THE
  DATUM TRIPLE KILL**: three basis slots cannot share one support.
* `Gtz.chart_tight_row_of_capture_zero` — the foreign tight row.
* `Gtz.SharedPrivateData.pairCircuit_tight_at_foreign` — the pair
  circuit columns are tight on the union of the two supports.
* `Gtz.SharedPrivateData.wideCircuit_two_le_outside_slots` — **THE
  OUTSIDE PAIRING LAW** of a wide circuit.
* `Gtz.tight_pair_direction_parallel_null` — **THE PAIR RIGIDITY**: the
  outer pair-null kill never fires on a tight direction.
* `Gtz.SharedPrivateData.pinAtom_notMem_of_identical_support` — a shared
  triple misses the pin atom.
* `Gtz.SharedPrivateData.identical_support_offdiag_product_pos` — the
  three cross entries of a shared triple are alive.
* `Gtz.SharedPrivateData.splitCircuit_label_dead_on_shared` — **THE
  SPLIT LABEL COLLAPSE.**
* `Gtz.SharedPrivateData.splitCircuit_pair_minor_of_dead_wedge` — the
  vanishing pair minor of the collapsed branch.
* `Gtz.SharedPrivateCircuitPairIdenticalClosed`,
  `Gtz.SharedPrivateCircuitPairSplitClosed`,
  `Gtz.SharedPrivateCircuitWideDistinctClosed`,
  `Gtz.SharedPrivateCircuitSplitWedgeClosed`,
  `Gtz.SharedPrivateCircuitSplitPairClosed` — the narrowed circuit
  residues.
* `Gtz.sharedPrivateCircuitPairSharedClosed_of_branches`,
  `Gtz.sharedPrivateCircuitPairSplitClosed_of_wedge`,
  `Gtz.sharedPrivateCircuitWideClosed_of_distinct` — the narrowing.
* `Gtz.sharedPrivateKilled_of_circuit_branches`,
  `Gtz.rankFourSharedPrivateClosed_of_circuit_branches`,
  `Gtz.rankFiveSharedPrivateClosed_of_circuit_branches`,
  `Gtz.rankSixSharedPrivateClosed_of_circuit_branches` — the coarse
  dispatch.
* `Gtz.sharedPrivateKilled_of_circuit_lattice`,
  `Gtz.rankFourSharedPrivateClosed_of_circuit_lattice`,
  `Gtz.rankFiveSharedPrivateClosed_of_circuit_lattice`,
  `Gtz.rankSixSharedPrivateClosed_of_circuit_lattice` — the fine
  dispatch.
* `Gtz.sharedPrivateExtrasClosed_of_circuit_lattice`,
  `Gtz.sharedPrivateKilled_of_sharedPrivate_lattice`,
  `Gtz.rankFourSharedPrivateClosed_of_sharedPrivate_lattice`,
  `Gtz.rankFiveSharedPrivateClosed_of_sharedPrivate_lattice`,
  `Gtz.rankSixSharedPrivateClosed_of_sharedPrivate_lattice` — **THE
  WHOLE OF CLOSURE TWO ON FIVE RESIDUES.**

## Vacuity

The matrix statements are unconditional.  The datum statements quantify
over chart stationary data and over shared-private data, and no
shared-private datum exists if `Gtz.GtzWeighted 6 3` holds.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the corner rows of a tight direction on a triple -/

section CornerRows

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- **THE CORNER ROWS.**  A tight direction supported inside a triple of
block atoms solves the three rows of the shifted gap block on that
triple.  The block is symmetric, thus the three rows use six entries
only. -/
theorem triple_tight_corner_rows
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {label : activeIndex} (hmem : label ∈ activeSet)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hUblock : atomU ∈ activeSubset label) (hVblock : atomV ∈ activeSubset label)
    (hSblock : atomS ∈ activeSubset label)
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir label atomIndex = 0) :
    ((chartStationaryGap projection weight atomU atomU - value)
          * tightDir label atomU
        + chartStationaryGap projection weight atomU atomV * tightDir label atomV
        + chartStationaryGap projection weight atomU atomS * tightDir label atomS
      = 0)
    ∧ (chartStationaryGap projection weight atomU atomV * tightDir label atomU
        + (chartStationaryGap projection weight atomV atomV - value)
          * tightDir label atomV
        + chartStationaryGap projection weight atomV atomS * tightDir label atomS
      = 0)
    ∧ (chartStationaryGap projection weight atomU atomS * tightDir label atomU
        + chartStationaryGap projection weight atomV atomS * tightDir label atomV
        + (chartStationaryGap projection weight atomS atomS - value)
          * tightDir label atomS
      = 0) := by
  have hrowU := hdata.tightDir_isTight label hmem atomU hUblock
  have hrowV := hdata.tightDir_isTight label hmem atomV hVblock
  have hrowS := hdata.tightDir_isTight label hmem atomS hSblock
  rw [mulVec_apply_of_triple_support _ hUV hUS hVS hsupp atomU] at hrowU
  rw [mulVec_apply_of_triple_support _ hUV hUS hVS hsupp atomV] at hrowV
  rw [mulVec_apply_of_triple_support _ hUV hUS hVS hsupp atomS] at hrowS
  rw [chartStationaryGap_entry_symm hdata atomV atomU] at hrowV
  rw [chartStationaryGap_entry_symm hdata atomS atomU,
    chartStationaryGap_entry_symm hdata atomS atomV] at hrowS
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **THE WEDGE LAW.**  Two independent tight directions supported inside
one triple have a live two-by-two wedge on the first pair of that
triple, as soon as the shifted diagonal at the third atom is positive and
the first direction is alive at the second atom.  A dead wedge would put
a live direction on the third atom alone, and the shifted diagonal
refuses it. -/
theorem wedge_ne_zero_of_common_triple
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {labelOne labelTwo : activeIndex} (hmemOne : labelOne ∈ activeSet)
    (hmemTwo : labelTwo ∈ activeSet)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hSpos : 0 < chartStationaryGap projection weight atomS atomS - value)
    (hUblockOne : atomU ∈ activeSubset labelOne)
    (hVblockOne : atomV ∈ activeSubset labelOne)
    (hSblockOne : atomS ∈ activeSubset labelOne)
    (hUblockTwo : atomU ∈ activeSubset labelTwo)
    (hVblockTwo : atomV ∈ activeSubset labelTwo)
    (hSblockTwo : atomS ∈ activeSubset labelTwo)
    (hsuppOne : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelOne atomIndex = 0)
    (hsuppTwo : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelTwo atomIndex = 0)
    (hliveV : tightDir labelOne atomV ≠ 0)
    (hindep : ∀ scaleOne scaleTwo : ℝ,
      (∀ atomIndex : Fin size, scaleOne * tightDir labelOne atomIndex
        + scaleTwo * tightDir labelTwo atomIndex = 0) →
      scaleOne = 0 ∧ scaleTwo = 0) :
    tightDir labelOne atomU * tightDir labelTwo atomV
      - tightDir labelOne atomV * tightDir labelTwo atomU ≠ 0 := by
  intro hwedge
  obtain ⟨_, _, hrowSOne⟩ := triple_tight_corner_rows hdata hmemOne hUV hUS hVS
    hUblockOne hVblockOne hSblockOne hsuppOne
  obtain ⟨_, _, hrowSTwo⟩ := triple_tight_corner_rows hdata hmemTwo hUV hUS hVS
    hUblockTwo hVblockTwo hSblockTwo hsuppTwo
  -- the excision of the second atom
  have hexciseU : tightDir labelTwo atomV * tightDir labelOne atomU
      - tightDir labelOne atomV * tightDir labelTwo atomU = 0 := by
    linear_combination hwedge
  have hexciseV : tightDir labelTwo atomV * tightDir labelOne atomV
      - tightDir labelOne atomV * tightDir labelTwo atomV = 0 := by ring
  have hexciseS : tightDir labelTwo atomV * tightDir labelOne atomS
      - tightDir labelOne atomV * tightDir labelTwo atomS = 0 := by
    have hrow : chartStationaryGap projection weight atomU atomS
          * (tightDir labelTwo atomV * tightDir labelOne atomU
            - tightDir labelOne atomV * tightDir labelTwo atomU)
        + chartStationaryGap projection weight atomV atomS
          * (tightDir labelTwo atomV * tightDir labelOne atomV
            - tightDir labelOne atomV * tightDir labelTwo atomV)
        + (chartStationaryGap projection weight atomS atomS - value)
          * (tightDir labelTwo atomV * tightDir labelOne atomS
            - tightDir labelOne atomV * tightDir labelTwo atomS) = 0 := by
      linear_combination tightDir labelTwo atomV * hrowSOne
        - tightDir labelOne atomV * hrowSTwo
    rw [hexciseU, hexciseV, mul_zero, mul_zero, zero_add, zero_add] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left hSpos.ne'
  have hcombo : ∀ atomIndex : Fin size,
      tightDir labelTwo atomV * tightDir labelOne atomIndex
        + (-(tightDir labelOne atomV)) * tightDir labelTwo atomIndex = 0 := by
    intro atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU; linear_combination hexciseU
    by_cases hV : atomIndex = atomV
    · subst hV; linear_combination hexciseV
    by_cases hS : atomIndex = atomS
    · subst hS; linear_combination hexciseS
    rw [hsuppOne atomIndex hU hV hS, hsuppTwo atomIndex hU hV hS]
    ring
  obtain ⟨_, hsecond⟩ := hindep _ _ hcombo
  exact hliveV (by linarith)

/-- **THE CROSS-FORK LINK.**  Two independent tight directions supported
inside one triple force the shifted gap block on that triple to be a
rank-one square: all six two-by-two minors vanish.  The proof feeds the
outer rank-one corner solver with the excision of the third atom as the
pair direction and with the first direction as the wide direction. -/
theorem gapBlockRankOne_of_common_triple
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {labelOne labelTwo : activeIndex} (hmemOne : labelOne ∈ activeSet)
    (hmemTwo : labelTwo ∈ activeSet)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hUpos : 0 < chartStationaryGap projection weight atomU atomU - value)
    (hVpos : 0 < chartStationaryGap projection weight atomV atomV - value)
    (hSpos : 0 < chartStationaryGap projection weight atomS atomS - value)
    (hUblockOne : atomU ∈ activeSubset labelOne)
    (hVblockOne : atomV ∈ activeSubset labelOne)
    (hSblockOne : atomS ∈ activeSubset labelOne)
    (hUblockTwo : atomU ∈ activeSubset labelTwo)
    (hVblockTwo : atomV ∈ activeSubset labelTwo)
    (hSblockTwo : atomS ∈ activeSubset labelTwo)
    (hsuppOne : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelOne atomIndex = 0)
    (hsuppTwo : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelTwo atomIndex = 0)
    (hliveV : tightDir labelOne atomV ≠ 0)
    (hliveS : tightDir labelOne atomS ≠ 0)
    (hindep : ∀ scaleOne scaleTwo : ℝ,
      (∀ atomIndex : Fin size, scaleOne * tightDir labelOne atomIndex
        + scaleTwo * tightDir labelTwo atomIndex = 0) →
      scaleOne = 0 ∧ scaleTwo = 0) :
    GapBlockRankOne projection weight value atomU atomV atomS := by
  obtain ⟨hrowUOne, hrowVOne, hrowSOne⟩ := triple_tight_corner_rows hdata hmemOne
    hUV hUS hVS hUblockOne hVblockOne hSblockOne hsuppOne
  obtain ⟨hrowUTwo, hrowVTwo, hrowSTwo⟩ := triple_tight_corner_rows hdata hmemTwo
    hUV hUS hVS hUblockTwo hVblockTwo hSblockTwo hsuppTwo
  -- the excision of the third atom is a pair direction
  set pairU : ℝ := tightDir labelTwo atomS * tightDir labelOne atomU
    - tightDir labelOne atomS * tightDir labelTwo atomU with hpairUDef
  set pairV : ℝ := tightDir labelTwo atomS * tightDir labelOne atomV
    - tightDir labelOne atomS * tightDir labelTwo atomV with hpairVDef
  have hpairRowU : (chartStationaryGap projection weight atomU atomU - value) * pairU
      + chartStationaryGap projection weight atomU atomV * pairV = 0 := by
    rw [hpairUDef, hpairVDef]
    linear_combination tightDir labelTwo atomS * hrowUOne
      - tightDir labelOne atomS * hrowUTwo
  have hpairRowV : chartStationaryGap projection weight atomU atomV * pairU
      + (chartStationaryGap projection weight atomV atomV - value) * pairV = 0 := by
    rw [hpairUDef, hpairVDef]
    linear_combination tightDir labelTwo atomS * hrowVOne
      - tightDir labelOne atomS * hrowVTwo
  -- the pair direction is alive at both atoms
  have hpairZero : pairU = 0 → pairV = 0 → False := by
    intro hzeroU hzeroV
    have hcombo : ∀ atomIndex : Fin size,
        tightDir labelTwo atomS * tightDir labelOne atomIndex
          + (-(tightDir labelOne atomS)) * tightDir labelTwo atomIndex = 0 := by
      intro atomIndex
      by_cases hU : atomIndex = atomU
      · subst hU
        rw [hpairUDef] at hzeroU
        linear_combination hzeroU
      by_cases hV : atomIndex = atomV
      · subst hV
        rw [hpairVDef] at hzeroV
        linear_combination hzeroV
      by_cases hS : atomIndex = atomS
      · subst hS; ring
      rw [hsuppOne atomIndex hU hV hS, hsuppTwo atomIndex hU hV hS]
      ring
    obtain ⟨_, hsecond⟩ := hindep _ _ hcombo
    exact hliveS (by linarith)
  have hpairUne : pairU ≠ 0 := by
    intro hzeroU
    refine hpairZero hzeroU ?_
    rw [hzeroU, mul_zero, zero_add] at hpairRowV
    exact (mul_eq_zero.mp hpairRowV).resolve_left hVpos.ne'
  have hpairVne : pairV ≠ 0 := by
    intro hzeroV
    refine hpairZero ?_ hzeroV
    rw [hzeroV, mul_zero, add_zero] at hpairRowU
    exact (mul_eq_zero.mp hpairRowU).resolve_left hUpos.ne'
  -- the wide direction is independent of the pair direction
  have hwedge := wedge_ne_zero_of_common_triple hdata hmemOne hmemTwo hUV hUS hVS
    hSpos hUblockOne hVblockOne hSblockOne hUblockTwo hVblockTwo hSblockTwo
    hsuppOne hsuppTwo hliveV hindep
  have hindepPair : tightDir labelOne atomV * pairU
      - tightDir labelOne atomU * pairV ≠ 0 := by
    rw [hpairUDef, hpairVDef]
    have hfactor : tightDir labelOne atomV
          * (tightDir labelTwo atomS * tightDir labelOne atomU
            - tightDir labelOne atomS * tightDir labelTwo atomU)
        - tightDir labelOne atomU
          * (tightDir labelTwo atomS * tightDir labelOne atomV
            - tightDir labelOne atomS * tightDir labelTwo atomV)
        = tightDir labelOne atomS
          * (tightDir labelOne atomU * tightDir labelTwo atomV
            - tightDir labelOne atomV * tightDir labelTwo atomU) := by
      ring
    rw [hfactor]
    exact mul_ne_zero hliveS hwedge
  obtain ⟨_, hone, htwo, hthree, hfour, hfive, hsix⟩ :=
    gap_rank_one_of_pair_and_wide
      (cornerUU := chartStationaryGap projection weight atomU atomU - value)
      (cornerVV := chartStationaryGap projection weight atomV atomV - value)
      (cornerSS := chartStationaryGap projection weight atomS atomS - value)
      (cornerUV := chartStationaryGap projection weight atomU atomV)
      (cornerUS := chartStationaryGap projection weight atomU atomS)
      (cornerVS := chartStationaryGap projection weight atomV atomS)
      (pairU := pairU) (pairV := pairV)
      (wideU := tightDir labelOne atomU) (wideV := tightDir labelOne atomV)
      (wideS := tightDir labelOne atomS)
      hUpos hVpos hpairUne hpairVne hindepPair hpairRowU hpairRowV
      (by linear_combination hrowUOne) (by linear_combination hrowVOne)
      (by linear_combination hrowSOne)
  exact ⟨hone, htwo, hthree, hfour, hfive, hsix⟩

/-- **THE TRIPLE KILL.**  Three independent tight directions cannot share
one triple of block atoms.  The shifted gap block on the triple has a
positive shifted diagonal, thus its kernel is a plane, and a third
independent direction does not fit.  The proof is the Cramer combination
that dies at the first two atoms of the triple. -/
theorem false_of_triple_common_triple
    (hdata : IsChartStationaryData rank projection weight value activeSet
      activeSubset activeWeight tightDir)
    {labelOne labelTwo labelThree : activeIndex} (hmemOne : labelOne ∈ activeSet)
    (hmemTwo : labelTwo ∈ activeSet) (hmemThree : labelThree ∈ activeSet)
    {atomU atomV atomS : Fin size} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hSpos : 0 < chartStationaryGap projection weight atomS atomS - value)
    (hUblockOne : atomU ∈ activeSubset labelOne)
    (hVblockOne : atomV ∈ activeSubset labelOne)
    (hSblockOne : atomS ∈ activeSubset labelOne)
    (hUblockTwo : atomU ∈ activeSubset labelTwo)
    (hVblockTwo : atomV ∈ activeSubset labelTwo)
    (hSblockTwo : atomS ∈ activeSubset labelTwo)
    (hUblockThree : atomU ∈ activeSubset labelThree)
    (hVblockThree : atomV ∈ activeSubset labelThree)
    (hSblockThree : atomS ∈ activeSubset labelThree)
    (hsuppOne : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelOne atomIndex = 0)
    (hsuppTwo : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelTwo atomIndex = 0)
    (hsuppThree : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomV →
      atomIndex ≠ atomS → tightDir labelThree atomIndex = 0)
    (hliveV : tightDir labelOne atomV ≠ 0)
    (hindepPair : ∀ scaleOne scaleTwo : ℝ,
      (∀ atomIndex : Fin size, scaleOne * tightDir labelOne atomIndex
        + scaleTwo * tightDir labelTwo atomIndex = 0) →
      scaleOne = 0 ∧ scaleTwo = 0)
    (hindepTriple : ∀ scaleOne scaleTwo scaleThree : ℝ,
      (∀ atomIndex : Fin size, scaleOne * tightDir labelOne atomIndex
        + scaleTwo * tightDir labelTwo atomIndex
        + scaleThree * tightDir labelThree atomIndex = 0) →
      scaleOne = 0 ∧ scaleTwo = 0 ∧ scaleThree = 0) :
    False := by
  obtain ⟨_, _, hrowSOne⟩ := triple_tight_corner_rows hdata hmemOne hUV hUS hVS
    hUblockOne hVblockOne hSblockOne hsuppOne
  obtain ⟨_, _, hrowSTwo⟩ := triple_tight_corner_rows hdata hmemTwo hUV hUS hVS
    hUblockTwo hVblockTwo hSblockTwo hsuppTwo
  obtain ⟨_, _, hrowSThree⟩ := triple_tight_corner_rows hdata hmemThree hUV hUS hVS
    hUblockThree hVblockThree hSblockThree hsuppThree
  have hwedge := wedge_ne_zero_of_common_triple hdata hmemOne hmemTwo hUV hUS hVS
    hSpos hUblockOne hVblockOne hSblockOne hUblockTwo hVblockTwo hSblockTwo
    hsuppOne hsuppTwo hliveV hindepPair
  -- the Cramer combination of the three directions
  set scaleThree : ℝ := tightDir labelOne atomU * tightDir labelTwo atomV
    - tightDir labelOne atomV * tightDir labelTwo atomU with hscaleThreeDef
  set scaleOne : ℝ := -(tightDir labelThree atomU * tightDir labelTwo atomV
    - tightDir labelThree atomV * tightDir labelTwo atomU) with hscaleOneDef
  set scaleTwo : ℝ := tightDir labelThree atomU * tightDir labelOne atomV
    - tightDir labelThree atomV * tightDir labelOne atomU with hscaleTwoDef
  have hcramerU : scaleOne * tightDir labelOne atomU
      + scaleTwo * tightDir labelTwo atomU
      + scaleThree * tightDir labelThree atomU = 0 := by
    rw [hscaleOneDef, hscaleTwoDef, hscaleThreeDef]; ring
  have hcramerV : scaleOne * tightDir labelOne atomV
      + scaleTwo * tightDir labelTwo atomV
      + scaleThree * tightDir labelThree atomV = 0 := by
    rw [hscaleOneDef, hscaleTwoDef, hscaleThreeDef]; ring
  have hcramerS : scaleOne * tightDir labelOne atomS
      + scaleTwo * tightDir labelTwo atomS
      + scaleThree * tightDir labelThree atomS = 0 := by
    have hrow : chartStationaryGap projection weight atomU atomS
          * (scaleOne * tightDir labelOne atomU
            + scaleTwo * tightDir labelTwo atomU
            + scaleThree * tightDir labelThree atomU)
        + chartStationaryGap projection weight atomV atomS
          * (scaleOne * tightDir labelOne atomV
            + scaleTwo * tightDir labelTwo atomV
            + scaleThree * tightDir labelThree atomV)
        + (chartStationaryGap projection weight atomS atomS - value)
          * (scaleOne * tightDir labelOne atomS
            + scaleTwo * tightDir labelTwo atomS
            + scaleThree * tightDir labelThree atomS) = 0 := by
      linear_combination scaleOne * hrowSOne + scaleTwo * hrowSTwo
        + scaleThree * hrowSThree
    rw [hcramerU, hcramerV, mul_zero, mul_zero, zero_add, zero_add] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left hSpos.ne'
  have hcombo : ∀ atomIndex : Fin size,
      scaleOne * tightDir labelOne atomIndex
        + scaleTwo * tightDir labelTwo atomIndex
        + scaleThree * tightDir labelThree atomIndex = 0 := by
    intro atomIndex
    by_cases hU : atomIndex = atomU
    · subst hU; exact hcramerU
    by_cases hV : atomIndex = atomV
    · subst hV; exact hcramerV
    by_cases hS : atomIndex = atomS
    · subst hS; exact hcramerS
    rw [hsuppOne atomIndex hU hV hS, hsuppTwo atomIndex hU hV hS,
      hsuppThree atomIndex hU hV hS]
    ring
  obtain ⟨_, _, hthird⟩ := hindepTriple _ _ _ hcombo
  exact hwedge hthird

end CornerRows

/-! ## Layer 2 — the basis frame of a shared-private datum -/

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- Every basis label is an active label. -/
theorem basisLabel_mem_activeSet (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) : data.basisLabel slot ∈ data.activeSet := by
  have hpos := data.hmem slot
  rw [positiveActiveSet, Finset.mem_filter] at hpos
  exact hpos.1

/-- **THE BASIS BLOCK LAW.**  A basis support has three atoms and the
block has three atoms, thus the two agree. -/
theorem basisBlock_eq_support (data : SharedPrivateData crux)
    (slot : Fin data.basisCount) :
    data.activeSubset (data.basisLabel slot)
      = datumTightSupport data.tightDir (data.basisLabel slot) := by
  refine (Finset.eq_of_subset_of_card_le
    (datumTightSupport_subset data.hdata (data.basisLabel_mem_activeSet slot)) ?_).symm
  rw [data.hthree slot,
    data.hdata.activeSubset_card _ (data.basisLabel_mem_activeSet slot)]

/-- A basis atom of the support carries a live coordinate. -/
theorem basis_live_of_mem_support (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomIndex : Fin 6}
    (hmem : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slot)) :
    data.tightDir (data.basisLabel slot) atomIndex ≠ 0 :=
  mem_datumTightSupport.mp hmem

/-- A basis atom outside the support carries a dead coordinate. -/
theorem basis_dead_of_notMem_support (data : SharedPrivateData crux)
    {slot : Fin data.basisCount} {atomIndex : Fin 6}
    (hout : atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)) :
    data.tightDir (data.basisLabel slot) atomIndex = 0 := by
  by_contra hne
  exact hout (mem_datumTightSupport.mpr hne)

/-- **THE LEFT INVERSE READ.**  The left inverse reads the basis columns
as the identity. -/
theorem leftInv_read (data : SharedPrivateData crux)
    (slotRow slotCol : Fin data.basisCount) :
    ∑ atomIndex : Fin 6, data.leftInv slotRow atomIndex
        * data.tightDir (data.basisLabel slotCol) atomIndex
      = if slotRow = slotCol then 1 else 0 := by
  have hentry := congrFun (congrFun data.hleft slotRow) slotCol
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  rw [← hentry]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- **THE PAIR INDEPENDENCE.**  Two distinct basis columns are
independent. -/
theorem pair_coeff_eq_zero (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {scaleOne scaleTwo : ℝ}
    (hcombo : ∀ atomIndex : Fin 6,
      scaleOne * data.tightDir (data.basisLabel slotOne) atomIndex
        + scaleTwo * data.tightDir (data.basisLabel slotTwo) atomIndex = 0) :
    scaleOne = 0 ∧ scaleTwo = 0 := by
  have hread : ∀ probe : Fin data.basisCount,
      scaleOne * (if probe = slotOne then (1 : ℝ) else 0)
        + scaleTwo * (if probe = slotTwo then (1 : ℝ) else 0) = 0 := by
    intro probe
    have hzero : ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
        * (scaleOne * data.tightDir (data.basisLabel slotOne) atomIndex
          + scaleTwo * data.tightDir (data.basisLabel slotTwo) atomIndex) = 0 :=
      Finset.sum_eq_zero fun atomIndex _ => by rw [hcombo atomIndex, mul_zero]
    have hexpand : ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
        * (scaleOne * data.tightDir (data.basisLabel slotOne) atomIndex
          + scaleTwo * data.tightDir (data.basisLabel slotTwo) atomIndex)
        = scaleOne * ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
            * data.tightDir (data.basisLabel slotOne) atomIndex
          + scaleTwo * ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
            * data.tightDir (data.basisLabel slotTwo) atomIndex := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hexpand, data.leftInv_read probe slotOne, data.leftInv_read probe slotTwo]
      at hzero
    exact hzero
  refine ⟨?_, ?_⟩
  · have hone := hread slotOne
    rw [if_pos rfl, if_neg hne] at hone
    linarith
  · have htwo := hread slotTwo
    rw [if_neg (Ne.symm hne), if_pos rfl] at htwo
    linarith

/-- **THE TRIPLE INDEPENDENCE.**  Three distinct basis columns are
independent. -/
theorem triple_coeff_eq_zero (data : SharedPrivateData crux)
    {slotOne slotTwo slotThree : Fin data.basisCount} (hOneTwo : slotOne ≠ slotTwo)
    (hOneThree : slotOne ≠ slotThree) (hTwoThree : slotTwo ≠ slotThree)
    {scaleOne scaleTwo scaleThree : ℝ}
    (hcombo : ∀ atomIndex : Fin 6,
      scaleOne * data.tightDir (data.basisLabel slotOne) atomIndex
        + scaleTwo * data.tightDir (data.basisLabel slotTwo) atomIndex
        + scaleThree * data.tightDir (data.basisLabel slotThree) atomIndex = 0) :
    scaleOne = 0 ∧ scaleTwo = 0 ∧ scaleThree = 0 := by
  have hread : ∀ probe : Fin data.basisCount,
      scaleOne * (if probe = slotOne then (1 : ℝ) else 0)
        + scaleTwo * (if probe = slotTwo then (1 : ℝ) else 0)
        + scaleThree * (if probe = slotThree then (1 : ℝ) else 0) = 0 := by
    intro probe
    have hzero : ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
        * (scaleOne * data.tightDir (data.basisLabel slotOne) atomIndex
          + scaleTwo * data.tightDir (data.basisLabel slotTwo) atomIndex
          + scaleThree * data.tightDir (data.basisLabel slotThree) atomIndex) = 0 :=
      Finset.sum_eq_zero fun atomIndex _ => by rw [hcombo atomIndex, mul_zero]
    have hexpand : ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
        * (scaleOne * data.tightDir (data.basisLabel slotOne) atomIndex
          + scaleTwo * data.tightDir (data.basisLabel slotTwo) atomIndex
          + scaleThree * data.tightDir (data.basisLabel slotThree) atomIndex)
        = scaleOne * ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
            * data.tightDir (data.basisLabel slotOne) atomIndex
          + scaleTwo * ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
            * data.tightDir (data.basisLabel slotTwo) atomIndex
          + scaleThree * ∑ atomIndex : Fin 6, data.leftInv probe atomIndex
            * data.tightDir (data.basisLabel slotThree) atomIndex := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hexpand, data.leftInv_read probe slotOne, data.leftInv_read probe slotTwo,
      data.leftInv_read probe slotThree] at hzero
    exact hzero
  refine ⟨?_, ?_, ?_⟩
  · have hone := hread slotOne
    rw [if_pos rfl, if_neg hOneTwo, if_neg hOneThree] at hone
    linarith
  · have htwo := hread slotTwo
    rw [if_neg (Ne.symm hOneTwo), if_pos rfl, if_neg hTwoThree] at htwo
    linarith
  · have hthree := hread slotThree
    rw [if_neg (Ne.symm hOneThree), if_neg (Ne.symm hTwoThree), if_pos rfl] at hthree
    linarith

/-- **THE CORNER FLOOR.**  The shifted gap diagonal is positive at every
atom: the gap floor is positive and the value is negative. -/
theorem shiftedGap_diag_pos (data : SharedPrivateData crux) (atomIndex : Fin 6) :
    0 < chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight atomIndex atomIndex
      - chartObjective (chartPointOfDesign crux.design) := by
  have hfloor := crux.chartGap_diagonal_pos atomIndex
  have hvalue := data.hvalueNeg
  linarith

/-! ## Layer 3 — the shared triple at the datum -/

/-- **THE DATUM RANK-ONE LINK.**  Two distinct basis slots with the same
support of three atoms force the shifted gap block on that triple to be a
rank-one square. -/
theorem gapBlockRankOne_of_identical_support (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    GapBlockRankOne (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS := by
  classical
  have hmemU : atomU ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hmemV : atomV ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hmemS : atomS ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hblockOne := data.basisBlock_eq_support slotOne
  have hblockTwo := data.basisBlock_eq_support slotTwo
  refine gapBlockRankOne_of_common_triple data.hdata
    (data.basisLabel_mem_activeSet slotOne) (data.basisLabel_mem_activeSet slotTwo)
    hUV hUS hVS (data.shiftedGap_diag_pos atomU) (data.shiftedGap_diag_pos atomV)
    (data.shiftedGap_diag_pos atomS)
    (by rw [hblockOne, hsupportOne]; exact hmemU)
    (by rw [hblockOne, hsupportOne]; exact hmemV)
    (by rw [hblockOne, hsupportOne]; exact hmemS)
    (by rw [hblockTwo, hsupportTwo]; exact hmemU)
    (by rw [hblockTwo, hsupportTwo]; exact hmemV)
    (by rw [hblockTwo, hsupportTwo]; exact hmemS)
    (fun atomIndex hU hV hS => data.basis_dead_of_notMem_support
      (by rw [hsupportOne]; simp [hU, hV, hS]))
    (fun atomIndex hU hV hS => data.basis_dead_of_notMem_support
      (by rw [hsupportTwo]; simp [hU, hV, hS]))
    (data.basis_live_of_mem_support (by rw [hsupportOne]; exact hmemV))
    (data.basis_live_of_mem_support (by rw [hsupportOne]; exact hmemS))
    fun scaleOne scaleTwo hcombo => data.pair_coeff_eq_zero hne hcombo

/-- **THE DATUM TRIPLE KILL.**  Three distinct basis slots cannot share
one support.  The support is a triple, the shifted gap block on it has a
positive shifted diagonal, thus its kernel is a plane, and three
independent basis columns do not fit in a plane. -/
theorem false_of_triple_identical_support (data : SharedPrivateData crux)
    {slotOne slotTwo slotThree : Fin data.basisCount} (hOneTwo : slotOne ≠ slotTwo)
    (hOneThree : slotOne ≠ slotThree) (hTwoThree : slotTwo ≠ slotThree)
    (hsameTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hsameThree : datumTightSupport data.tightDir (data.basisLabel slotThree)
      = datumTightSupport data.tightDir (data.basisLabel slotOne)) :
    False := by
  classical
  obtain ⟨atomU, atomV, atomS, hUV, hUS, hVS, hsupportOne⟩ :=
    Finset.card_eq_three.mp (data.hthree slotOne)
  have hmemU : atomU ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hmemV : atomV ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hmemS : atomS ∈ ({atomU, atomV, atomS} : Finset (Fin 6)) := by simp
  have hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS} := by rw [hsameTwo, hsupportOne]
  have hsupportThree : datumTightSupport data.tightDir (data.basisLabel slotThree)
      = {atomU, atomV, atomS} := by rw [hsameThree, hsupportOne]
  have hblockOne := data.basisBlock_eq_support slotOne
  have hblockTwo := data.basisBlock_eq_support slotTwo
  have hblockThree := data.basisBlock_eq_support slotThree
  refine false_of_triple_common_triple data.hdata
    (data.basisLabel_mem_activeSet slotOne) (data.basisLabel_mem_activeSet slotTwo)
    (data.basisLabel_mem_activeSet slotThree) hUV hUS hVS
    (data.shiftedGap_diag_pos atomS)
    (by rw [hblockOne, hsupportOne]; exact hmemU)
    (by rw [hblockOne, hsupportOne]; exact hmemV)
    (by rw [hblockOne, hsupportOne]; exact hmemS)
    (by rw [hblockTwo, hsupportTwo]; exact hmemU)
    (by rw [hblockTwo, hsupportTwo]; exact hmemV)
    (by rw [hblockTwo, hsupportTwo]; exact hmemS)
    (by rw [hblockThree, hsupportThree]; exact hmemU)
    (by rw [hblockThree, hsupportThree]; exact hmemV)
    (by rw [hblockThree, hsupportThree]; exact hmemS)
    (fun atomIndex hU hV hS => data.basis_dead_of_notMem_support
      (by rw [hsupportOne]; simp [hU, hV, hS]))
    (fun atomIndex hU hV hS => data.basis_dead_of_notMem_support
      (by rw [hsupportTwo]; simp [hU, hV, hS]))
    (fun atomIndex hU hV hS => data.basis_dead_of_notMem_support
      (by rw [hsupportThree]; simp [hU, hV, hS]))
    (data.basis_live_of_mem_support (by rw [hsupportOne]; exact hmemV))
    (fun scaleOne scaleTwo hcombo => data.pair_coeff_eq_zero hOneTwo hcombo)
    fun scaleOne scaleTwo scaleThree hcombo =>
      data.triple_coeff_eq_zero hOneTwo hOneThree hTwoThree hcombo

end SharedPrivateData

/-! ## Layer 4 — the split branch of a pair circuit -/

/-- **THE FOREIGN TIGHT ROW.**  A direction that the chart annihilates at
an atom where the direction itself vanishes is tight at that atom, even
though the atom sits outside the direction's block. -/
theorem chart_tight_row_of_capture_zero {crux : SixThreeCrux} {vec : Fin 6 → ℝ}
    {atomIndex : Fin 6}
    (hcapture : ((chartPointOfDesign crux.design).chart *ᵥ vec) atomIndex = 0)
    (hzero : vec atomIndex = 0) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight *ᵥ vec) atomIndex
      = chartObjective (chartPointOfDesign crux.design) * vec atomIndex := by
  rw [hzero, mul_zero, chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
    hcapture, Matrix.mulVec_diagonal, hzero, mul_zero, sub_zero]

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- **THE FOREIGN TIGHTNESS OF A PAIR CIRCUIT.**  At an atom of one
support that the other misses, the missing column is tight as well.  Thus
both columns of a pair circuit are tight on the union of the two
supports, which carries one atom more than either block. -/
theorem pairCircuit_tight_at_foreign (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomIndex : Fin 6}
    (hin : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (hout : atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo)) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
      *ᵥ data.tightDir (data.basisLabel slotTwo)) atomIndex
      = chartObjective (chartPointOfDesign crux.design)
        * data.tightDir (data.basisLabel slotTwo) atomIndex :=
  chart_tight_row_of_capture_zero
    (data.pairCircuit_capture_eq_zero hmem hpos hne hcoeffOne hcoeffTwo hpair hin hout)
    (data.basis_dead_of_notMem_support hout)

/-- **THE OUTSIDE PAIRING LAW OF A WIDE CIRCUIT.**  An atom outside the
label's block that sits in exactly one live support kills that live
coefficient.  Thus every such atom sits in two live supports or in
none. -/
theorem wideCircuit_two_le_outside_slots (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne : Fin data.basisCount}
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    {atomIndex : Fin 6} (hout : atomIndex ∉ data.activeSubset label)
    (hin : atomIndex ∈ datumTightSupport data.tightDir (data.basisLabel slotOne))
    (halone : ∀ slot, slot ≠ slotOne →
      atomIndex ∉ datumTightSupport data.tightDir (data.basisLabel slot)) :
    False := by
  classical
  have hcircuit := data.circuit_equation hmem hpos hout
  have hcollapse : ∑ slot, data.labelCoeff label slot
      * data.tightDir (data.basisLabel slot) atomIndex
      = data.labelCoeff label slotOne
        * data.tightDir (data.basisLabel slotOne) atomIndex :=
    Finset.sum_eq_single slotOne
      (fun slot _ hslot => by
        rw [data.basis_dead_of_notMem_support (halone slot hslot), mul_zero])
      (fun hnot => absurd (Finset.mem_univ _) hnot)
  rw [hcollapse] at hcircuit
  exact (mul_ne_zero hcoeffOne (data.basis_live_of_mem_support hin)) hcircuit

end SharedPrivateData

/-! ## Layer 5 — the readings of the shared triple and the split dichotomy -/

section PairRigidity

variable {size : ℕ}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ}

/-- **THE PAIR RIGIDITY.**  Every direction supported inside one atom pair
with a tight row at the left atom is proportional to the null direction of
that pair.  Thus the outer pair-null kill never fires on a tight
direction, and a kill of the shared triple must use a second law. -/
theorem tight_pair_direction_parallel_null {atomU atomS : Fin size}
    (hUS : atomU ≠ atomS) {vec : Fin size → ℝ}
    (hsupp : ∀ atomIndex, atomIndex ≠ atomU → atomIndex ≠ atomS →
      vec atomIndex = 0)
    (hrow : (chartStationaryGap projection weight *ᵥ vec) atomU
      = value * vec atomU) :
    vec atomU * (value - chartStationaryGap projection weight atomU atomU)
      - vec atomS * chartStationaryGap projection weight atomU atomS = 0 := by
  rw [mulVec_apply_of_pair_support _ hUS hsupp atomU] at hrow
  linarith

end PairRigidity

namespace SharedPrivateData

variable {crux : SixThreeCrux}

/-- **THE PIN IS OUTSIDE A SHARED TRIPLE.**  Two distinct basis slots with
the same support miss the pin atom, because the pin atom sits in one
basis support only. -/
theorem pinAtom_notMem_of_identical_support (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = datumTightSupport data.tightDir (data.basisLabel slotOne)) :
    data.pinAtom ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
  intro hpinMem
  have hpinTwo : data.pinAtom
      ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsame]; exact hpinMem
  have hone : slotOne = data.privateSlot := by
    by_contra hcontra
    exact data.basis_live_of_mem_support hpinMem (data.hprivate slotOne hcontra)
  have htwo : slotTwo = data.privateSlot := by
    by_contra hcontra
    exact data.basis_live_of_mem_support hpinTwo (data.hprivate slotTwo hcontra)
  exact hne (hone.trans htwo.symm)

/-- **THE LIVE CROSS ENTRIES.**  On a shared triple the three off-diagonal
gap entries are alive and their product is positive: the block is a
rank-one square with a positive shifted diagonal. -/
theorem identical_support_offdiag_product_pos (data : SharedPrivateData crux)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    {atomU atomV atomS : Fin 6} (hUV : atomU ≠ atomV) (hUS : atomU ≠ atomS)
    (hVS : atomV ≠ atomS)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomU, atomV, atomS})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomU, atomV, atomS}) :
    0 < chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomU atomV
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomU atomS
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomV atomS :=
  gap_rankOne_offdiag_product_pos data.hvalueNeg
    (crux.chartGap_diagonal_pos atomU) (crux.chartGap_diagonal_pos atomV)
    (crux.chartGap_diagonal_pos atomS)
    (data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportOne
      hsupportTwo)

/-! ## The split dichotomy -/

/-- **THE SPLIT LABEL COLLAPSE.**  In the split branch a dead wedge on the
shared pair kills the circuit label at both shared atoms.  The label
already lives at the two foreign atoms, thus a live shared atom would give
the label four support atoms against a block of three. -/
theorem splitCircuit_label_dead_on_shared (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomA atomB atomX atomY : Fin 6}
    (hAB : atomA ≠ atomB) (hAX : atomA ≠ atomX) (hAY : atomA ≠ atomY)
    (hBX : atomB ≠ atomX) (hBY : atomB ≠ atomY) (hXY : atomX ≠ atomY)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomA, atomB, atomX})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomA, atomB, atomY})
    (hwedge : data.tightDir (data.basisLabel slotOne) atomA
        * data.tightDir (data.basisLabel slotTwo) atomB
      - data.tightDir (data.basisLabel slotOne) atomB
        * data.tightDir (data.basisLabel slotTwo) atomA = 0) :
    data.tightDir label atomA = 0 ∧ data.tightDir label atomB = 0 := by
  classical
  have hliveOneA : data.tightDir (data.basisLabel slotOne) atomA ≠ 0 :=
    data.basis_live_of_mem_support (by rw [hsupportOne]; simp)
  have hliveOneB : data.tightDir (data.basisLabel slotOne) atomB ≠ 0 :=
    data.basis_live_of_mem_support (by rw [hsupportOne]; simp)
  have hXinOne : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hXoutTwo : atomX ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp [Ne.symm hAX, Ne.symm hBX, hXY]
  have hYinTwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hYoutOne : atomY ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp [Ne.symm hAY, Ne.symm hBY, Ne.symm hXY]
  have hXlabel : atomX ∈ datumTightSupport data.tightDir label :=
    data.pairCircuit_mem_support_of_sdiff hmem hpos hne hcoeffOne hpair hXinOne hXoutTwo
  have hYlabel : atomY ∈ datumTightSupport data.tightDir label :=
    data.pairCircuit_mem_support_of_sdiff hmem hpos (Ne.symm hne) hcoeffTwo
      (fun slot htwoNe honeNe => hpair slot honeNe htwoNe) hYinTwo hYoutOne
  -- the shared pair reads one line only
  have hline : data.tightDir label atomA
        * data.tightDir (data.basisLabel slotOne) atomB
      - data.tightDir label atomB
        * data.tightDir (data.basisLabel slotOne) atomA = 0 := by
    rw [data.pair_reconstruction hmem hpos hne hpair atomA,
      data.pair_reconstruction hmem hpos hne hpair atomB]
    linear_combination (-(data.labelCoeff label slotTwo)) * hwedge
  have hAdead : data.tightDir label atomA = 0 := by
    by_contra hAlive
    have hAlabel : atomA ∈ datumTightSupport data.tightDir label :=
      mem_datumTightSupport.mpr hAlive
    have htriple : ({atomA, atomX, atomY} : Finset (Fin 6))
        ⊆ datumTightSupport data.tightDir label := by
      intro probe hprobe
      simp only [Finset.mem_insert, Finset.mem_singleton] at hprobe
      rcases hprobe with heq | heq | heq
      · exact heq ▸ hAlabel
      · exact heq ▸ hXlabel
      · exact heq ▸ hYlabel
    have htripleCard : ({atomA, atomX, atomY} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hAX, hAY]),
        Finset.card_insert_of_notMem (by simp [hXY]), Finset.card_singleton]
    have hlabelCard : (datumTightSupport data.tightDir label).card ≤ 3 := by
      have hsub := datumTightSupport_subset data.hdata hmem
      have hcard := Finset.card_le_card hsub
      rwa [data.hdata.activeSubset_card label hmem] at hcard
    have hlabelEq : datumTightSupport data.tightDir label = {atomA, atomX, atomY} :=
      (Finset.eq_of_subset_of_card_le htriple (by rw [htripleCard]; exact hlabelCard)).symm
    have hBdead : data.tightDir label atomB = 0 := by
      by_contra hBlive
      have hBlabel : atomB ∈ datumTightSupport data.tightDir label :=
        mem_datumTightSupport.mpr hBlive
      rw [hlabelEq] at hBlabel
      simp only [Finset.mem_insert, Finset.mem_singleton] at hBlabel
      rcases hBlabel with heq | heq | heq
      · exact hAB heq.symm
      · exact hBX heq
      · exact hBY heq
    rw [hBdead, zero_mul, sub_zero] at hline
    exact hAlive ((mul_eq_zero.mp hline).resolve_right hliveOneB)
  refine ⟨hAdead, ?_⟩
  rw [hAdead, zero_mul, zero_sub, neg_eq_zero] at hline
  exact (mul_eq_zero.mp hline).resolve_right hliveOneA

/-- **THE SPLIT PAIR MINOR.**  In the split branch a dead wedge makes the
circuit label a support-two label on the two foreign atoms, thus the
shifted gap minor on that pair vanishes. -/
theorem splitCircuit_pair_minor_of_dead_wedge (data : SharedPrivateData crux)
    {label : data.activeIndex} (hmem : label ∈ data.activeSet)
    (hpos : 0 < data.reducedWeight label)
    {slotOne slotTwo : Fin data.basisCount} (hne : slotOne ≠ slotTwo)
    (hcoeffOne : data.labelCoeff label slotOne ≠ 0)
    (hcoeffTwo : data.labelCoeff label slotTwo ≠ 0)
    (hpair : ∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
      data.labelCoeff label slot = 0)
    {atomA atomB atomX atomY : Fin 6}
    (hAB : atomA ≠ atomB) (hAX : atomA ≠ atomX) (hAY : atomA ≠ atomY)
    (hBX : atomB ≠ atomX) (hBY : atomB ≠ atomY) (hXY : atomX ≠ atomY)
    (hsupportOne : datumTightSupport data.tightDir (data.basisLabel slotOne)
      = {atomA, atomB, atomX})
    (hsupportTwo : datumTightSupport data.tightDir (data.basisLabel slotTwo)
      = {atomA, atomB, atomY})
    (hwedge : data.tightDir (data.basisLabel slotOne) atomA
        * data.tightDir (data.basisLabel slotTwo) atomB
      - data.tightDir (data.basisLabel slotOne) atomB
        * data.tightDir (data.basisLabel slotTwo) atomA = 0) :
    chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomX atomY
        * chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight atomX atomY
      = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomX atomX
          - chartObjective (chartPointOfDesign crux.design))
        * (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight atomY atomY
          - chartObjective (chartPointOfDesign crux.design)) := by
  classical
  obtain ⟨hAdead, hBdead⟩ := data.splitCircuit_label_dead_on_shared hmem hpos hne
    hcoeffOne hcoeffTwo hpair hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo hwedge
  have hXinOne : atomX ∈ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp
  have hXoutTwo : atomX ∉ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp [Ne.symm hAX, Ne.symm hBX, hXY]
  have hYinTwo : atomY ∈ datumTightSupport data.tightDir (data.basisLabel slotTwo) := by
    rw [hsupportTwo]; simp
  have hYoutOne : atomY ∉ datumTightSupport data.tightDir (data.basisLabel slotOne) := by
    rw [hsupportOne]; simp [Ne.symm hAY, Ne.symm hBY, Ne.symm hXY]
  have hXlabel : atomX ∈ datumTightSupport data.tightDir label :=
    data.pairCircuit_mem_support_of_sdiff hmem hpos hne hcoeffOne hpair hXinOne hXoutTwo
  have hYlabel : atomY ∈ datumTightSupport data.tightDir label :=
    data.pairCircuit_mem_support_of_sdiff hmem hpos (Ne.symm hne) hcoeffTwo
      (fun slot htwoNe honeNe => hpair slot honeNe htwoNe) hYinTwo hYoutOne
  have hlabelSupp : ∀ atomIndex : Fin 6, atomIndex ≠ atomX → atomIndex ≠ atomY →
      data.tightDir label atomIndex = 0 := by
    intro atomIndex hX hY
    by_cases hA : atomIndex = atomA
    · rw [hA]; exact hAdead
    by_cases hB : atomIndex = atomB
    · rw [hB]; exact hBdead
    rw [data.pair_reconstruction hmem hpos hne hpair atomIndex,
      data.basis_dead_of_notMem_support (slot := slotOne)
        (by rw [hsupportOne]; simp [hA, hB, hX]),
      data.basis_dead_of_notMem_support (slot := slotTwo)
        (by rw [hsupportTwo]; simp [hA, hB, hY])]
    ring
  exact gap_pair_minor_eq_zero_of_pair_supported data.hdata hmem hXY
    (datumTightSupport_subset data.hdata hmem hXlabel)
    (datumTightSupport_subset data.hdata hmem hYlabel) hlabelSupp
    (mem_datumTightSupport.mp hXlabel) (mem_datumTightSupport.mp hYlabel)

end SharedPrivateData

/-! ## Layer 5 — the three narrowed circuit residues -/

/-- **THE IDENTICAL PAIR RESIDUE.**  A pair circuit whose two basis
supports agree, together with the rank-one shifted gap block that the
agreement forces. -/
def SharedPrivateCircuitPairIdenticalClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomU atomV atomS : Fin 6, atomU ≠ atomV → atomU ≠ atomS → atomV ≠ atomS →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomU, atomV, atomS} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomU, atomV, atomS} →
        GapBlockRankOne (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          (chartObjective (chartPointOfDesign crux.design)) atomU atomV atomS →
        False

/-- **THE SPLIT PAIR RESIDUE.**  A pair circuit whose two basis supports
share exactly two atoms, together with the two foreign tight rows that
the sharing forces. -/
def SharedPrivateCircuitPairSplitClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomA atomB atomX atomY : Fin 6,
        atomA ≠ atomB → atomA ≠ atomX → atomA ≠ atomY →
        atomB ≠ atomX → atomB ≠ atomY → atomX ≠ atomY →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomA, atomB, atomX} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomA, atomB, atomY} →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotTwo)) atomX = 0 →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotOne)) atomY = 0 →
        False

/-- **THE DISTINCT WIDE RESIDUE.**  A wide circuit whose three live
supports do not all agree. -/
def SharedPrivateCircuitWideDistinctClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo slotThree : Fin data.basisCount,
      slotOne ≠ slotTwo → slotOne ≠ slotThree → slotTwo ≠ slotThree →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      data.labelCoeff label slotThree ≠ 0 →
      ¬ (datumTightSupport data.tightDir (data.basisLabel slotTwo)
            = datumTightSupport data.tightDir (data.basisLabel slotOne)
          ∧ datumTightSupport data.tightDir (data.basisLabel slotThree)
            = datumTightSupport data.tightDir (data.basisLabel slotOne)) →
      False

/-- **THE LIVE-WEDGE SPLIT RESIDUE.**  The split branch whose two basis
columns have a live wedge on the two shared atoms. -/
def SharedPrivateCircuitSplitWedgeClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomA atomB atomX atomY : Fin 6,
        atomA ≠ atomB → atomA ≠ atomX → atomA ≠ atomY →
        atomB ≠ atomX → atomB ≠ atomY → atomX ≠ atomY →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomA, atomB, atomX} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomA, atomB, atomY} →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotTwo)) atomX = 0 →
        (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ data.tightDir (data.basisLabel slotOne)) atomY = 0 →
        data.tightDir (data.basisLabel slotOne) atomA
            * data.tightDir (data.basisLabel slotTwo) atomB
          - data.tightDir (data.basisLabel slotOne) atomB
            * data.tightDir (data.basisLabel slotTwo) atomA ≠ 0 →
        False

/-- **THE DEAD-WEDGE SPLIT RESIDUE.**  The split branch whose circuit
label collapses to a support-two label on the two foreign atoms, with the
vanishing pair minor that the collapse forces. -/
def SharedPrivateCircuitSplitPairClosed : Prop :=
  ∀ (crux : SixThreeCrux) (data : SharedPrivateData crux)
    (label : data.activeIndex),
    label ∈ data.activeSet →
    0 < data.reducedWeight label →
    ∀ slotOne slotTwo : Fin data.basisCount, slotOne ≠ slotTwo →
      data.labelCoeff label slotOne ≠ 0 →
      data.labelCoeff label slotTwo ≠ 0 →
      (∀ slot, slot ≠ slotOne → slot ≠ slotTwo →
        data.labelCoeff label slot = 0) →
      ∀ atomA atomB atomX atomY : Fin 6,
        atomA ≠ atomB → atomA ≠ atomX → atomA ≠ atomY →
        atomB ≠ atomX → atomB ≠ atomY → atomX ≠ atomY →
        datumTightSupport data.tightDir (data.basisLabel slotOne)
          = {atomA, atomB, atomX} →
        datumTightSupport data.tightDir (data.basisLabel slotTwo)
          = {atomA, atomB, atomY} →
        data.tightDir label atomA = 0 →
        data.tightDir label atomB = 0 →
        chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomX atomY
            * chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight atomX atomY
          = (chartStationaryGap (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight atomX atomX
              - chartObjective (chartPointOfDesign crux.design))
            * (chartStationaryGap (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight atomY atomY
              - chartObjective (chartPointOfDesign crux.design)) →
        False

/-! ## Layer 6 — the narrowing and the dispatch -/

/-- **THE PAIR BRANCH SPLIT.**  A pair circuit shares two atoms or three.
Three atoms make the two supports agree and the rank-one link fires; two
atoms give the split shape with its two foreign tight rows. -/
theorem sharedPrivateCircuitPairSharedClosed_of_branches
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hsplit : SharedPrivateCircuitPairSplitClosed) :
    SharedPrivateCircuitPairSharedClosed := by
  classical
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    hinter hcaptureOne hcaptureTwo
  set supportOne := datumTightSupport data.tightDir (data.basisLabel slotOne)
    with hsupportOneDef
  set supportTwo := datumTightSupport data.tightDir (data.basisLabel slotTwo)
    with hsupportTwoDef
  have hcardOne : supportOne.card = 3 := by
    rw [hsupportOneDef]; exact data.hthree slotOne
  have hcardTwo : supportTwo.card = 3 := by
    rw [hsupportTwoDef]; exact data.hthree slotTwo
  have hinterLe : (supportOne ∩ supportTwo).card ≤ 3 := by
    rw [← hcardOne]
    exact Finset.card_le_card Finset.inter_subset_left
  interval_cases hcard : (supportOne ∩ supportTwo).card
  · -- the two supports share exactly two atoms
    obtain ⟨atomA, atomB, hAB, hinterEq⟩ := Finset.card_eq_two.mp hcard
    have hsdiffOne : (supportOne \ supportTwo).card = 1 := by
      have hsplitOne := Finset.card_sdiff_add_card_inter supportOne supportTwo
      omega
    have hsdiffTwo : (supportTwo \ supportOne).card = 1 := by
      have hsplitTwo := Finset.card_sdiff_add_card_inter supportTwo supportOne
      have hcomm : (supportTwo ∩ supportOne).card = (supportOne ∩ supportTwo).card := by
        rw [Finset.inter_comm]
      omega
    obtain ⟨atomX, hXeq⟩ := Finset.card_eq_one.mp hsdiffOne
    obtain ⟨atomY, hYeq⟩ := Finset.card_eq_one.mp hsdiffTwo
    have hXmem : atomX ∈ supportOne \ supportTwo := by
      rw [hXeq]; exact Finset.mem_singleton_self _
    have hYmem : atomY ∈ supportTwo \ supportOne := by
      rw [hYeq]; exact Finset.mem_singleton_self _
    rw [Finset.mem_sdiff] at hXmem hYmem
    have hXinOne : atomX ∈ supportOne := hXmem.1
    have hXoutTwo : atomX ∉ supportTwo := hXmem.2
    have hYinTwo : atomY ∈ supportTwo := hYmem.1
    have hYoutOne : atomY ∉ supportOne := hYmem.2
    have hAinter : atomA ∈ supportOne ∩ supportTwo := by
      rw [hinterEq]; simp
    have hBinter : atomB ∈ supportOne ∩ supportTwo := by
      rw [hinterEq]; simp
    have hAX : atomA ≠ atomX := fun heq =>
      hXoutTwo (heq ▸ (Finset.mem_inter.mp hAinter).2)
    have hBX : atomB ≠ atomX := fun heq =>
      hXoutTwo (heq ▸ (Finset.mem_inter.mp hBinter).2)
    have hAY : atomA ≠ atomY := fun heq =>
      hYoutOne (heq ▸ (Finset.mem_inter.mp hAinter).1)
    have hBY : atomB ≠ atomY := fun heq =>
      hYoutOne (heq ▸ (Finset.mem_inter.mp hBinter).1)
    have hXY : atomX ≠ atomY := fun heq =>
      hYoutOne (heq ▸ hXinOne)
    have htripleCardOne : ({atomA, atomB, atomX} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hAB, hAX]),
        Finset.card_insert_of_notMem (by simp [hBX]), Finset.card_singleton]
    have htripleCardTwo : ({atomA, atomB, atomY} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hAB, hAY]),
        Finset.card_insert_of_notMem (by simp [hBY]), Finset.card_singleton]
    have hsupportOneEq : supportOne = {atomA, atomB, atomX} := by
      refine (Finset.eq_of_subset_of_card_le ?_ (by rw [hcardOne, htripleCardOne])).symm
      intro probe hprobe
      simp only [Finset.mem_insert, Finset.mem_singleton] at hprobe
      rcases hprobe with heq | heq | heq
      · exact heq ▸ (Finset.mem_inter.mp hAinter).1
      · exact heq ▸ (Finset.mem_inter.mp hBinter).1
      · exact heq ▸ hXinOne
    have hsupportTwoEq : supportTwo = {atomA, atomB, atomY} := by
      refine (Finset.eq_of_subset_of_card_le ?_ (by rw [hcardTwo, htripleCardTwo])).symm
      intro probe hprobe
      simp only [Finset.mem_insert, Finset.mem_singleton] at hprobe
      rcases hprobe with heq | heq | heq
      · exact heq ▸ (Finset.mem_inter.mp hAinter).2
      · exact heq ▸ (Finset.mem_inter.mp hBinter).2
      · exact heq ▸ hYinTwo
    refine hsplit crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo
      hpair atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOneEq
      hsupportTwoEq ?_ ?_
    · have hzero := data.basis_dead_of_notMem_support (slot := slotTwo) hXoutTwo
      rw [chart_tight_row_of_capture_zero
        (data.pairCircuit_capture_eq_zero hmem hpos hne hcoeffOne hcoeffTwo hpair
          hXinOne hXoutTwo) hzero, hzero, mul_zero]
    · have hzero := data.basis_dead_of_notMem_support (slot := slotOne) hYoutOne
      rw [chart_tight_row_of_capture_zero
        (data.pairCircuit_capture_eq_zero hmem hpos (Ne.symm hne) hcoeffTwo hcoeffOne
          (fun slot htwoNe honeNe => hpair slot honeNe htwoNe) hYinTwo hYoutOne) hzero,
        hzero, mul_zero]
  · -- the two supports agree
    have hsame : supportOne = supportTwo := by
      have hone : supportOne ∩ supportTwo = supportOne :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hcardOne, hcard])
      have htwo : supportOne ∩ supportTwo = supportTwo :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hcardTwo, hcard])
      rw [← hone, htwo]
    obtain ⟨atomU, atomV, atomS, hUV, hUS, hVS, hsupportEq⟩ :=
      Finset.card_eq_three.mp hcardOne
    refine hidentical crux data label hmem hpos slotOne slotTwo hne hcoeffOne
      hcoeffTwo hpair atomU atomV atomS hUV hUS hVS hsupportEq
      (by rw [← hsupportTwoDef, ← hsame]; exact hsupportEq) ?_
    exact data.gapBlockRankOne_of_identical_support hne hUV hUS hVS hsupportEq
      (by rw [← hsupportTwoDef, ← hsame]; exact hsupportEq)

/-- **THE WEDGE DICHOTOMY.**  The split branch splits again on the wedge
of the two basis columns over the shared pair.  A live wedge is the first
fine residue.  A dead wedge collapses the circuit label to the two foreign
atoms and prices their pair minor, which is the second fine residue. -/
theorem sharedPrivateCircuitPairSplitClosed_of_wedge
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed) :
    SharedPrivateCircuitPairSplitClosed := by
  classical
  intro crux data label hmem hpos slotOne slotTwo hne hcoeffOne hcoeffTwo hpair
    atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
    hrowX hrowY
  by_cases hwedge : data.tightDir (data.basisLabel slotOne) atomA
        * data.tightDir (data.basisLabel slotTwo) atomB
      - data.tightDir (data.basisLabel slotOne) atomB
        * data.tightDir (data.basisLabel slotTwo) atomA = 0
  · obtain ⟨hAdead, hBdead⟩ := data.splitCircuit_label_dead_on_shared hmem hpos hne
      hcoeffOne hcoeffTwo hpair hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo
      hwedge
    exact hwedgeDead crux data label hmem hpos slotOne slotTwo hne hcoeffOne
      hcoeffTwo hpair atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne
      hsupportTwo hAdead hBdead
      (data.splitCircuit_pair_minor_of_dead_wedge hmem hpos hne hcoeffOne hcoeffTwo
        hpair hAB hAX hAY hBX hBY hXY hsupportOne hsupportTwo hwedge)
  · exact hwedgeLive crux data label hmem hpos slotOne slotTwo hne hcoeffOne
      hcoeffTwo hpair atomA atomB atomX atomY hAB hAX hAY hBX hBY hXY hsupportOne
      hsupportTwo hrowX hrowY hwedge

/-- **THE WIDE NARROWING.**  A wide circuit whose three live supports all
agree carries three basis columns on one triple, and the triple kill
refuses that.  Thus the wide residue needs the distinct branch only. -/
theorem sharedPrivateCircuitWideClosed_of_distinct
    (hdistinct : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateCircuitWideClosed := by
  classical
  intro crux data label hmem hpos slotOne slotTwo slotThree hOneTwo hOneThree
    hTwoThree hcoeffOne hcoeffTwo hcoeffThree
  by_cases hsame : datumTightSupport data.tightDir (data.basisLabel slotTwo)
        = datumTightSupport data.tightDir (data.basisLabel slotOne)
      ∧ datumTightSupport data.tightDir (data.basisLabel slotThree)
        = datumTightSupport data.tightDir (data.basisLabel slotOne)
  · exact data.false_of_triple_identical_support hOneTwo hOneThree hTwoThree
      hsame.1 hsame.2
  · exact hdistinct crux data label hmem hpos slotOne slotTwo slotThree hOneTwo
      hOneThree hTwoThree hcoeffOne hcoeffTwo hcoeffThree hsame

/-- **THE CIRCUIT BRANCH DISPATCH.**  The three narrowed circuit residues
and the boundary residue close the generic shared-private kill.  The
deficit stratum is a theorem, thus it needs no hypothesis. -/
theorem sharedPrivateKilled_of_circuit_branches
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hsplit : SharedPrivateCircuitPairSplitClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_leak_strata
    (sharedPrivateCircuitPairSharedClosed_of_branches hidentical hsplit)
    (sharedPrivateCircuitWideClosed_of_distinct hwide) hboundary

/-- The rank-four bridge through the circuit branches. -/
theorem rankFourSharedPrivateClosed_of_circuit_branches
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hsplit : SharedPrivateCircuitPairSplitClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_circuit_branches hidentical hsplit hwide hboundary)

/-- The rank-five bridge through the circuit branches. -/
theorem rankFiveSharedPrivateClosed_of_circuit_branches
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hsplit : SharedPrivateCircuitPairSplitClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_circuit_branches hidentical hsplit hwide hboundary)

/-- The rank-six bridge through the circuit branches. -/
theorem rankSixSharedPrivateClosed_of_circuit_branches
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hsplit : SharedPrivateCircuitPairSplitClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_circuit_branches hidentical hsplit hwide hboundary)

/-! ## Layer 7 — the fine circuit lattice -/

/-- **THE FINE CIRCUIT DISPATCH.**  The four fine circuit residues and the
boundary residue close the generic shared-private kill. -/
theorem sharedPrivateKilled_of_circuit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_circuit_branches hidentical
    (sharedPrivateCircuitPairSplitClosed_of_wedge hwedgeLive hwedgeDead) hwide
    hboundary

/-- The rank-four bridge through the fine circuit lattice. -/
theorem rankFourSharedPrivateClosed_of_circuit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_circuit_lattice hidentical hwedgeLive hwedgeDead hwide
      hboundary)

/-- The rank-five bridge through the fine circuit lattice. -/
theorem rankFiveSharedPrivateClosed_of_circuit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_circuit_lattice hidentical hwedgeLive hwedgeDead hwide
      hboundary)

/-- The rank-six bridge through the fine circuit lattice. -/
theorem rankSixSharedPrivateClosed_of_circuit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hboundary : SharedPrivateBoundaryClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_circuit_lattice hidentical hwedgeLive hwedgeDead hwide
      hboundary)

/-! ## Layer 8 — the whole of closure two on five residues -/

/-- **THE EXTRAS FROM THE CIRCUIT LATTICE.**  The four fine circuit
residues close the whole extras stratum. -/
theorem sharedPrivateExtrasClosed_of_circuit_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed) :
    SharedPrivateExtrasClosed :=
  sharedPrivateExtrasClosed_of_width
    (sharedPrivateCircuitPairClosed_of_shared
      (sharedPrivateCircuitPairSharedClosed_of_branches hidentical
        (sharedPrivateCircuitPairSplitClosed_of_wedge hwedgeLive hwedgeDead)))
    (sharedPrivateCircuitWideClosed_of_distinct hwide)

/-- **THE WHOLE OF CLOSURE TWO ON FIVE RESIDUES.**  The generic
shared-private kill needs the four fine circuit residues and the confined
basis-count-five boundary residue.  The deficit stratum is a theorem, thus
it costs nothing. -/
theorem sharedPrivateKilled_of_sharedPrivate_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    SharedPrivateKilled :=
  sharedPrivateKilled_of_confined_strata
    (sharedPrivateExtrasClosed_of_circuit_lattice hidentical hwedgeLive hwedgeDead
      hwide) hconfined

/-- Closure two of the rank-four rung on the five residues. -/
theorem rankFourSharedPrivateClosed_of_sharedPrivate_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFourSharedPrivateClosed :=
  rankFourSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_sharedPrivate_lattice hidentical hwedgeLive hwedgeDead
      hwide hconfined)

/-- The shared-private closure of the rank-five rung on the five
residues. -/
theorem rankFiveSharedPrivateClosed_of_sharedPrivate_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankFiveSharedPrivateClosed :=
  rankFiveSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_sharedPrivate_lattice hidentical hwedgeLive hwedgeDead
      hwide hconfined)

/-- The shared-private closure of the rank-six rung on the five
residues. -/
theorem rankSixSharedPrivateClosed_of_sharedPrivate_lattice
    (hidentical : SharedPrivateCircuitPairIdenticalClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairClosed)
    (hwide : SharedPrivateCircuitWideDistinctClosed)
    (hconfined : SharedPrivateBoundaryFiveConfinedClosed) :
    RankSixSharedPrivateClosed :=
  rankSixSharedPrivateClosed_of_killed
    (sharedPrivateKilled_of_sharedPrivate_lattice hidentical hwedgeLive hwedgeDead
      hwide hconfined)

end Gtz
