import Gtz.Wave.DoubledPairClosure
import Gtz.Wave.AllPrivateSupportKill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The rank-four rung assembly — the rung modulo five named closures

The pinned dispatch splits every rank-four crux datum into three census
branches.  This file reifies the dispatch tuple as THE RANK-FOUR FRAME,
names the five remaining closure obligations as standalone propositions
over frames, discharges everything the landed kills already close, and
assembles the rung: the five closures imply
`IsSixThreeAssemblyRankExcluded 4`.

The five named closures, with their branch of origin:

1. `RankFourSupportTwoClosed` — census branch one: some basis support has
   cardinality two.
2. `RankFourSharedPrivateClosed` — census branch two after the private
   split: the pinned slot's support carries a shared atom.  The fully
   private side is DEAD through the landed all-private-support kill.
3. `RankFourKFourClosed` — the dense K4 profile: every pair shares one
   atom.
4. `RankFourCycleIndependentClosed` — the labeled cycle with some nonzero
   cross determinant.
5. `RankFourBothParallelClosed` — the labeled cycle with both cross
   determinants zero: the named open sub-branch of the campaign.

Every other route is closed by landed theorems: the rank floor and caps,
the pinned dispatch, the all-private-support kill, the full-share kill,
the exact split, the cycle normalization, and the oriented routing.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.RankFourFrame` with `Gtz.SixThreeCrux.exists_rankFourFrame` — **THE
  FRAME.**
* `Gtz.RankFourSupportTwoClosed`, `Gtz.RankFourSharedPrivateClosed`,
  `Gtz.RankFourKFourClosed`, `Gtz.RankFourCycleIndependentClosed`,
  `Gtz.RankFourBothParallelClosed` — **THE FIVE CLOSURES.**
* `Gtz.RankFourFrame.false_of_multOne_branch` — the branch-two discharge.
* `Gtz.RankFourFrame.false_of_dense_branch` — the branch-three discharge.
* `Gtz.isSixThreeAssemblyRankExcluded_four_of_closures` — **THE RUNG
  MODULO THE CLOSURES.**

## Vacuity

The closures and the rung are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-! ## The rank-four frame -/

/-- **THE RANK-FOUR FRAME.**  The reified pinned-dispatch tuple: the
reduced datum, the four-label basis, the coefficient triple, and the
fourteen laws.  Every branch kill consumes a frame. -/
structure RankFourFrame (crux : SixThreeCrux) where
  /-- The label type of the datum. -/
  activeIndex : Type
  /-- The active label set. -/
  activeSet : Finset activeIndex
  /-- The block of each label. -/
  activeSubset : activeIndex → Finset (Fin 6)
  /-- The reduced multiplier weights. -/
  reducedWeight : activeIndex → ℝ
  /-- The tight directions. -/
  tightDir : activeIndex → Fin 6 → ℝ
  /-- The four-label basis. -/
  basisLabel : Fin 4 → activeIndex
  /-- The left inverse of the basis columns. -/
  leftInv : Matrix (Fin 4) (Fin 6) ℝ
  /-- The coefficient matrix of the projection. -/
  coeff : Matrix (Fin 4) (Fin 4) ℝ
  /-- The coefficient Gram core. -/
  gram : Matrix (Fin 4) (Fin 4) ℝ
  /-- The reduced datum is stationary. -/
  hdata : IsChartStationaryData 3
    (chartPointOfDesign crux.design).chart
    (chartPointOfDesign crux.design).weight
    (chartObjective (chartPointOfDesign crux.design))
    activeSet activeSubset reducedWeight tightDir
  /-- The basis is injective. -/
  hinjective : Function.Injective basisLabel
  /-- Every basis label is positive. -/
  hmem : ∀ columnIndex, basisLabel columnIndex
    ∈ positiveActiveSet activeSet reducedWeight
  /-- The basis spans the assembly range. -/
  hspan : Submodule.span ℝ
      (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
    = LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet reducedWeight tightDir))
  /-- The left inverse law. -/
  hleft : leftInv * tightBasisColumns tightDir basisLabel = 1
  /-- The coefficient representation of the projection. -/
  hrepresentation : (chartPointOfDesign crux.design).chart
      * tightBasisColumns tightDir basisLabel
    = tightBasisColumns tightDir basisLabel * coeff
  /-- The coefficient matrix is idempotent. -/
  hidempotent : coeff * coeff = coeff
  /-- The Gram form of the assembly. -/
  hHform : tightBasisColumns tightDir basisLabel * gram
      * (tightBasisColumns tightDir basisLabel)ᵀ
    = chartMultiplierAssembly activeSet reducedWeight tightDir
  /-- The Gram core is symmetric. -/
  hsymmH : gramᵀ = gram
  /-- The Gram core is positive semidefinite. -/
  hpsd : gram.PosSemidef
  /-- The Gram core has a trivial kernel. -/
  hker : ∀ coeffVec : Fin 4 → ℝ, gram *ᵥ coeffVec = 0 → coeffVec = 0
  /-- The exchange law. -/
  hexchange : coeff * gram = gram * coeffᵀ
  /-- The trace budget. -/
  htrace : Matrix.trace coeff = 2

/-- Every basis label of a frame is active. -/
theorem RankFourFrame.hmemAll {crux : SixThreeCrux} (frame : RankFourFrame crux)
    (columnIndex : Fin 4) : frame.basisLabel columnIndex ∈ frame.activeSet :=
  positiveActiveSet_subset_activeSet (frame.hmem columnIndex)

/-- The crux value is negative at every frame. -/
theorem RankFourFrame.hvalueNeg {crux : SixThreeCrux}
    (_frame : RankFourFrame crux) :
    chartObjective (chartPointOfDesign crux.design) < 0 :=
  crux.hasNegativeChartValue

/-- **THE FRAME EXTRACTION.**  Every rank-four crux datum yields a frame
together with the pinned census trichotomy over its basis. -/
theorem SixThreeCrux.exists_rankFourFrame (crux : SixThreeCrux)
    {activeIndex : Type} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hrankFour : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 4) :
    ∃ frame : RankFourFrame crux,
      frame.activeIndex = activeIndex
      ∧ ((∃ columnIndex, (datumTightSupport frame.tightDir
            (frame.basisLabel columnIndex)).card = 2)
        ∨ ((∀ columnIndex, (datumTightSupport frame.tightDir
              (frame.basisLabel columnIndex)).card = 3)
            ∧ ∃ (atomIndex : Fin 6) (privateSlot : Fin 4),
                basisSupportMultiplicity frame.tightDir frame.basisLabel
                  atomIndex = 1
                ∧ atomIndex ∈ frame.activeSubset (frame.basisLabel privateSlot)
                ∧ frame.tightDir (frame.basisLabel privateSlot) atomIndex ≠ 0
                ∧ (∀ columnIndex, columnIndex ≠ privateSlot →
                    frame.tightDir (frame.basisLabel columnIndex) atomIndex = 0)
                ∧ frame.coeff privateSlot privateSlot
                    = chartObjective (chartPointOfDesign crux.design)
                      + (chartPointOfDesign crux.design).weight atomIndex)
        ∨ ((∀ columnIndex, (datumTightSupport frame.tightDir
              (frame.basisLabel columnIndex)).card = 3)
            ∧ ∀ atomIndex, basisSupportMultiplicity frame.tightDir
                frame.basisLabel atomIndex = 2)) := by
  obtain ⟨reducedWeight, basisLabel, leftInv, coeff, gram, hreducedData,
    _hassemblyEq, hinjective, hmem, hspan, hleft, hrepresentation,
    hidempotent, hHform, hsymmH, hpsd, hker, hexchange, htrace, htrichotomy⟩ :=
    crux.exists_rankFour_pinned_dispatch hdata hrankFour
  exact ⟨⟨activeIndex, activeSet, activeSubset, reducedWeight, tightDir,
    basisLabel, leftInv, coeff, gram, hreducedData, hinjective, hmem, hspan,
    hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace⟩, rfl, htrichotomy⟩

/-! ## The five named closures -/

/-- **CLOSURE ONE.**  Census branch one: a basis support of cardinality
two dies at every frame. -/
def RankFourSupportTwoClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux) (columnIndex : Fin 4),
    (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
    False

/-- **CLOSURE TWO.**  Census branch two with a shared atom: the pinned
slot's support carries an atom of multiplicity at least two, all supports
have cardinality three, and the frame dies. -/
def RankFourSharedPrivateClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux)
    (privateSlot : Fin 4) (pinAtom sharedAtom : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    basisSupportMultiplicity frame.tightDir frame.basisLabel pinAtom = 1 →
    pinAtom ∈ frame.activeSubset (frame.basisLabel privateSlot) →
    frame.tightDir (frame.basisLabel privateSlot) pinAtom ≠ 0 →
    (∀ columnIndex, columnIndex ≠ privateSlot →
      frame.tightDir (frame.basisLabel columnIndex) pinAtom = 0) →
    frame.coeff privateSlot privateSlot
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight pinAtom →
    sharedAtom ∈ datumTightSupport frame.tightDir
      (frame.basisLabel privateSlot) →
    2 ≤ basisSupportMultiplicity frame.tightDir frame.basisLabel sharedAtom →
    False

/-- **CLOSURE THREE.**  The dense K4 profile dies at every frame. -/
def RankFourKFourClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux),
    (∀ atomIndex, basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex = 2) →
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    (∀ slotK slotL : Fin 4, slotK ≠ slotL →
      pairShare frame.tightDir frame.basisLabel slotK slotL = 1) →
    False

/-- **CLOSURE FOUR.**  The labeled cycle with some nonzero cross
determinant dies at every frame. -/
def RankFourCycleIndependentClosed : Prop :=
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
    (frame.tightDir (frame.basisLabel slotK) pairAtomOne
        * frame.tightDir (frame.basisLabel slotL) pairAtomTwo
      - frame.tightDir (frame.basisLabel slotK) pairAtomTwo
        * frame.tightDir (frame.basisLabel slotL) pairAtomOne ≠ 0
      ∨ frame.tightDir (frame.basisLabel slotM) coAtomOne
        * frame.tightDir (frame.basisLabel slotN) coAtomTwo
      - frame.tightDir (frame.basisLabel slotM) coAtomTwo
        * frame.tightDir (frame.basisLabel slotN) coAtomOne ≠ 0) →
    False

/-- **CLOSURE FIVE.**  The labeled cycle with both cross determinants
zero: the named open sub-branch of the campaign. -/
def RankFourBothParallelClosed : Prop :=
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
    False

/-! ## The branch discharges -/

/-- **THE BRANCH-TWO DISCHARGE.**  At a frame with all supports of
cardinality three and a pinned multiplicity-one atom, the private split
routes: the fully private side dies through the landed kill, and the
shared side goes to closure two. -/
theorem RankFourFrame.false_of_multOne_branch {crux : SixThreeCrux}
    (frame : RankFourFrame crux)
    (hclosureTwo : RankFourSharedPrivateClosed)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    {pinAtom : Fin 6} {privateSlot : Fin 4}
    (hmultOne : basisSupportMultiplicity frame.tightDir frame.basisLabel
      pinAtom = 1)
    (hatomMem : pinAtom ∈ frame.activeSubset (frame.basisLabel privateSlot))
    (hslotNe : frame.tightDir (frame.basisLabel privateSlot) pinAtom ≠ 0)
    (hprivate : ∀ columnIndex, columnIndex ≠ privateSlot →
      frame.tightDir (frame.basisLabel columnIndex) pinAtom = 0)
    (hpin : frame.coeff privateSlot privateSlot
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight pinAtom) :
    False := by
  rcases all_private_or_exists_shared_atom
      (tightDir := frame.tightDir) frame.basisLabel privateSlot with
    hallPrivate | ⟨sharedAtom, hsharedMem, hsharedMult⟩
  · exact false_of_all_private_support frame.hdata frame.hvalueNeg
      frame.basisLabel frame.hleft frame.hrepresentation frame.htrace
      frame.hmemAll (hthree privateSlot)
      (fun columnIndex _ => hthree columnIndex) hallPrivate
  · exact hclosureTwo crux frame privateSlot pinAtom sharedAtom hthree
      hmultOne hatomMem hslotNe hprivate hpin hsharedMem hsharedMult

/-- **THE BRANCH-THREE DISCHARGE.**  At a dense frame the oriented routing
consumes the three dense closures. -/
theorem RankFourFrame.false_of_dense_branch {crux : SixThreeCrux}
    (frame : RankFourFrame crux)
    (hclosureKFour : RankFourKFourClosed)
    (hclosureIndependent : RankFourCycleIndependentClosed)
    (hclosureParallel : RankFourBothParallelClosed)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    (hmultTwo : ∀ atomIndex, basisSupportMultiplicity frame.tightDir
      frame.basisLabel atomIndex = 2) :
    False := by
  refine false_of_dense_branch_oriented frame.hdata frame.hvalueNeg
    frame.basisLabel frame.hleft frame.hrepresentation frame.htrace
    hmultTwo hthree frame.hmemAll
    (fun hKFour => hclosureKFour crux frame hmultTwo hthree hKFour)
    ?_ ?_
  · intro slotK slotL slotM slotN pairAtomOne pairAtomTwo coAtomOne coAtomTwo
      singleKM singleLN hKL hMN hKM hKN hLM hLN hpairNe hcoNe hpairSet hcoSet
      hKMset hLNset hsuppK hsuppL hsuppM hsuppN hdet
    exact hclosureIndependent crux frame slotK slotL slotM slotN pairAtomOne
      pairAtomTwo coAtomOne coAtomTwo singleKM singleLN hmultTwo hKL hMN hKM
      hKN hLM hLN hpairNe hcoNe hpairSet hcoSet hKMset hLNset hsuppK hsuppL
      hsuppM hsuppN hdet
  · intro slotK slotL slotM slotN pairAtomOne pairAtomTwo coAtomOne coAtomTwo
      singleKM singleLN hKL hMN hKM hKN hLM hLN hpairNe hcoNe hpairSet hcoSet
      hKMset hLNset hsuppK hsuppL hsuppM hsuppN hdetKL hdetMN
    exact hclosureParallel crux frame slotK slotL slotM slotN pairAtomOne
      pairAtomTwo coAtomOne coAtomTwo singleKM singleLN hmultTwo hKL hMN hKM
      hKN hLM hLN hpairNe hcoNe hpairSet hcoSet hKMset hLNset hsuppK hsuppL
      hsuppM hsuppN hdetKL hdetMN

/-! ## The K4 normal form -/

/-- **THE THREE-SINGLES ENUMERATION.**  A support of cardinality three
with one atom shared against each other slot is exactly the three shared
atoms. -/
theorem support_enumeration_of_three_singles {size : ℕ}
    {activeIndex : Type*} {tightDir : activeIndex → (Fin size → ℝ)}
    {basisCount : ℕ} (basisLabel : Fin basisCount → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    {slotK slotL slotM slotN : Fin basisCount}
    (hKL : slotK ≠ slotL) (hKM : slotK ≠ slotM) (hKN : slotK ≠ slotN)
    (hLM : slotL ≠ slotM) (hLN : slotL ≠ slotN) (hMN : slotM ≠ slotN)
    (hcardK : (datumTightSupport tightDir (basisLabel slotK)).card = 3)
    {atomL atomM atomN : Fin size}
    (hmemL : atomL ∈ shareSet tightDir basisLabel slotK slotL)
    (hmemM : atomM ∈ shareSet tightDir basisLabel slotK slotM)
    (hmemN : atomN ∈ shareSet tightDir basisLabel slotK slotN) :
    datumTightSupport tightDir (basisLabel slotK) = {atomL, atomM, atomN} := by
  classical
  have hmemM' : atomM ∈ shareSet tightDir basisLabel slotM slotK := by
    rw [shareSet_comm]
    exact hmemM
  have hmemN' : atomN ∈ shareSet tightDir basisLabel slotN slotK := by
    rw [shareSet_comm]
    exact hmemN
  have hneLM : atomL ≠ atomM :=
    shareSet_disjoint_atom_ne basisLabel hmult hKL (Ne.symm hKM)
      (Ne.symm hLM) hmemL hmemM'
  have hneLN : atomL ≠ atomN :=
    shareSet_disjoint_atom_ne basisLabel hmult hKL (Ne.symm hKN)
      (Ne.symm hLN) hmemL hmemN'
  have hneMN : atomM ≠ atomN :=
    shareSet_disjoint_atom_ne basisLabel hmult hKM (Ne.symm hKN)
      (Ne.symm hMN) hmemM hmemN'
  have hnotL : atomL ∉ ({atomM, atomN} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hneLM heq
    · exact hneLN (Finset.mem_singleton.mp hmem')
  have hnotM : atomM ∉ ({atomN} : Finset (Fin size)) := fun hmem =>
    hneMN (Finset.mem_singleton.mp hmem)
  have hsubset : ({atomL, atomM, atomN} : Finset (Fin size))
      ⊆ datumTightSupport tightDir (basisLabel slotK) := by
    intro atomIndex hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · rw [heq]
      exact ((mem_shareSet_iff basisLabel slotK slotL).mp hmemL).1
    rcases Finset.mem_insert.mp hmem' with heq | hmem''
    · rw [heq]
      exact ((mem_shareSet_iff basisLabel slotK slotM).mp hmemM).1
    · rw [Finset.mem_singleton.mp hmem'']
      exact ((mem_shareSet_iff basisLabel slotK slotN).mp hmemN).1
  have hcardTriple : ({atomL, atomM, atomN} : Finset (Fin size)).card = 3 := by
    rw [Finset.card_insert_of_notMem hnotL,
      Finset.card_insert_of_notMem hnotM, Finset.card_singleton]
  symm
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hcardTriple, hcardK]

/-- **THE K4 ATOM LABELING.**  At the K4 profile the six share sets are
singletons on the literal slots, and the four supports enumerate as the
edge triples of the complete graph. -/
theorem kfour_atom_labeling {size : ℕ} {activeIndex : Type*}
    {tightDir : activeIndex → (Fin size → ℝ)}
    (basisLabel : Fin 4 → activeIndex)
    (hmult : ∀ atomIndex : Fin size,
      basisSupportMultiplicity tightDir basisLabel atomIndex = 2)
    (hcard : ∀ slotIndex : Fin 4,
      (datumTightSupport tightDir (basisLabel slotIndex)).card = 3)
    (hKFour : ∀ slotK slotL : Fin 4, slotK ≠ slotL →
      pairShare tightDir basisLabel slotK slotL = 1) :
    ∃ edgeKL edgeKM edgeKN edgeLM edgeLN edgeMN : Fin size,
      shareSet tightDir basisLabel 0 1 = {edgeKL}
      ∧ shareSet tightDir basisLabel 0 2 = {edgeKM}
      ∧ shareSet tightDir basisLabel 0 3 = {edgeKN}
      ∧ shareSet tightDir basisLabel 1 2 = {edgeLM}
      ∧ shareSet tightDir basisLabel 1 3 = {edgeLN}
      ∧ shareSet tightDir basisLabel 2 3 = {edgeMN}
      ∧ datumTightSupport tightDir (basisLabel 0) = {edgeKL, edgeKM, edgeKN}
      ∧ datumTightSupport tightDir (basisLabel 1) = {edgeKL, edgeLM, edgeLN}
      ∧ datumTightSupport tightDir (basisLabel 2) = {edgeKM, edgeLM, edgeMN}
      ∧ datumTightSupport tightDir (basisLabel 3) = {edgeKN, edgeLN, edgeMN} := by
  classical
  have hshare : ∀ slotK slotL : Fin 4, slotK ≠ slotL →
      (shareSet tightDir basisLabel slotK slotL).card = 1 := by
    intro slotK slotL hne
    rw [← pairShare_eq_card_shareSet]
    exact hKFour slotK slotL hne
  obtain ⟨edgeKL, hsetKL⟩ := Finset.card_eq_one.mp (hshare 0 1 (by decide))
  obtain ⟨edgeKM, hsetKM⟩ := Finset.card_eq_one.mp (hshare 0 2 (by decide))
  obtain ⟨edgeKN, hsetKN⟩ := Finset.card_eq_one.mp (hshare 0 3 (by decide))
  obtain ⟨edgeLM, hsetLM⟩ := Finset.card_eq_one.mp (hshare 1 2 (by decide))
  obtain ⟨edgeLN, hsetLN⟩ := Finset.card_eq_one.mp (hshare 1 3 (by decide))
  obtain ⟨edgeMN, hsetMN⟩ := Finset.card_eq_one.mp (hshare 2 3 (by decide))
  have hmemKL : edgeKL ∈ shareSet tightDir basisLabel 0 1 := by
    rw [hsetKL]
    exact Finset.mem_singleton_self _
  have hmemKM : edgeKM ∈ shareSet tightDir basisLabel 0 2 := by
    rw [hsetKM]
    exact Finset.mem_singleton_self _
  have hmemKN : edgeKN ∈ shareSet tightDir basisLabel 0 3 := by
    rw [hsetKN]
    exact Finset.mem_singleton_self _
  have hmemLM : edgeLM ∈ shareSet tightDir basisLabel 1 2 := by
    rw [hsetLM]
    exact Finset.mem_singleton_self _
  have hmemLN : edgeLN ∈ shareSet tightDir basisLabel 1 3 := by
    rw [hsetLN]
    exact Finset.mem_singleton_self _
  have hmemMN : edgeMN ∈ shareSet tightDir basisLabel 2 3 := by
    rw [hsetMN]
    exact Finset.mem_singleton_self _
  have hmemKL' : edgeKL ∈ shareSet tightDir basisLabel 1 0 := by
    rw [shareSet_comm]
    exact hmemKL
  have hmemKM' : edgeKM ∈ shareSet tightDir basisLabel 2 0 := by
    rw [shareSet_comm]
    exact hmemKM
  have hmemKN' : edgeKN ∈ shareSet tightDir basisLabel 3 0 := by
    rw [shareSet_comm]
    exact hmemKN
  have hmemLM' : edgeLM ∈ shareSet tightDir basisLabel 2 1 := by
    rw [shareSet_comm]
    exact hmemLM
  have hmemLN' : edgeLN ∈ shareSet tightDir basisLabel 3 1 := by
    rw [shareSet_comm]
    exact hmemLN
  have hmemMN' : edgeMN ∈ shareSet tightDir basisLabel 3 2 := by
    rw [shareSet_comm]
    exact hmemMN
  refine ⟨edgeKL, edgeKM, edgeKN, edgeLM, edgeLN, edgeMN, hsetKL, hsetKM,
    hsetKN, hsetLM, hsetLN, hsetMN, ?_, ?_, ?_, ?_⟩
  · exact support_enumeration_of_three_singles basisLabel hmult
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hcard 0) hmemKL hmemKM hmemKN
  · exact support_enumeration_of_three_singles basisLabel hmult
      (show (1 : Fin 4) ≠ 0 by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (hcard 1) hmemKL' hmemLM hmemLN
  · exact support_enumeration_of_three_singles basisLabel hmult
      (show (2 : Fin 4) ≠ 0 by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (hcard 2) hmemKM' hmemLM' hmemMN
  · exact support_enumeration_of_three_singles basisLabel hmult
      (show (3 : Fin 4) ≠ 0 by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (hcard 3) hmemKN' hmemLN' hmemMN'

/-- **THE LABELED K4 BRIDGE.**  A kill of the labeled K4 normal form
closes the K4 profile. -/
theorem rankFourKFourClosed_of_labeled
    (killLabeled : ∀ (crux : SixThreeCrux) (frame : RankFourFrame crux)
      (edgeKL edgeKM edgeKN edgeLM edgeLN edgeMN : Fin 6),
      (∀ atomIndex, basisSupportMultiplicity frame.tightDir frame.basisLabel
        atomIndex = 2) →
      shareSet frame.tightDir frame.basisLabel 0 1 = {edgeKL} →
      shareSet frame.tightDir frame.basisLabel 0 2 = {edgeKM} →
      shareSet frame.tightDir frame.basisLabel 0 3 = {edgeKN} →
      shareSet frame.tightDir frame.basisLabel 1 2 = {edgeLM} →
      shareSet frame.tightDir frame.basisLabel 1 3 = {edgeLN} →
      shareSet frame.tightDir frame.basisLabel 2 3 = {edgeMN} →
      datumTightSupport frame.tightDir (frame.basisLabel 0)
        = {edgeKL, edgeKM, edgeKN} →
      datumTightSupport frame.tightDir (frame.basisLabel 1)
        = {edgeKL, edgeLM, edgeLN} →
      datumTightSupport frame.tightDir (frame.basisLabel 2)
        = {edgeKM, edgeLM, edgeMN} →
      datumTightSupport frame.tightDir (frame.basisLabel 3)
        = {edgeKN, edgeLN, edgeMN} →
      False) :
    RankFourKFourClosed := by
  intro crux frame hmultTwo hcard hKFour
  obtain ⟨edgeKL, edgeKM, edgeKN, edgeLM, edgeLN, edgeMN, hsetKL, hsetKM,
    hsetKN, hsetLM, hsetLN, hsetMN, hsuppK, hsuppL, hsuppM, hsuppN⟩ :=
    kfour_atom_labeling frame.basisLabel hmultTwo hcard hKFour
  exact killLabeled crux frame edgeKL edgeKM edgeKN edgeLM edgeLN edgeMN
    hmultTwo hsetKL hsetKM hsetKN hsetLM hsetLN hsetMN hsuppK hsuppL
    hsuppM hsuppN

/-! ## The rung modulo the closures -/

/-- **THE RUNG MODULO THE CLOSURES.**  The five named closures imply the
rank-four rung: the frame extraction dispatches every rank-four crux
datum, branch one goes to closure one, branch two routes through the
private split with the landed all-private kill, and branch three routes
through the oriented dense closure. -/
theorem isSixThreeAssemblyRankExcluded_four_of_closures
    (hclosureOne : RankFourSupportTwoClosed)
    (hclosureTwo : RankFourSharedPrivateClosed)
    (hclosureKFour : RankFourKFourClosed)
    (hclosureIndependent : RankFourCycleIndependentClosed)
    (hclosureParallel : RankFourBothParallelClosed) :
    IsSixThreeAssemblyRankExcluded 4 := by
  intro crux activeIndex activeSet activeSubset activeWeight tightDir hdata
    hrankFour
  obtain ⟨frame, _htype, htrichotomy⟩ :=
    crux.exists_rankFourFrame hdata hrankFour
  rcases htrichotomy with ⟨columnIndex, htwo⟩ |
    ⟨hthree, pinAtom, privateSlot, hmultOne, hatomMem, hslotNe, hprivate,
      hpin⟩ | ⟨hthree, hmultTwo⟩
  · exact hclosureOne crux frame columnIndex htwo
  · exact frame.false_of_multOne_branch hclosureTwo hthree hmultOne hatomMem
      hslotNe hprivate hpin
  · exact frame.false_of_dense_branch hclosureKFour hclosureIndependent
      hclosureParallel hthree hmultTwo

end Gtz
