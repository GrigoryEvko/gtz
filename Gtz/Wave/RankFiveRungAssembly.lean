import Gtz.Wave.SupportQuintupleCensus
import Gtz.Wave.PrivateSupportSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The rank-five rung assembly — the rung modulo three named closures

The pinned dispatch splits every rank-five crux datum into three census
branches.  This file reifies the dispatch tuple as THE RANK-FIVE FRAME,
names the three remaining closure obligations as standalone propositions
over frames, discharges the fully private side inline, and assembles the
rung: the three closures imply `IsSixThreeAssemblyRankExcluded 5`.

The three named closures, with their branch of origin:

1. `RankFiveSupportTwoClosed` — census branch one: some basis support has
   cardinality two.
2. `RankFiveSharedPrivateClosed` — census branch two after the private
   split: the pinned slot's support carries a shared atom.  The fully
   private side is DEAD through the independence cap — at rank five it
   needs no trace budget, against the rank-four discharge that consumed
   the budget.
3. `RankFiveDenseClosed` — the dense branch: all supports have
   cardinality three, every atom sits in at least two supports, and the
   heavy atom sits in at least three.

Rank four needed FIVE closures, because its dense branch normalized into
the multigraph cycle shapes.  The rank-five dense branch carries twenty
one numeric representatives over three mass profiles, and the numeric
sweep (`r5sweep_report.md`) kills every one at first order plus at most
the ceiling, with fat floors.  The per-cell refinement stays inside the
one dense closure until the certificates name the sub-branches that
genuinely differ.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.RankFiveFrame` with `Gtz.SixThreeCrux.exists_rankFiveFrame` — **THE
  FRAME.**
* `Gtz.RankFiveFrame.hindep` — the derived independence of the basis.
* `Gtz.RankFiveSupportTwoClosed`, `Gtz.RankFiveSharedPrivateClosed`,
  `Gtz.RankFiveDenseClosed` — **THE THREE CLOSURES.**
* `Gtz.RankFiveFrame.false_of_multOne_branch` — the branch-two discharge
  with the inline fully-private kill.
* `Gtz.isSixThreeAssemblyRankExcluded_five_of_closures` — **THE RUNG
  MODULO THE CLOSURES.**

## Vacuity

The closures and the rung are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-! ## The rank-five frame -/

/-- **THE RANK-FIVE FRAME.**  The reified pinned-dispatch tuple: the
reduced datum, the five-label basis, the coefficient triple, and the
fourteen laws with the captured-trace disjunction.  Every branch kill
consumes a frame. -/
structure RankFiveFrame (crux : SixThreeCrux) where
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
  /-- The five-label basis. -/
  basisLabel : Fin 5 → activeIndex
  /-- The left inverse of the basis columns. -/
  leftInv : Matrix (Fin 5) (Fin 6) ℝ
  /-- The coefficient matrix of the projection. -/
  coeff : Matrix (Fin 5) (Fin 5) ℝ
  /-- The coefficient Gram core. -/
  gram : Matrix (Fin 5) (Fin 5) ℝ
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
  hker : ∀ coeffVec : Fin 5 → ℝ, gram *ᵥ coeffVec = 0 → coeffVec = 0
  /-- The exchange law. -/
  hexchange : coeff * gram = gram * coeffᵀ
  /-- The trace budget: the captured rank is two or three. -/
  htrace : Matrix.trace coeff = 2 ∨ Matrix.trace coeff = 3

/-- Every basis label of a frame is active. -/
theorem RankFiveFrame.hmemAll {crux : SixThreeCrux} (frame : RankFiveFrame crux)
    (columnIndex : Fin 5) : frame.basisLabel columnIndex ∈ frame.activeSet :=
  positiveActiveSet_subset_activeSet (frame.hmem columnIndex)

/-- The crux value is negative at every frame. -/
theorem RankFiveFrame.hvalueNeg {crux : SixThreeCrux}
    (_frame : RankFiveFrame crux) :
    chartObjective (chartPointOfDesign crux.design) < 0 :=
  crux.hasNegativeChartValue

/-- The basis directions of a frame are linearly independent: the left
inverse reads every coefficient. -/
theorem RankFiveFrame.hindep {crux : SixThreeCrux} (frame : RankFiveFrame crux) :
    LinearIndependent ℝ
      (fun columnIndex => frame.tightDir (frame.basisLabel columnIndex)) :=
  linearIndependent_tightDir_of_leftInverse frame.basisLabel frame.leftInv
    frame.hleft

/-- **THE FRAME EXTRACTION.**  Every rank-five crux datum yields a frame
together with the pinned census trichotomy over its basis. -/
theorem SixThreeCrux.exists_rankFiveFrame (crux : SixThreeCrux)
    {activeIndex : Type} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hrankFive : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 5) :
    ∃ frame : RankFiveFrame crux,
      frame.activeIndex = activeIndex
      ∧ ((∃ columnIndex, (datumTightSupport frame.tightDir
            (frame.basisLabel columnIndex)).card = 2)
        ∨ ((∀ columnIndex, (datumTightSupport frame.tightDir
              (frame.basisLabel columnIndex)).card = 3)
            ∧ ∃ (atomIndex : Fin 6) (privateSlot : Fin 5),
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
            ∧ (∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir
                frame.basisLabel atomIndex)
            ∧ ∃ atomIndex, 3 ≤ basisSupportMultiplicity frame.tightDir
                frame.basisLabel atomIndex)) := by
  obtain ⟨reducedWeight, basisLabel, leftInv, coeff, gram, hreducedData,
    _hassemblyEq, hinjective, hmem, hspan, hleft, hrepresentation,
    hidempotent, hHform, hsymmH, hpsd, hker, hexchange, htrace, htrichotomy⟩ :=
    crux.exists_rankFive_pinned_dispatch hdata hrankFive
  exact ⟨⟨activeIndex, activeSet, activeSubset, reducedWeight, tightDir,
    basisLabel, leftInv, coeff, gram, hreducedData, hinjective, hmem, hspan,
    hleft, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace⟩, rfl, htrichotomy⟩

/-! ## The three named closures -/

/-- **CLOSURE ONE.**  Census branch one: a basis support of cardinality
two dies at every frame. -/
def RankFiveSupportTwoClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux) (columnIndex : Fin 5),
    (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
    False

/-- **CLOSURE TWO.**  Census branch two with a shared atom: the pinned
slot's support carries an atom of multiplicity at least two, all supports
have cardinality three, and the frame dies. -/
def RankFiveSharedPrivateClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux)
    (privateSlot : Fin 5) (pinAtom sharedAtom : Fin 6),
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

/-- **CLOSURE THREE.**  The dense branch dies at every frame: all supports
have cardinality three, every atom sits in at least two supports, and the
heavy atom sits in at least three. -/
def RankFiveDenseClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankFiveFrame crux) (heavyAtom : Fin 6),
    (∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3) →
    (∀ atomIndex, 2 ≤ basisSupportMultiplicity frame.tightDir frame.basisLabel
      atomIndex) →
    3 ≤ basisSupportMultiplicity frame.tightDir frame.basisLabel heavyAtom →
    False

/-! ## The branch discharges -/

/-- **THE BRANCH-TWO DISCHARGE.**  At a frame with all supports of
cardinality three and a pinned multiplicity-one atom, the private split
routes: the fully private side dies through the independence cap, and the
shared side goes to closure two. -/
theorem RankFiveFrame.false_of_multOne_branch {crux : SixThreeCrux}
    (frame : RankFiveFrame crux)
    (hclosureTwo : RankFiveSharedPrivateClosed)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    {pinAtom : Fin 6} {privateSlot : Fin 5}
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
  · exact false_of_fully_private_quintuple frame.hindep
      (hthree privateSlot) hallPrivate
  · exact hclosureTwo crux frame privateSlot pinAtom sharedAtom hthree
      hmultOne hatomMem hslotNe hprivate hpin hsharedMem hsharedMult

/-! ## The rung modulo the closures -/

/-- **THE RUNG MODULO THE CLOSURES.**  The three named closures imply the
rank-five rung: the frame extraction dispatches every rank-five crux
datum, branch one goes to closure one, branch two routes through the
private split with the inline fully-private kill, and the dense branch
goes to closure three with its heavy atom. -/
theorem isSixThreeAssemblyRankExcluded_five_of_closures
    (hclosureOne : RankFiveSupportTwoClosed)
    (hclosureTwo : RankFiveSharedPrivateClosed)
    (hclosureDense : RankFiveDenseClosed) :
    IsSixThreeAssemblyRankExcluded 5 := by
  intro crux activeIndex activeSet activeSubset activeWeight tightDir hdata
    hrankFive
  obtain ⟨frame, _htype, htrichotomy⟩ :=
    crux.exists_rankFiveFrame hdata hrankFive
  rcases htrichotomy with ⟨columnIndex, htwo⟩ |
    ⟨hthree, pinAtom, privateSlot, hmultOne, hatomMem, hslotNe, hprivate,
      hpin⟩ | ⟨hthree, htwoLe, heavyAtom, hheavy⟩
  · exact hclosureOne crux frame columnIndex htwo
  · exact frame.false_of_multOne_branch hclosureTwo hthree hmultOne hatomMem
      hslotNe hprivate hpin
  · exact hclosureDense crux frame heavyAtom hthree htwoLe hheavy

end Gtz
