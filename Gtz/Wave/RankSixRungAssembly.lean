import Gtz.Wave.SupportSextupleCensus
import Gtz.Wave.PrivateSupportSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The rank-six rung assembly — the rung modulo three named closures

The pinned dispatch splits every rank-six crux datum into three census
branches.  This file reifies the dispatch tuple as THE RANK-SIX FRAME,
names the three remaining closure obligations as standalone propositions
over frames, discharges the fully private side inline, and assembles the
rung: the three closures imply `IsSixThreeAssemblyRankExcluded 6`.

The three named closures, with their branch of origin:

1. `RankSixSupportTwoClosed` — census branch one: some basis support has
   cardinality two.
2. `RankSixSharedPrivateClosed` — census branch two after the private
   split: the pinned slot's support carries a shared atom.  The fully
   private side is DEAD through the independence cap, exactly as at rank
   five.
3. `RankSixDenseClosed` — the dense branch: all supports have cardinality
   three, every atom sits in at least two supports, and the heavy atom
   sits in at least three.

The three closure Props repeat the rank-five SHAPES at `Fin 6`: the
support-two closure narrows to the same outer-sharer residual (the
closure supply lands the bridge), and the shared-private closure carries
the same pin package.  One certificate argument at the generic datum
level thus discharges the matching closures of all three rungs through
the parallel bridges.  The frame is STRONGER than the lower frames in two
laws: the basis matrix carries a two-sided inverse (`hright`), and the
trace is pinned at three with no disjunction.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.RankSixFrame` with `Gtz.SixThreeCrux.exists_rankSixFrame` — **THE
  FRAME.**
* `Gtz.RankSixFrame.hindep` — the derived independence of the basis.
* `Gtz.RankSixSupportTwoClosed`, `Gtz.RankSixSharedPrivateClosed`,
  `Gtz.RankSixDenseClosed` — **THE THREE CLOSURES.**
* `Gtz.RankSixFrame.false_of_multOne_branch` — the branch-two discharge
  with the inline fully-private kill.
* `Gtz.isSixThreeAssemblyRankExcluded_six_of_closures` — **THE RUNG
  MODULO THE CLOSURES.**

## Vacuity

The closures and the rung are vacuous if `Gtz.GtzWeighted 6 3` holds: no
crux exists, thus no frame exists.
-/

namespace Gtz

open Matrix

/-! ## The rank-six frame -/

/-- **THE RANK-SIX FRAME.**  The reified pinned-dispatch tuple: the
reduced datum, the six-label basis, the coefficient triple, and the
fifteen laws with the two-sided inverse and the exact trace.  Every
branch kill consumes a frame. -/
structure RankSixFrame (crux : SixThreeCrux) where
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
  /-- The six-label basis. -/
  basisLabel : Fin 6 → activeIndex
  /-- The two-sided inverse of the basis columns. -/
  leftInv : Matrix (Fin 6) (Fin 6) ℝ
  /-- The coefficient matrix of the projection. -/
  coeff : Matrix (Fin 6) (Fin 6) ℝ
  /-- The coefficient Gram core. -/
  gram : Matrix (Fin 6) (Fin 6) ℝ
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
  /-- The right inverse law: at rank six the basis matrix is square and the
  inverse is two-sided. -/
  hright : tightBasisColumns tightDir basisLabel * leftInv = 1
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
  hker : ∀ coeffVec : Fin 6 → ℝ, gram *ᵥ coeffVec = 0 → coeffVec = 0
  /-- The exchange law. -/
  hexchange : coeff * gram = gram * coeffᵀ
  /-- The trace law: the captured rank is three exactly. -/
  htrace : Matrix.trace coeff = 3

/-- Every basis label of a frame is active. -/
theorem RankSixFrame.hmemAll {crux : SixThreeCrux} (frame : RankSixFrame crux)
    (columnIndex : Fin 6) : frame.basisLabel columnIndex ∈ frame.activeSet :=
  positiveActiveSet_subset_activeSet (frame.hmem columnIndex)

/-- The crux value is negative at every frame. -/
theorem RankSixFrame.hvalueNeg {crux : SixThreeCrux}
    (_frame : RankSixFrame crux) :
    chartObjective (chartPointOfDesign crux.design) < 0 :=
  crux.hasNegativeChartValue

/-- The basis directions of a frame are linearly independent: the left
inverse reads every coefficient. -/
theorem RankSixFrame.hindep {crux : SixThreeCrux} (frame : RankSixFrame crux) :
    LinearIndependent ℝ
      (fun columnIndex => frame.tightDir (frame.basisLabel columnIndex)) :=
  linearIndependent_tightDir_of_leftInverse frame.basisLabel frame.leftInv
    frame.hleft

/-- **THE FRAME EXTRACTION.**  Every rank-six crux datum yields a frame
together with the pinned census trichotomy over its basis. -/
theorem SixThreeCrux.exists_rankSixFrame (crux : SixThreeCrux)
    {activeIndex : Type} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)}
    {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (hrankSix : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly activeSet activeWeight tightDir))) = 6) :
    ∃ frame : RankSixFrame crux,
      frame.activeIndex = activeIndex
      ∧ ((∃ columnIndex, (datumTightSupport frame.tightDir
            (frame.basisLabel columnIndex)).card = 2)
        ∨ ((∀ columnIndex, (datumTightSupport frame.tightDir
              (frame.basisLabel columnIndex)).card = 3)
            ∧ ∃ (atomIndex : Fin 6) (privateSlot : Fin 6),
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
    _hassemblyEq, hinjective, hmem, hspan, hleft, hright, hrepresentation,
    hidempotent, hHform, hsymmH, hpsd, hker, hexchange, htrace, htrichotomy⟩ :=
    crux.exists_rankSix_pinned_dispatch hdata hrankSix
  exact ⟨⟨activeIndex, activeSet, activeSubset, reducedWeight, tightDir,
    basisLabel, leftInv, coeff, gram, hreducedData, hinjective, hmem, hspan,
    hleft, hright, hrepresentation, hidempotent, hHform, hsymmH, hpsd, hker,
    hexchange, htrace⟩, rfl, htrichotomy⟩

/-! ## The three named closures -/

/-- **CLOSURE ONE.**  Census branch one: a basis support of cardinality
two dies at every frame. -/
def RankSixSupportTwoClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux) (columnIndex : Fin 6),
    (datumTightSupport frame.tightDir (frame.basisLabel columnIndex)).card = 2 →
    False

/-- **CLOSURE TWO.**  Census branch two with a shared atom: the pinned
slot's support carries an atom of multiplicity at least two, all supports
have cardinality three, and the frame dies. -/
def RankSixSharedPrivateClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux)
    (privateSlot : Fin 6) (pinAtom sharedAtom : Fin 6),
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
def RankSixDenseClosed : Prop :=
  ∀ (crux : SixThreeCrux) (frame : RankSixFrame crux) (heavyAtom : Fin 6),
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
theorem RankSixFrame.false_of_multOne_branch {crux : SixThreeCrux}
    (frame : RankSixFrame crux)
    (hclosureTwo : RankSixSharedPrivateClosed)
    (hthree : ∀ columnIndex, (datumTightSupport frame.tightDir
      (frame.basisLabel columnIndex)).card = 3)
    {pinAtom : Fin 6} {privateSlot : Fin 6}
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
  · exact false_of_fully_private_sextuple frame.hindep
      (hthree privateSlot) hallPrivate
  · exact hclosureTwo crux frame privateSlot pinAtom sharedAtom hthree
      hmultOne hatomMem hslotNe hprivate hpin hsharedMem hsharedMult

/-! ## The rung modulo the closures -/

/-- **THE RUNG MODULO THE CLOSURES.**  The three named closures imply the
rank-six rung: the frame extraction dispatches every rank-six crux datum,
branch one goes to closure one, branch two routes through the private
split with the inline fully-private kill, and the dense branch goes to
closure three with its heavy atom. -/
theorem isSixThreeAssemblyRankExcluded_six_of_closures
    (hclosureOne : RankSixSupportTwoClosed)
    (hclosureTwo : RankSixSharedPrivateClosed)
    (hclosureDense : RankSixDenseClosed) :
    IsSixThreeAssemblyRankExcluded 6 := by
  intro crux activeIndex activeSet activeSubset activeWeight tightDir hdata
    hrankSix
  obtain ⟨frame, _htype, htrichotomy⟩ :=
    crux.exists_rankSixFrame hdata hrankSix
  rcases htrichotomy with ⟨columnIndex, htwo⟩ |
    ⟨hthree, pinAtom, privateSlot, hmultOne, hatomMem, hslotNe, hprivate,
      hpin⟩ | ⟨hthree, htwoLe, heavyAtom, hheavy⟩
  · exact hclosureOne crux frame columnIndex htwo
  · exact frame.false_of_multOne_branch hclosureTwo hthree hmultOne hatomMem
      hslotNe hprivate hpin
  · exact hclosureDense crux frame heavyAtom hthree htwoLe hheavy

end Gtz
