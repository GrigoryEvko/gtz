import Gtz

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The GTZ obligation registry

This module declares, as named `axiom`s, exactly the obligations on the stage-2
verifier's authoritative frontier.  Nothing else.

## Why axioms and not `sorry`

`sorry` collapses every open obligation into the single opaque constant
`sorryAx`, which records nothing about what is left.  A named axiom with a
closed statement makes `#print axioms` -- and the `#gtz_frontier` command in
`Skeleton.Frontier` -- print the exact remaining obligations, by name, computed
by the kernel.  That printed list is the anti-forgetting device.

## Why module root `Skeleton` and not `Gtz`

The repository's `Gtz/Audit.lean` ends with an environment sweep that fails the
build if any theorem whose module root is `Gtz` reaches an axiom outside
`{propext, Classical.choice, Quot.sound}`.  This scaffold must stay invisible to
that sweep, so it lives outside the repository under its own root and is
imported by nothing inside it.

## The frontier: four axioms, three independent obligations

Two roots are in play.

* Root A, rank three: `forall n, 0 < n -> Gtz.GtzOriginal n 3`.  Needs exactly
  one obligation, `obligationStressFreeHingeSixThree`.
* Root B, general rank: `forall rank, Gtz.GtzWeightedAll rank`, with no rank
  excluded because `Gtz.gtzWeighted_dim_zero` discharges rank zero.  Needs
  exactly three, `obligationSubThresholdBandHinge`,
  `obligationThresholdCellHinge` and `obligationSharpWindowAnchorReach`.

The merged count is THREE, not four: `stressFreeHingeSixThree_of_thresholdCellHinge`
below derives Root A's obligation from Root B's threshold-cell hinge, because
that hinge's own antecedent at rank three is `Gtz.GtzWeighted 5 3`, a theorem.
Root A's axiom is kept separately so the cheap rank-three capstone does not have
to assume the general-rank obligations.

## Standing prohibitions carried from the verifier

Do not add axioms for `NoMinimalCruxInSharpWindow`, the triangular ladder,
`ClosesCanonicalWindow` at any rank range, `forall k, Gtz.LiftingLemma k`, or
`WindowArrowFromPredecessorWeighted`: each is kernel-proved equivalent to the
root, so axiomatizing it axiomatizes the conjecture.  Do not axiomatize the
stress sign-split fan-out; it is a theorem.  Do not use
`Gtz.DirectionChartHasStrictTriple`; it is FALSE at a degenerate direction.
Do not add any of the six rank-three equivalent spellings alongside
`obligationStressFreeHingeSixThree`.
-/

namespace Skeleton

/--
STATUS: partial proof -- reduced to two chart obligations whose RIGIDITY halves are already unconditional theorems (`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`, `Gtz.parameterizedChartCovers_threeLinesDirection`); only the analytic half over an eleven-real chart is open. NOT VACUOUS: the stage-four audit constructed a stress-free (6,3) design (the six coordinate-plane diagonals at uniform weight one sixth, /tmp/gtz-chain/stage4/audit/audit5.lean), so this obligation genuinely quantifies over an inhabited stratum. It is also STRICTLY STRONGER than rank-three GTZ: the value holds at (5,3) while the hinge is refuted there.
CONSUMERS: the rank-three capstone in `Skeleton.RankThree`; ten in-tree consumers headed by `Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone`. Subsumed at rank three by `obligationThresholdCellHinge` via `Skeleton.stressFreeHingeSixThree_of_thresholdCellHinge`.
WHY OPEN: eight producers in the tree, ZERO of them unconditional. Every producer is either a restatement (residual families, uncovered residual, tight drop, corank-three alias -- all Iff-equal to this statement) or needs `Gtz.DirectionChartIsTieFree`, whose sole producer `Gtz.directionChartIsTieFree_of_hasStrictTriple` needs `Gtz.DirectionChartHasStrictTriple`, which has zero producers tree-wide.
ATTACK: take `Gtz.stressFreeHingeHoldsSixThree_of_kFourChart` (Gtz/Design/RigidityBridge.lean:1160), cost two, because its rigidity half is already discharged; what remains is positive-definiteness of `Gtz.directionChartGap` on the K4 chart plus tie-freeness of the four `Gtz.nonRigidResidualFamiliesSix` classes. Route through `Gtz.DirectionChartIsTieFree`, never through `Gtz.DirectionChartHasStrictTriple`, which drops the `PosSemidef` antecedent and is refutable.
NOT-REFUTED: no row of the stage-2 refutation census (533 refutation rows, 874 False-conclusion rows) targets it. The nearest refutations `Gtz.not_hingeHoldsAtSize_five_three` and `Gtz.not_hingeHoldsAtSize_four_three` are at sizes five and four, strictly below six. The refuted `0 <= weight` relaxation `Gtz.not_relaxedStressFreeHinge_of_fiveThree_tie` cannot touch this statement: `Gtz.WeightedDesign` carries `weight_pos : forall label, 0 < weight label`, STRICT.
-/
axiom obligationStressFreeHingeSixThree : Gtz.StressFreeHingeHoldsSixThree

/--
STATUS: no evidence. The band holds `rank * (rank - 3) / 2` cells and is EMPTY at rank three, so no rank-three theorem in the tree is evidence about it. The only unconditional `Gtz.HingeHoldsAtSize` instance anywhere is the vacuous `(2,2)`.
CONSUMERS: the general-rank capstone in `Skeleton.GeneralRank`, through the sharp-window hinge that pairs it with `obligationThresholdCellHinge`.
WHY OPEN: no producer at any rank. Below the threshold cell a design has fewer than `dim Sym(rank)` atoms, so the atom matrices need not span, the dual-conic instrument and the normalizer-form uniqueness used at rank three both lose their precondition, and no stress is forced.
ATTACK: the first live cell is rank four, size eight, i.e. `Gtz.GtzWeighted 8 4`, for which the tree already has the downward edge `Gtz.gtzWeighted_six_three_of_eight_four`. Climb from the Naimark floor `Gtz.UniformPositionBridge.gtzWeighted_belowWindow_of_predecessor`, which supplies size `2 * rank - 1` at every rank, one cell at a time; the closest in-tree precedent for the transfer instrument is `Gtz.CorankTwo.exists_tieLockedNaimarkDual` together with `Gtz.CorankTwo.sharedCircuitPairAtCorankTwoTie_holds`.
NOT-REFUTED: both hinge refutations sit at sizes four and five, strictly below this band's lower bound `2 * rank`, and the band is empty at rank three, so neither is an instance. No refutation row in the census targets any cell with `2 * rank <= size < rank * (rank + 1) / 2`.
-/
axiom obligationSubThresholdBandHinge :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        Gtz.GtzWeighted (size - 1) rank →
          ∀ design : Gtz.WeightedDesign size rank,
            Gtz.IsTie design → Gtz.HasParallelPair design

/--
STATUS: partial proof. At rank three this IS `Gtz.HingeHoldsAtSize 6 3`, whose STRESSED arm is already a theorem (`Gtz.sixThree_stress_trichotomy` with branches (ii) and (iii) discharged by `Gtz.balancedStratumSelection_six_holds` and `Gtz.twoPoleStratumSelection_six_unconditional`) and whose STRESS-FREE arm is exactly `obligationStressFreeHingeSixThree`. At rank four and above both arms are open.
CONSUMERS: the general-rank capstone in `Skeleton.GeneralRank`; and it SUBSUMES `obligationStressFreeHingeSixThree`, kernel-checked by `Skeleton.stressFreeHingeSixThree_of_thresholdCellHinge`.
WHY OPEN: the threshold cell carries exactly `dim Sym(rank)` atoms, so stress-freeness there means the atom matrices form a BASIS -- the rank-three situation, rank-generically. What breaks above rank three is the stressed arm: the admissible sign-split interval `[rank, rank * (rank + 1) / 2 - rank]` is a singleton ONLY at rank three, so the branch analysis fans out, and both discharged rank-three capstones hard-code rank three in their types (`Gtz.BalancedStratumSelection` quantifies card-three triples, `Gtz.TwoPoleStratumSelection` uses `probe : Fin 3 -> Real`).
ATTACK: split on stress-freeness, which is a tautology, then attack the two arms separately. The stressed arm needs `Gtz.BalancedStratumSelection` and `Gtz.TwoPoleStratumSelection` re-authored at general rank; the bound they would rest on, `Gtz.design_rank_le_card_sides`, is ALREADY rank-uniform. The stress-free arm is the rank-three frontier lifted along the threshold axis; note that reading the rank-three coincidence along `rank + 3` instead leaves the window at rank four and loses spanning, so `rank * (rank + 1) / 2` is the correct carrier.
NOT-REFUTED: nothing in the census refutes it. `Gtz.not_hingeHoldsAtSize_five_three` is at size five, below the rank-three threshold cell six, and below `2 * rank` at every rank, so it is not an instance at any rank.
-/
axiom obligationThresholdCellHinge :
    ∀ rank : ℕ, 3 ≤ rank →
      Gtz.GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : Gtz.WeightedDesign (rank * (rank + 1) / 2) rank,
          Gtz.IsTie design → Gtz.HasParallelPair design

/--
STATUS: partial proof, and a THEOREM at rank three. At rank three the sharp window is the single cell size six, discharged by `Gtz.icosaDesign` with `Gtz.icosaDesign_hasStrictlyDominatingSubset` and `Gtz.parallelFreeReachesAnchor_six_three`. The anchor's STRICT half is free at every rank by positive rescaling, `Gtz.UniformPositionBridge.exists_strictAnchor_of_weakDominator`.
CONSUMERS: the general-rank capstone in `Skeleton.GeneralRank`, feeding every rung of `Gtz.UniformPositionBridge.gtzWeighted_succ_of_hinge_of_reach`.
WHY OPEN: the only `Gtz.ParallelFreeReachesAnchor` instance in the entire tree is the rank-three one. Above rank three what is missing is per-cell connectivity of the parallel-free locus, plus an assembly step that nothing in the tree performs: `Gtz.UniformPositionBridge.DiagonalTailAtCell` has ZERO producers AND ZERO consumers, so even proving it would leave it unwired.
ATTACK: `Gtz.UniformPositionBridge.windowAnchorReachFree_of_weakWitness` plus `exists_strictAnchor_of_weakDominator` already reduce this to a weak parallel-free dominator at each cell together with per-cell connectivity. Two concrete gaps remain: wire `DiagonalTailAtCell` and `Gtz.UniformPositionBridge.coreTailBookkeeping_feasible` into that weak witness (the Fin reindexing and the Parseval sum are unwritten), and close the tail-block diagonality matrix identity that Gtz/Uniform/AnchorAssembly.lean:269-283 self-declares unproved, whose content `sum_tailRawWeight_mul_tailCoeff` is already a theorem.
NOT-REFUTED: `Gtz.UniformPositionBridge.not_windowAnchorReachFree_two` and `Gtz.not_parallelFreeReachesAnchor_rankTwo` refute reach at RANK TWO, but they are not instances of this statement: the sharp window is empty at rank two, since `2 * 2 = 4` exceeds `2 * (2 + 1) / 2 = 3`. The stage-2 lane confirmed the rank-two obstruction dissolves under the sharpening. The guard `3 <= rank` is therefore what keeps this statement clear of the only known refutation.
-/
axiom obligationSharpWindowAnchorReach :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        ∃ anchor : Gtz.WeightedDesign size rank,
          Gtz.HasStrictlyDominatingSubset anchor
            ∧ Gtz.ParallelFreeReachesAnchor size rank anchor

/-!
## The subsumption, as a kernel fact rather than a docstring claim

`obligationThresholdCellHinge` at rank three needs `Gtz.GtzWeighted 5 3`, which
is the theorem `Gtz.gtzWeighted_of_le_five`, and its conclusion then covers the
stress-free arm by simply ignoring the stress-freeness hypothesis.  So the
general-rank registry already contains the rank-three obligation.  This is why
the honest frontier count is three, not four.
-/

/-- The general-rank threshold-cell hinge yields the rank-three obligation
outright, so `obligationStressFreeHingeSixThree` is redundant for anyone who has
already assumed `obligationThresholdCellHinge`. -/
theorem stressFreeHingeSixThree_of_thresholdCellHinge
    (thresholdHinge :
      ∀ rank : ℕ, 3 ≤ rank →
        Gtz.GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
          ∀ design : Gtz.WeightedDesign (rank * (rank + 1) / 2) rank,
            Gtz.IsTie design → Gtz.HasParallelPair design) :
    Gtz.StressFreeHingeHoldsSixThree := by
  have hfive : Gtz.GtzWeighted (3 * (3 + 1) / 2 - 1) 3 :=
    Gtz.gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)
  exact fun design _isStressFree hTie => thresholdHinge 3 (by norm_num) hfive design hTie

/-!
## Machine-readable index

`liveObligationNames` lets tooling enumerate the registry without parsing this
source.  `Skeleton.Frontier` cross-checks it against an environment scan of
every axiom declared in this namespace, so it cannot silently drift.
-/

/-- Every obligation axiom declared in this module, in declaration order.
Kept honest by `#gtz_registry_check` in `Skeleton.Frontier`. -/
def liveObligationNames : List Lean.Name :=
  [`Skeleton.obligationStressFreeHingeSixThree,
   `Skeleton.obligationSubThresholdBandHinge,
   `Skeleton.obligationThresholdCellHinge,
   `Skeleton.obligationSharpWindowAnchorReach]

end Skeleton
