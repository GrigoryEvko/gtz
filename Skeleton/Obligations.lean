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

## The frontier after the five-class split

Two roots are in play.

* Root A, rank three: `forall n, 0 < n -> Gtz.GtzOriginal n 3`.  Rests on FIVE
  class obligations, one per surviving matroid class of the stress-free (6,3)
  stratum: `obligationTieFreeUThreeSix`, `obligationTieFreeOneLine`,
  `obligationTieFreeTwoMeetingLines`, `obligationTieFreeThreeLines`,
  `obligationTieFreeKFour`.  Their conjunction is EXACTLY the original single
  obligation `obligationStressFreeHingeSixThree`, which survives below as a
  theorem assembled from the five, so the split is lossless and every class
  discharge shrinks the frontier monotonically.
* Root B, general rank: `forall rank, Gtz.GtzWeightedAll rank`, with no rank
  excluded because `Gtz.gtzWeighted_dim_zero` discharges rank zero.  Needs
  exactly three, `obligationSubThresholdBandHinge`,
  `obligationThresholdCellHinge` and
  `obligationSharpWindowAnchorReachRankFourAndUp` -- the reach obligation's
  rank-three half is DISCHARGED (`Gtz.icosaDesign`), and the original name
  `obligationSharpWindowAnchorReach` survives as a theorem assembled from the
  two halves.

The merged mathematical count is still THREE:
`stressFreeHingeSixThree_of_thresholdCellHinge` below derives the whole
rank-three side from Root B's threshold-cell hinge, because that hinge's own
antecedent at rank three is `Gtz.GtzWeighted 5 3`, a theorem.  The class axioms
are kept separately so the cheap rank-three capstone does not have to assume
the general-rank obligations, and so each class closes independently.

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

/-!
### SPLIT RECORD: `obligationStressFreeHingeSixThree`, split into the five matroid classes

Retired as an axiom and re-proved below as a theorem assembled from the five
class obligations.  The split is LOSSLESS: the hinge implies every class
statement at every pattern, because its tie-emptiness reading
(`Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie`) carries no pattern
hypothesis at all -- so each class axiom is strictly weaker than the parent and
their conjunction is exactly it.  The five classes are the entries of
`Gtz.stressFreeResidualFamiliesSix`, the survivors of the plane-pair escape law
(Gtz/Design/StressFreeMatroidStratification.lean:303 proves the residual list is
EXACTLY the not-plane-pair-covered list).

Original five fields, kept as provenance; the live fields are on the class
axioms below.

STATUS: partial proof -- reduced to two chart obligations whose RIGIDITY halves are already unconditional theorems (`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`, `Gtz.parameterizedChartCovers_threeLinesDirection`); only the analytic half over an eleven-real chart is open. NOT VACUOUS: the stage-four audit constructed a stress-free (6,3) design (the six coordinate-plane diagonals at uniform weight one sixth, /tmp/gtz-chain/stage4/audit/audit5.lean), so this obligation genuinely quantifies over an inhabited stratum. It is also STRICTLY STRONGER than rank-three GTZ: the value holds at (5,3) while the hinge is refuted there.
CONSUMERS: the rank-three capstone in `Skeleton.RankThree`; ten in-tree consumers headed by `Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone`. Subsumed at rank three by `obligationThresholdCellHinge` via `Skeleton.stressFreeHingeSixThree_of_thresholdCellHinge`.
WHY OPEN: eight producers in the tree, ZERO of them unconditional. Every producer is either a restatement (residual families, uncovered residual, tight drop, corank-three alias -- all Iff-equal to this statement) or needs `Gtz.DirectionChartIsTieFree`, whose sole producer `Gtz.directionChartIsTieFree_of_hasStrictTriple` needs `Gtz.DirectionChartHasStrictTriple`, which has zero producers tree-wide.
ATTACK: take `Gtz.stressFreeHingeHoldsSixThree_of_kFourChart` (Gtz/Design/RigidityBridge.lean:1160), cost two, because its rigidity half is already discharged; what remains is positive-definiteness of `Gtz.directionChartGap` on the K4 chart plus tie-freeness of the four `Gtz.nonRigidResidualFamiliesSix` classes. Route through `Gtz.DirectionChartIsTieFree`, never through `Gtz.DirectionChartHasStrictTriple`, which drops the `PosSemidef` antecedent and is refutable.
NOT-REFUTED: no row of the stage-2 refutation census (533 refutation rows, 874 False-conclusion rows) targets it. The nearest refutations `Gtz.not_hingeHoldsAtSize_five_three` and `Gtz.not_hingeHoldsAtSize_four_three` are at sizes five and four, strictly below six. The refuted `0 <= weight` relaxation `Gtz.not_relaxedStressFreeHinge_of_fiveThree_tie` cannot touch this statement: `Gtz.WeightedDesign` carries `weight_pos : forall label, 0 < weight label`, STRICT.
-/

/--
STATUS: open, no producer. The single MIXED class: on the line-free stratum a stress has full support, and full support means the six directions lie on a conic (`Gtz.stratumStressHasFullSupport_lineFree`, Gtz/Reduction/TrichotomyLedger.lean:524), so stress-free here means OFF-CONIC. Uniquely among the five classes the stress-freeness hypothesis excludes a genuine sublocus, and that sublocus is exactly where the margin degenerates. This is where the (4,3) tetrahedron and (5,3) diamond tie shadows live.
CONSUMERS: `obligationStressFreeHingeSixThree` (the split parent, now a theorem), hence the rank-three capstone.
WHY OPEN: on a line-free stratum every distinct triple is a basis, so no pruning rule bites, and the deflation rule is provably inert (`Gtz.not_blindLabel_lineFree`, Gtz/Design/StratumTieFreeClasses.lean). The tree records that attacking this class FIRST is backwards (StratumTieFreeClasses.lean:207-215); it is sequenced LAST, after the four rigid classes.
ATTACK: start from the conic characterization, never from a selector. Orbit-split by the weakly dominating triple via `Gtz.relabelDesign`; per representative a TWO-FAMILY argument -- interior certificate plus boundary compactification onto the proved (5,3) exclusions (`EndpointSpike.endpointBottomTieExclusionFiveThree_holds`, `Gtz.twoVanishedRigidBottomDomination_holds`). Candidate non-vacuity anchor: `Gtz.icosaDesign` (parallel-free, has a strictly dominating triple, hence itself no tie); its line-freeness is not yet a kernel fact.
NOT-REFUTED: no census row targets the class statement. What IS refuted are methods: every finite pure-triple or orbit selector, every constant, label-free or continuous selector, matroid exchange, bounded-radius search, weight-uniform threshold certificates (margin infimum zero), and Putinar/Schmuedgen. A stress-forcing pattern filter cannot apply here: it would assert every line-free design lies on a conic.
-/
axiom obligationTieFreeUThreeSix :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [])

/--
STATUS: open, no producer, no chart. The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_oneThreePointLine`, Gtz/Reduction/TrichotomyLedger.lean:485), so the stress-freeness hypothesis is automatic and this obligation reads exactly: no (6,3) design realizing one three-point line is an exact tie.
CONSUMERS: `obligationStressFreeHingeSixThree` (the split parent, now a theorem), hence the rank-three capstone.
WHY OPEN: of the six producers of `Gtz.StressFreeStratumIsTieFree` in the tree, three are chart instances at other patterns, the plane-pair filter is provably anti-aligned (the residual list IS the not-plane-pair-covered list, Gtz/Design/StressFreeMatroidStratification.lean:303), and the two generic chart forms need a chart nobody has built for this pattern.
ATTACK: build the chart following the shipped precedent -- Gtz/Design/RigidityBridge.lean:1-60 (PGL(3) simply transitive on four general lines, made rational, plus the per-atom scaling group) and the structure of `Gtz.directionChartCoversPrimitiveStratum_kFourDirection`. The pattern pins only three atoms projectively, so the chart carries genuine moduli and the analytic half is a parametric family. Pen-work triage of /tmp/gtz-p38/rigidity2 pending.
NOT-REFUTED: no census row targets it. No stress-forcing pattern filter can ever apply: the pattern forces stress-freeNESS (TrichotomyLedger.lean:485), the opposite polarity, so the plane-pair mechanism has nothing left to kill here.
-/
axiom obligationTieFreeOneLine :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [[0, 1, 2]])

/--
STATUS: open, no producer, no chart. The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_twoMeetingLines`, Gtz/Reduction/TrichotomyLedger.lean:491), so this obligation reads exactly: no (6,3) design realizing two meeting three-point lines is an exact tie.
CONSUMERS: `obligationStressFreeHingeSixThree` (the split parent, now a theorem), hence the rank-three capstone.
WHY OPEN: same producer situation as the one-line class -- no chart exists for this pattern and the plane-pair filter is structurally inapplicable. Two concurrent lines are the closest residual pattern to the plane-pair boundary: the two line planes cover five of the six atoms, and it is exactly the sixth that escapes the escape law.
ATTACK: same chart-building precedent as the one-line class (RigidityBridge.lean:1-60 plus the :796 covering structure); the pattern pins five atoms up to the two line moduli, so the chart is SMALLER than the one-line chart -- build this one first of the two. Pen-work triage of /tmp/gtz-p38/rigidity2 pending.
NOT-REFUTED: no census row targets it. No stress-forcing pattern filter can apply (TrichotomyLedger.lean:491, opposite polarity).
-/
axiom obligationTieFreeTwoMeetingLines :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4]])

/--
STATUS: chart-covered, analytic half open. The covering half is the unconditional `Gtz.parameterizedChartCovers_threeLinesDirection` (Gtz/Design/RigidityBridge.lean:1098) with consumer `Gtz.stressFreeStratumIsTieFree_threeLines_of_chart` (:1135); the stratum is uniformly stress-free (`Gtz.stratumIsStressFree_threeLines`, Gtz/Reduction/TrichotomyLedger.lean:497). What is open is `Gtz.DirectionChartIsTieFree (Gtz.threeLinesDirection slide)` at every admissible slide (`Gtz.IsAdmissibleThreeLinesParameter`: slide != 0 and slide != -1, RigidityBridge.lean:883) -- twelve numbers, one more than the K4 chart.
CONSUMERS: `obligationStressFreeHingeSixThree` (the split parent, now a theorem), hence the rank-three capstone.
WHY OPEN: the sole producer of `Gtz.DirectionChartIsTieFree` routes through `Gtz.DirectionChartHasStrictTriple`, which is FALSE at a degenerate direction; no direct certificate exists at any slide.
ATTACK: inherit whatever certificate format closes the K4 chart, PARAMETRICALLY in the slide from the start; partition the admissible line into finitely many intervals with exact algebraic endpoints. The two excluded slides are the degenerations onto a collapsed atom (a parallel pair, outside every stress-free stratum) or the M(K4) pattern (the K4 class); they are not gaps.
NOT-REFUTED: no census row targets it. The strict-triple refutation kills only that producer's premise at a degenerate direction, not this statement. No stress-forcing filter can apply (TrichotomyLedger.lean:497).
-/
axiom obligationTieFreeThreeLines :
    Gtz.StressFreeStratumIsTieFree
      (Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4], [1, 3, 5]])

/--
STATUS: the most rigid class; covering half PROVED (`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`, Gtz/Design/RigidityBridge.lean:796), direct class consumer `Gtz.stressFreeStratumIsTieFree_graphicKFour_of_chart` (:834). The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_graphicKFour`, Gtz/Reduction/TrichotomyLedger.lean:505). NOT VACUOUS: the stage-four audit's coordinate-diagonal design (the regular tetrahedron's six edge directions) realizes exactly this pattern. Open: `Gtz.DirectionChartIsTieFree Gtz.kFourDirection` -- eleven positive reals against six FIXED rational chart vectors, twenty triples, no design, no whitener, no square root in the statement.
CONSUMERS: `obligationStressFreeHingeSixThree` (the split parent, now a theorem), hence the rank-three capstone.
WHY OPEN: the sole producer of `Gtz.DirectionChartIsTieFree` is `Gtz.directionChartIsTieFree_of_hasStrictTriple` (:176), whose premise `Gtz.DirectionChartHasStrictTriple` is kernel-FALSE at a degenerate chart point; the weak-domination antecedent must stay in every lemma. The class-level sibling `stressFreeStratumIsTieFree_graphicKFour_of_strictTriple` (:841) is forbidden for the same reason.
ATTACK: DECIDED (spike, 2026-08-07): the DIRECT road. The collar weld was sized in a typed probe and needs THREE layers that do not exist (a record-to-gap-minor dictionary, coverage of the eleven-dimensional chart domain by the checker's five-integer evaluation points -- the 299-quadruple banding is commit-attested only and the generating pickle is gone -- and a record-inequality-to-PosDef strictness transfer); each alone exceeds the direct road. First brick LANDED: `Gtz.tetrahedronChartPoint` (Gtz/Design/KFourChartSample.lean) is the tetrahedron witness's FULLY RATIONAL chart image (mass 1/4, weight 1/6 -- the gauge absorbs sqrt(3/2)), and `Gtz.tetrahedron_gap_posDef` proves the coordinate-axis triple `{3,4,5}` strictly dominating there, margin 1/2, by `norm_num`/`nlinarith` on a 3x3 rational matrix. Next: the weak-implies-strict argument at a GENERAL chart point -- expand the three Sylvester minors of `Gtz.directionChartGap` (:128) into polynomials in the eleven chart coordinates and either perturb a PSD-but-singular triple to a strict neighbor or certify KillCellCertificate-style over a cell decomposition.
NOT-REFUTED: no census row targets it. The relaxed-weight refutation needs `0 <= weight`; chart points carry strict positivity. No stress-forcing filter can apply (TrichotomyLedger.lean:505 plus the tetrahedron inhabitant).
-/
axiom obligationTieFreeKFour :
    Gtz.StressFreeStratumIsTieFree
      (Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]])

/-- **Split, not weakened.**  Same name, same statement as the axiom it
replaces, assembled from the five class obligations through the tree's own
`Gtz.stressFreeHingeHoldsSixThree_of_residualFamilies`, with the enumeration
premise discharged by `Gtz.linearSpaceListIsComplete_six`.  Every downstream
capstone compiles untouched. -/
theorem obligationStressFreeHingeSixThree : Gtz.StressFreeHingeHoldsSixThree :=
  Gtz.stressFreeHingeHoldsSixThree_of_residualFamilies Gtz.linearSpaceListIsComplete_six
    (by
      intro lines hlines
      simp only [Gtz.stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil,
        or_false] at hlines
      rcases hlines with rfl | rfl | rfl | rfl | rfl
      · exact obligationTieFreeUThreeSix
      · exact obligationTieFreeOneLine
      · exact obligationTieFreeTwoMeetingLines
      · exact obligationTieFreeThreeLines
      · exact obligationTieFreeKFour)

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

/-!
### SPLIT RECORD: `obligationSharpWindowAnchorReach`, split by rank

Retired as an axiom and re-proved below from `...RankThree` and
`...RankFourAndUp`.  Its original five fields are kept verbatim here because
they are the provenance of the two finer statements; the live fields are on
those.

STATUS: partial proof, and a THEOREM at rank three. At rank three the sharp window is the single cell size six, discharged by `Gtz.icosaDesign` with `Gtz.icosaDesign_hasStrictlyDominatingSubset` and `Gtz.parallelFreeReachesAnchor_six_three`. The anchor's STRICT half is free at every rank by positive rescaling, `Gtz.UniformPositionBridge.exists_strictAnchor_of_weakDominator`.
CONSUMERS: the general-rank capstone in `Skeleton.GeneralRank`, feeding every rung of `Gtz.UniformPositionBridge.gtzWeighted_succ_of_hinge_of_reach`.
WHY OPEN: the only `Gtz.ParallelFreeReachesAnchor` instance in the entire tree is the rank-three one. Above rank three what is missing is per-cell connectivity of the parallel-free locus, plus an assembly step that nothing in the tree performs: `Gtz.UniformPositionBridge.DiagonalTailAtCell` has ZERO producers AND ZERO consumers, so even proving it would leave it unwired.
ATTACK: `Gtz.UniformPositionBridge.windowAnchorReachFree_of_weakWitness` plus `exists_strictAnchor_of_weakDominator` already reduce this to a weak parallel-free dominator at each cell together with per-cell connectivity. Two concrete gaps remain: wire `DiagonalTailAtCell` and `Gtz.UniformPositionBridge.coreTailBookkeeping_feasible` into that weak witness (the Fin reindexing and the Parseval sum are unwritten), and close the tail-block diagonality matrix identity that Gtz/Uniform/AnchorAssembly.lean:269-283 self-declares unproved, whose content `sum_tailRawWeight_mul_tailCoeff` is already a theorem.
NOT-REFUTED: `Gtz.UniformPositionBridge.not_windowAnchorReachFree_two` and `Gtz.not_parallelFreeReachesAnchor_rankTwo` refute reach at RANK TWO, but they are not instances of this statement: the sharp window is empty at rank two, since `2 * 2 = 4` exceeds `2 * (2 + 1) / 2 = 3`. The stage-2 lane confirmed the rank-two obstruction dissolves under the sharpening. The guard `3 <= rank` is therefore what keeps this statement clear of the only known refutation.
-/

/--
STATUS: partial proof. The sharp window at rank three is the single cell size six.
CONSUMERS: `obligationSharpWindowAnchorReach`, which survives as a theorem so no capstone changed.
WHY OPEN: split off from `obligationSharpWindowAnchorReach` so the rank-three half can be discharged separately.
ATTACK: `Gtz.icosaDesign` with `Gtz.icosaDesign_hasStrictlyDominatingSubset` and `Gtz.parallelFreeReachesAnchor_six_three`, exactly as `skeletonSharpWindowAnchorReachAtRankThree` already does in `Skeleton.RankThree`.
NOT-REFUTED: the rank-two refutations are not instances; the sharp window is empty at rank two.
-/
theorem obligationSharpWindowAnchorReachRankThree :
    ∀ size : ℕ, 2 * 3 ≤ size → size ≤ 3 * (3 + 1) / 2 →
      ∃ anchor : Gtz.WeightedDesign size 3,
        Gtz.HasStrictlyDominatingSubset anchor
          ∧ Gtz.ParallelFreeReachesAnchor size 3 anchor := by
  intro size hsizeAtLeastSix hsizeAtMostSix
  have hsizeIsSix : size = 6 := by omega
  subst hsizeIsSix
  exact ⟨Gtz.icosaDesign, Gtz.icosaDesign_hasStrictlyDominatingSubset,
    Gtz.parallelFreeReachesAnchor_six_three⟩

/--
STATUS: no kernel evidence at any rank in this range, but the anchor half's tail obligation is now a THEOREM: `Gtz.UniformPositionBridge.diagonalTailAtCell_of_two_le` discharges `DiagonalTailAtCell` at every `2 <= extra` and every `2 <= rank` (Gtz/Uniform/AnchorAssembly.lean, single-plane construction; FALSE at `extra = 1`, `not_diagonalTailAtCell_one`, so the guard is sharp -- and the window supplies `extra = size - rank >= rank` for free).
CONSUMERS: `obligationSharpWindowAnchorReach`, which survives as a theorem so no capstone changed.
WHY OPEN: the only `Gtz.ParallelFreeReachesAnchor` instance in the tree is the rank-three one, so nothing here has a single supporting instance.
ATTACK: two pieces remain. (1) ASSEMBLY, mechanical: reindex the axis-aligned core (`sum_core_atomMatrix`) and the diagonal tail (`sum_tailRawWeight_atomMatrix`) along `Fin size = Fin rank (+) Fin (size - rank)`, balance Parseval with `coreTailBookkeeping_feasible`, and feed the weak dominator to `windowAnchorReachFree_of_weakWitness` with `exists_strictAnchor_of_weakDominator`. (2) TOPOLOGY, the real content: per-cell connectivity of the parallel-free locus -- generalize the (6,3) moment-curve walk of Gtz/Reduction/ParallelFreeReach.lean, whose schedule condition is exactly the window floor (`windowCell_meets_walkSchedule`).
NOT-REFUTED: no census row targets any cell with `2 * rank <= size <= rank * (rank + 1) / 2` at rank four or above.
-/
axiom obligationSharpWindowAnchorReachRankFourAndUp :
    ∀ rank : ℕ, 4 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        ∃ anchor : Gtz.WeightedDesign size rank,
          Gtz.HasStrictlyDominatingSubset anchor
            ∧ Gtz.ParallelFreeReachesAnchor size rank anchor

/-- **Split, not weakened.**  Same name, same type as the axiom it replaces, so
every downstream capstone compiles untouched. -/
theorem obligationSharpWindowAnchorReach :
    ∀ rank : ℕ, 3 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        ∃ anchor : Gtz.WeightedDesign size rank,
          Gtz.HasStrictlyDominatingSubset anchor
            ∧ Gtz.ParallelFreeReachesAnchor size rank anchor := by
  intro rank hrankAtLeastThree
  rcases Nat.lt_or_ge rank 4 with hrankBelowFour | hrankAtLeastFour
  · have hrankIsThree : rank = 3 := by omega
    subst hrankIsThree
    exact obligationSharpWindowAnchorReachRankThree
  · exact obligationSharpWindowAnchorReachRankFourAndUp rank hrankAtLeastFour

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
  [`Skeleton.obligationTieFreeUThreeSix,
   `Skeleton.obligationTieFreeOneLine,
   `Skeleton.obligationTieFreeTwoMeetingLines,
   `Skeleton.obligationTieFreeThreeLines,
   `Skeleton.obligationTieFreeKFour,
   `Skeleton.obligationSubThresholdBandHinge,
   `Skeleton.obligationThresholdCellHinge,
   `Skeleton.obligationSharpWindowAnchorReachRankFourAndUp]

end Skeleton
