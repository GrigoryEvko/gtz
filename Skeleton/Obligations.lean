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
  obligations, one per surviving matroid class of the stress-free (6,3)
  stratum.  The 2026-08-08 SHARPENING pushed each of the five DOWN the proved
  chain until it names the first genuinely open statement, spending every
  landed reduction on the way:

  - `obligationBaseTripleTightUThreeSix` =
    `Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` (the
    design-level weak-to-strict upgrade with the weak triple pinned at
    `{0,1,2}`, both separated directions and every tie pin carried, the full
    twenty-triple balance obstruction assumed, one weight at least `1/10`, and
    the no-strict counterexample ledger sharpened by a nonzero gap needle on
    every triple at the attained global cap;
    this is kernel-equivalent to the former A1 statement);
  - `obligationHeavyWeakToStrictOneLine` and
    `obligationHeavyWeakToStrictTwoMeetingLines` =
    the fully wired tenth-heavy line residuals.  The one-line formula retains
    only the joint pair-cap/line-normal blind spot; the two-meeting-lines
    formula retains only the joint cap/two-normal blind spot and asks for one
    of four explicit transversal triples.  Both are kernel-equivalent to the
    former pattern statement;
  - `obligationChartTieFreeThreeLinesFundamentalDomain` =
    `Gtz.ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines`
    on HALF the parameter line (`1 <= |slide|`), outside the allocated budget,
    max-reading, the two fixed unsigned cells, and the one-inequality trace
    cells on all five moved `Z/3` orbits.  The weak witness is restricted to
    the seventeen off-line triples.  The chart-heavy gate is gone because it
    is automatic;
  - `obligationKnifeBandRefinedKFour` =
    `Gtz.KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict`, strictness demanded
    ONLY off Layer A, the exchange star, and the seventeen-cell all-tree minor
    atlas, with explicit nonnegative adjugate witnesses, Gershgorin bad-row
    alternatives, and cleared division-free polynomial edge budgets for every
    one of the sixteen spanning trees.  Every weak non-strict tree, including
    every vertex star, now supplies a nonzero gap kernel and outside pointer.
    Spending the pointer leaves only the positive-definite window pivot wall or
    two independent kernels of the original tree gap.  The former now exposes
    all four window pivots at least one, including the pointer's deletion.  Exact
    irreducible-Z pullbacks exclude the latter branch on all twelve path trees;
    every survivor is a vertex star whose gap is a nonnegative rank-one atom
    and whose two transverse kernel directions carry two distinct outside
    repair pointers.  On that star, one opposite-triangle label strictly
    amplifies two distinct outgoing labels.  Both exchange readings are
    evaluated exactly on two selections proved to be K4 spanning trees.
    Neither repaired tree can be positive definite: the original corank-two
    kernel plane always contains a nonzero direction orthogonal to the incoming
    chart vector, where the repair has nonpositive reading.  Thus the positive
    exchange-reading branch is retained only as a stratifier, alongside the
    strict two-sided boost-ratio reversal.  On the gauge star, the full six
    wall-family equations are retained and atlas silence now removes the
    landed balanced region: either the first positive axis coordinate is not
    maximal, or one of the four vertex-a weights is strictly above `1/6`.
    The exact washout
    witness shows that the bad-row layer alone cannot decide coverage.  Both
    quantifiers are restricted to the sixteen spanning trees.  The chart-heavy
    gate is gone because six positive chart weights sum to one and therefore
    always contain a label of weight at least `1/10`.

  Everything above each axiom survives as a THEOREM -- the old class
  statements `obligationTieFree*`, the intermediate
  `obligationStratumTieFree*` and `obligationChartTieFreeKFour`, and their
  assembly `obligationStressFreeHingeSixThree` -- so no downstream capstone
  changed.

  HOW TO READ "SHARPENING" HERE (round-3 correction).  These moves are NOT
  weakenings of logical strength, and the registry no longer claims they are:
  carving a `forall`-region by a condition on which the conclusion is already
  provable, or adding an antecedent that a tie supplies for free, yields an
  EQUIVALENT Prop every time (kernel-verified this round at three separate
  entries, e.g. `Gtz.patternTightDominatedCoverProperty_iff_stratumIsTieFree`).
  The two auditable metrics are SPEND -- how many landed engines appear in the
  discharge instead of being silently re-demanded -- and REGION/ANTECEDENTS --
  how much smaller the quantified region is and how many facts the eventual
  prover is handed.  The one exception is the chartless pair, where round 2
  really had made the axiom STRICTLY STRONGER than the class statement, so the
  round-3 repair really is a strict weakening; see the CORRECTION fields on
  those two entries.
* Root B, general rank: `forall rank, Gtz.GtzWeightedAll rank`, with no rank
  excluded because `Gtz.gtzWeighted_dim_zero` discharges rank zero.  Needs
  exactly two, `obligationSubThresholdBandHinge` and
  `obligationThresholdCellHingeRankFourAndUp` -- the two hinges.  The reach
  obligation is CLOSED at every rank: the rank-three half by `Gtz.icosaDesign`
  and the rank-four-and-up half by
  `Gtz.GeneralRankReach.sharpWindowAnchorReachRankFourAndUp`, thus both
  `obligationSharpWindowAnchorReachRankFourAndUp` and the assembled
  `obligationSharpWindowAnchorReach` are theorems.

The merged registry count is SEVEN, and the general capstone reaches all
seven.  Before the 2026-08-08 rank split the threshold-cell hinge covered
`3 <= rank`, so its rank-three instance silently re-assumed the entire
rank-three frontier in a strictly stronger wrapper; `obligationThresholdCellHinge`
is now a THEOREM whose rank-three instance is discharged from the five class
residuals, so the general route pays for rank three in exactly the rank-three
currency and no registry axiom subsumes another.

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
STATUS: open -- THE EXACT U(3,6) RESIDUAL is now `Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual`.  It is kernel-equivalent to the former `Gtz.BaseTripleTightLineFreeOffConicWeakToStrict`, but it spends four landed producer layers before exposing the obligation: `Gtz.baseTripleTightLineFreeOffConicWeakToStrict_of_separatedWeakResidualBranch` carries the weak residual direction, strict separation of the tie direction, both share ledgers, the zero discriminant, non-strict base gap, and positive base residual; the twenty-triple balance family closes every light-triple branch; `Gtz.exists_posDef_triple_of_weights_lt_tenth`, obtained in the projection dictionary from the unconditional real tenth spectral supply and the square-transpose law, closes every design whose six weights are below `1/10`; and the general complement-jaw theorem now applies at `Gtz.baseComplementMaxWeight`, the maximum of the pinned base/complement maxima.  Under the explicit no-strict ledger the weak base triple makes the design an `IsTie`, so every triple receives a nonzero needle satisfying `(1 - 2*tau)||v||^2 <= tau*v^T(S_C-I)v`; the cap is attained, lies in `[1/10,1)`, and bounds all six weights.  `Gtz.baseTripleTightLineFreeOffConicHeavyNeedleResidual_iff` proves that this is a formula sharpening, not a strengthening.  Everything between it and the class statement remains theorem-only.
CONSUMERS: `obligationTieFreeUThreeSix` (now a theorem), hence `obligationStressFreeHingeSixThree` and the rank-three capstone.
WHY OPEN: on a line-free stratum every distinct triple is a basis, so no pruning rule bites, and the deflation rule is provably inert (`Gtz.not_blindLabel_lineFree`, Gtz/Design/StratumTieFreeClasses.lean). The tree records that attacking this class FIRST is backwards (StratumTieFreeClasses.lean:207-215); it is sequenced LAST, after the four rigid classes.
ATTACK: start from the conic characterization, never from a selector. The formulation layer is now IN KERNEL (Gtz/Design/LineFreeConicBridge.lean): `Gtz.LineFreeOffConicWeakToStrict` (antecedent KEPT -- load-bearing here) reduces the class statement verbatim via `Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict`, and this obligation sits one step below it; the two-family assembly `Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies` is proved; the mass-reading clearance functionals (`Gtz.wallClearanceOf`, positive exactly on the open stratum -- clearance MUST read masses, the fiber margin infimum is zero at every direction tuple via mass collapse) are defined; and the exact rational icosa approximant (`Gtz.icosaApproximantDirection`: kernel-proved line-free, stress-free, off-conic, with `Gtz.icosaApproximantChartPoint_hasStrictTriple`) is the interior family's seed. STAGE-3 UPDATE (2026-08-08): the interior family is fully interfaced -- `Gtz.ClearanceBoundedInteriorFloor` (weak antecedent kept) reduces through `Gtz.interiorFamilyMarginFloor_of_clearanceBounded` into the assembly, the orbit split is spent once in kernel (`Gtz.clearanceBoundedInteriorFloor_of_baseTriple` pins the weak triple at {0,1,2} via the proved relabelling-invariance suite), and the icosa seed is quantitative (`Gtz.icosaApproximant_gap_floorThree`, moment matrix tau * identity). The collar is split per wall (`Gtz.boundaryCollarExcludesTies_wallClearance_of_perWall`); the attained mass wall provably lies ON the conic wall (`Gtz.not_hasNoCommonQuadric_of_atom_eq_zero`), the stress walk is quantified with explicit off-wall residual, and dust-ray witnesses cover both named surviving ties (`Gtz.tetraCorner_gap_posDef_on_dustRay` on (0,1/4], `Gtz.diamondCorner_gap_posDef_on_dustRay` on (0,1/16]). STAGE-4 UPDATE (2026-08-08): the instance at the scan-proposed constants (1/16, 1/4) is REFUTED IN KERNEL -- `Gtz.baseTripleClearanceBoundedFloor_sixteenth_quarter_refuted` and `Gtz.clearanceBoundedInteriorFloor_sixteenth_quarter_refuted` (exact rational Parseval refuter, Cayley Stiefel rows over square weights, line-free, off-conic via the first exact 6x6 Veronese determinant in the tree, clearance above 1/16, all twenty triples defeated at the 1/4 floor); the in-region margin record ladder (0.237 -> 0.1724 -> 0.1145 under heavy weight tilts) has not stabilized at any positive floor. STAGE-5 UPDATE (2026-08-08): the adversarial minimax DECIDED the interior question over `Gtz.wallClearanceOf` negatively, in kernel -- NO constant pair with cf <= 3/8 and mf >= 1/16 exists (`Gtz.baseTripleClearanceBoundedFloor_rectangle_refuted`, `Gtz.clearanceBoundedInteriorFloor_rectangle_refuted`) and NO Monotone clearance-graded floor reaching 1/16 by clearance 3/8 exists (`Gtz.interiorFamilyMarginFloor_monotoneGraded_refuted`); the escape is the dust-weight channel (raw weights below ~1/128 mask a jointly degenerating frame from every weight-compensated clearance leg; margin infimum 0 in EVERY wallClearanceOf band, exact witness with best margin in [7.619e-5, 7.620e-5] at exact wall clearance >= 1/4; a raw-weight floor restores the margin linearly, measured stall ~2.2 x weightFloor). Truth of tie-freeness is never threatened -- the escape runs along the open weight-simplex boundary where no design exists. Remaining: RE-FOUND the interior family on a weight-aware clearance functional (e.g. min of wallClearanceOf and a scaled minimum raw weight; the two-family assembly `Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies` is already parametric in the functional, so this costs interfaces, not plumbing), with mandatory adversarial re-validation at the repaired region before any instance is proposed; PLUS the collar at the repaired region -- which now needs a dust-WEIGHT witness family (the landed tetra/diamond dust-MASS rays do not cover it; required witness floors are linear in the raw weight, the same margin ~ 2 x dustWeight law as the corner cascade -- the universal boundary law of this stratum). The joint three-coordinate corner of the collar stays WALLED as `wallUThreeSixJointCornerCollar` after three documented rounds (no uniform-margin mechanism exists at any positive floor; the margin dies linearly only along the full offset x dust-weight x dust-ratio cascade; the (5,3) exclusions are branch-(ii) objects needing a compactification bridge before they bite here).
NOT-REFUTED: no census row targets the class statement. What IS refuted are methods: every finite pure-triple or orbit selector, every constant, label-free or continuous selector, matroid exchange, bounded-radius search, weight-uniform threshold certificates (margin infimum zero), and Putinar/Schmuedgen. A stress-forcing pattern filter cannot apply here: it would assert every line-free design lies on a conic.
-/
axiom obligationBaseTripleTightUThreeSix :
    Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual

/-- The narrowed registry axiom reconstructs the former A1 statement through
the fully wired producer chain. -/
theorem obligationBaseTripleTightUThreeSix_full :
    Gtz.BaseTripleTightLineFreeOffConicWeakToStrict :=
  Gtz.baseTripleTightLineFreeOffConicWeakToStrict_of_separatedHeavyResidual
    (Gtz.separatedHeavyResidual_of_heavyNeedleResidual
      obligationBaseTripleTightUThreeSix)

/-- **Discharged from the sharpened axiom.**  Same name, same statement:
`Gtz.lineFreeOffConicWeakToStrict_of_baseTripleTight` spends the five-lemma
relabelling-invariance suite to pin the weak triple at `{0,1,2}` and the new
pointwise KKT extraction `Gtz.exists_tightDirection_of_dominates_not_posDef`
to supply the tight direction.  Equivalence, not weakening (round-3 metric):
what changes is that five landed lemmas plus the extraction are SPENT here
rather than re-demanded of the eventual prover. -/
theorem obligationWeakToStrictUThreeSix : Gtz.LineFreeOffConicWeakToStrict :=
  Gtz.lineFreeOffConicWeakToStrict_of_baseTripleTight
    obligationBaseTripleTightUThreeSix_full

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the class statement follows from the exact residual
`obligationWeakToStrictUThreeSix` by the tree's own reduction
`Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict`. -/
theorem obligationTieFreeUThreeSix :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern []) :=
  Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict obligationWeakToStrictUThreeSix

/--
STATUS: open -- the one-line residual is `Gtz.OneLineTenthHeavyJointBlindLineSparse`: every LEVERAGE-HEAVY design of the stratum that carries SOME weakly dominating card-3 subset, a label of RAW WEIGHT at least `1/10`, and lies simultaneously in `Gtz.IsCapBlindSpot` and `Gtz.IsOneLineNormalBlindSpot`, satisfies the existing ten-way `Gtz.PlaneBranchTenCandidate` selector. Four landed engines have already fired before the axiom: the all-light theorem, the pair-cap engine, the line-normal lift criterion, and the exact localization excluding every strict triple with two atoms from `{0,1,2}`. The endpoint is deliberately shared with the line-free U(3,6) plane branch rather than duplicated. `Gtz.oneLineTenthHeavyJointBlindLineSparse_iff` proves this formula equivalent to the former `Gtz.PatternHeavyWeakToStrict`; it is not a stronger sufficient condition. No plane-cover quantifier and no tight direction survive. The remaining class chain is unchanged: `Gtz.patternTightDominatedCoverProperty_iff_heavyWeakToStrict`, `Gtz.stratumIsTieFree_of_tightDominatedCoverProperty`, and the relabel bridge recover class tie-freeness. The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_oneThreePointLine`, Gtz/Reduction/TrichotomyLedger.lean:485).
CORRECTION (2026-08-08, round 3): the round-2 entry `obligationReducedCoverOneLine` (`Gtz.PatternReducedCoverProperty`) was a STRENGTHENING sold as a sharpening and has been RETIRED OUTRIGHT -- it does not survive as a theorem, because the tight-dominated form does not imply it. Unconditioned on ties, the reduced cover property forces a STRICTLY dominating card-3 subset at EVERY design of the stratum (`Gtz.hasStrictDominator_of_reducedCoverProperty`), i.e. the stratum-restricted strict half of the very conclusion the campaign is proving, on top of tie-freeness. The replacement is kernel-EQUIVALENT to the class statement (`Gtz.patternTightDominatedCoverProperty_iff_stratumIsTieFree`, using the new converse of the producer `Gtz.normalSurplus_planeCover_of_posDef`), so it asserts nothing beyond it. No partial work is lost: the stage-4 RCP attack was developed against the unconditioned form, and adding antecedents only hands a prover more.
CONSUMERS: `obligationStratumTieFreeOneLine` (now a theorem), hence `obligationTieFreeOneLine`, `obligationStressFreeHingeSixThree`, and the rank-three capstone.
WHY OPEN: of the six producers of `Gtz.StressFreeStratumIsTieFree` in the tree, three are chart instances at other patterns, the plane-pair filter is provably anti-aligned (the residual list IS the not-plane-pair-covered list, Gtz/Design/StressFreeMatroidStratification.lean:303), and the two generic chart forms need a chart nobody has built for this pattern.
ATTACK: build the chart following the shipped precedent -- Gtz/Design/RigidityBridge.lean:1-60 (PGL(3) simply transitive on four general lines, made rational, plus the per-atom scaling group) and the structure of `Gtz.directionChartCoversPrimitiveStratum_kFourDirection`. The pattern pins only three atoms projectively, so the chart carries genuine moduli and the analytic half is a parametric family. BUILD THIS CLASS FIRST of the two chartless ones: its boundary is diamond-FREE, so uniform-in-parameter arguments should survive. Corpora triage complete (2026-08-07): /tmp/gtz-p38/rigidity2 and /tmp/gtz-p35/zerochart are empty/dead; the w2 lane targeted the K4 tube route, nothing shortcuts the chart build. Direct-route levers: a tie's weak dominator avoids the line (`Gtz.not_dominates_of_atomBracket_eq_zero`), hence is one of the NINETEEN basis triples; the line's common orthogonal is the lever -- Parseval transfers the whole normal direction to the three free atoms, and positivity of the line weights makes the free triple exceed the identity STRICTLY along the normal, a strict seed present on every design of the stratum. Exact-rational non-vacuity sample with two strictly dominating triples now IN KERNEL: `Gtz.oneLineSampleDesign` (Gtz/Design/LineClassObstructions.lean) with `Gtz.oneLineSampleDesign_not_isTie`; the census ladder G1-G3/O1-O7 is landed in the same module (the relabel bridge `Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` closes this obligation from any identity-labelled tie-freeness proof). STAGE-3 UPDATE (2026-08-08): the producer layer is LANDED -- the pointwise normal seed `Gtz.exists_complementAtom_overcovers_normal` (one complement atom alone beats the squared normal), the uniform Schur producer `Gtz.posDef_of_normalSurplus_planeCover` (normal surplus + plane cover => PosDef gap, one completed square, direction-generic), and the tie-side `Gtz.isTie_yields_planeCover_failure`. The class residual is ONE statement, RCP: some card-3 subset satisfies both producer hypotheses. Constraints on any RCP proof (exact witnesses in the campaign record): the argmax-normal-conductance selection is refuted at the matched-normal knife, and NO uniform margin floor exists on the stratum (an explicit rational family collapses the margin like 1/N at the line-starved normal-matched weight corner) -- the proof must be sign-only; recommended attack is rank-2 slack in the plane with per-atom penalty deflations, worked at that corner first. STAGE-4 UPDATE (2026-08-08): the corner reduces to a dichotomy on min_i eps_i vs 1/2; leg B (all eps in the closed half [0, 1/2], including the E = I/2 knife) is PEN-PROVED via the Half-Plane Lemma (Bhatia-Davis range bound x_min x_max <= -V with a matroid equality-kill; campaign record, stage-4 rcp lane -- NOT yet in kernel); leg C is reduced with zero slack (gamma-elimination + von Neumann duality) to RCP-C1: all eps_i > 1/2 implies an admissible vertex dual y with VERT_k below mu_k (401 strict exact confirmations, zero violations, max cValue -23/799); plus the RCP-LIFT seam (corner-to-interior: A-triples are corner-redundant but NOT interior-redundant, 9/360). CLOSED DOOR: b-averaged and ALL line-data-only C-engines are provably insufficient -- they die on the isotropic band E = cI (exact witness: lines (1,0), (4,7), (-4,7), masses (363/980, 11/1960, 11/1960), c = 11/20; band (1/2, 4/7]); any C-certificate must read shadow data. STAGE-6 UPDATE (2026-08-08, round 4 landings): the residual is now QUANTIFIER-FREE and two thirds discharged. `Gtz.subsetSum_posDef_iff_tripleInvariants` decides strict domination by three coordinate-free polynomial inequalities in the atoms' leverages, pair cross-norms and bracket (Cauchy-Binet plus a hand-rolled Sylvester -- Mathlib has none), and `Gtz.subsetSum_posDef_of_heavy_of_minorSum_of_det` discharges the FIRST of the three from heaviness outright, so the open content is exactly TWO polynomial inequalities at a card-3 subset containing one strictly heavy atom. Two independent quantifier eliminations are landed: the anatomy-free pair-difference form (`Gtz.planeCover_iff_pairDifferenceExcess`, of which LLF/LFF/FFF are the three specializations, each an Iff with its producer and its blind-probe kill) and the frame-minor form (`Gtz.posDef_iff_surplus_and_frameMinors`, three scalars against any orthonormal plane frame). The TIE SIDE is collapsed to three two-dimensional refusals (`Gtz.noStrictDominator_yields_overReaderRefusals`), the surplus premise of each discharged by weighted Parseval. The IN-PLANE half is an instance of a THEOREM: the restriction to an orthonormal plane frame is a genuine rank-two WeightedDesign (`Gtz.inPlaneRestriction`) so `Gtz.gtz_rank_two` hands back a covering pair (`Gtz.exists_inPlane_dominating_pair`). ANATOMY IS DEAD, and now dead IN SCOPE: `Gtz.not_oneLineLlfSelectorAtTightAntecedent` refutes two-line-plus-one-free INSIDE this obligation's own antecedent region (`Gtz.tightLlfDesign` fires pattern, heaviness, the weak dominator {0,1,3} and its tight direction (0,8,-3)); `Gtz.refutes_uniform_llf_rule` and `Gtz.refutes_uniform_fff_rule` kill both uniform anatomies at heavy designs; `Gtz.not_complementSelectorRule` and `Gtz.not_freeTripleSelectorRule` kill the two remaining named selectors. The mechanism is the LEVERAGE FLOOR: every member of a strict dominator is STRICTLY heavy (`Gtz.one_lt_leverage_of_mem_of_posDef`) while heaviness supplies only `1 <= leverageOf`, so a floor atom poisons all ten subsets containing it. CONSEQUENCE: `Gtz.oneLine_planeCover_of_inPlaneExcess` is a DEAD ROUTE with zero consumers, retained only as the exact statement of what fails. The margin question is settled two-sided: `Gtz.margin_cap_and_its_floor` shows the cap at a line normal is at least lineWeight/complementWeight, so ONLY starving the line weight can drive the margin to zero -- no in-plane angle and no single free weight can. PRIOR ART, checked: restricted invertibility (Bourgain-Tzafriri, Vershynin, BSS, MSS) is VACUOUS at k = d, which is exactly this cell; nothing published discharges it. METHOD WARNING: exact-rational sampling is NOT adversarial for strict-inequality conjectures here -- a 1500/1500-supported conjecture was false on a tangency locus rational sampling cannot reach.
NOT-REFUTED: no census row targets it. The stress-forcing filter door is CLOSED, not just unused: the pattern forces stress-freeNESS uniformly (`Gtz.stratumIsStressFree_oneThreePointLine`, TrichotomyLedger.lean:485), so a filter asserting a forced nonzero stress is refutable at any design of the stratum, and the residual list is already exactly the not-plane-pair-covered list (StressFreeMatroidStratification.lean:303). Only direct tie obstructions remain admissible here.
-/
axiom obligationHeavyWeakToStrictOneLine :
    Gtz.OneLineTenthHeavyJointBlindLineSparse

/-- The wired one-line axiom reconstructs the former chartless residual by
spending the all-light, pair-cap, line-normal lift, and ten-candidate
localization theorems. -/
theorem obligationHeavyWeakToStrictOneLine_full :
    Gtz.PatternHeavyWeakToStrict (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  Gtz.patternHeavyWeakToStrict_oneLine_of_tenthHeavyJointBlindLineSparse
    obligationHeavyWeakToStrictOneLine

/-- **Discharged from the sharpened axiom.**  Same name, same statement:
`Gtz.patternTightDominatedCoverProperty_of_heavyWeakToStrict` reinstates the
unit normal (`![1,0,0]` will do -- ANY unit normal will do) and both producer
hypotheses from the bare positive definite gap, through the landed converse
`Gtz.normalSurplus_planeCover_of_posDef`.  Equivalence, not weakening: the two
Props are interderivable by
`Gtz.patternTightDominatedCoverProperty_iff_heavyWeakToStrict`.  What the swap
buys is FORMULA SIZE at zero logical cost -- the unit-normal existential, the
forall-probe plane cover and the Rayleigh equation all leave the statement a
prover has to attack. -/
theorem obligationTightDominatedCoverOneLine :
    Gtz.PatternTightDominatedCoverProperty (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  Gtz.patternTightDominatedCoverProperty_of_heavyWeakToStrict _
    obligationHeavyWeakToStrictOneLine_full

/-- **Discharged from the repaired axiom.**  Same name, same statement as
before: `Gtz.stratumIsTieFree_of_tightDominatedCoverProperty` spends the heavy
narrowing, the tie's weak dominator and its tight direction, then applies the
uniform Schur producer against the tie's second component. -/
theorem obligationStratumTieFreeOneLine :
    Gtz.StratumIsTieFree (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  Gtz.stratumIsTieFree_of_tightDominatedCoverProperty obligationTightDominatedCoverOneLine

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the relabel bridge
`Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` closes the class statement
from identity-labelled tie-freeness -- no relabel quantifier, no
stress-freeness hypothesis (the stratum is uniformly stress-free,
`Gtz.stratumIsStressFree_oneThreePointLine`). -/
theorem obligationTieFreeOneLine :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [[0, 1, 2]]) :=
  Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree _ obligationStratumTieFreeOneLine

/--
STATUS: open -- the two-meeting-lines residual is `Gtz.TwoMeetingLinesTenthHeavyJointBlindTransversal`. It retains leverage heaviness, a weak dominator and a raw weight at least `1/10`, assumes the pair-cap engine and both line-normal lift criteria are blind, and asks only that one of `{1,3,5}`, `{1,4,5}`, `{2,3,5}`, `{2,4,5}` dominate strictly. Every other triple has already been excluded by the exact matroid/flat-pair theorem. `Gtz.twoMeetingLinesTenthHeavyJointBlindTransversal_iff` proves this formula equivalent to the former pattern statement. This class is diamond-CARRYING, so the residual remains genuinely boundary-sensitive; the stratum is uniformly stress-free (`Gtz.stratumIsStressFree_twoMeetingLines`, Gtz/Reduction/TrichotomyLedger.lean:491).
CORRECTION (2026-08-08, round 3): as at the one-line pattern, the round-2 entry `obligationReducedCoverTwoMeetingLines` was a STRENGTHENING and is RETIRED OUTRIGHT, not demoted -- see the one-line entry for the kernel evidence.
CONSUMERS: `obligationStratumTieFreeTwoMeetingLines` (now a theorem), hence `obligationTieFreeTwoMeetingLines`, `obligationStressFreeHingeSixThree`, and the rank-three capstone.
WHY OPEN: same producer situation as the one-line class -- no chart exists for this pattern and the plane-pair filter is structurally inapplicable. Two concurrent lines are the closest residual pattern to the plane-pair boundary: the two line planes cover five of the six atoms, and it is exactly the sixth that escapes the escape law.
ATTACK: same chart-building precedent as the one-line class (RigidityBridge.lean:1-60 plus the :796 covering structure); the pattern pins five atoms up to the two line moduli, so the chart is SMALLER than the one-line chart -- but build it SECOND: this class is diamond-CARRYING (`Gtz.diamondCarryingResidualFamiliesSix`, StressFreeMatroidStratification.lean:580), a positive-dimensional (5,3) tie family through `Gtz.diamondDesign` sits on its weight-zero boundary, margins die linearly there and no uniform-in-weights certificate exists; the boundary leg must route the diamond shadow through the proved five-label exclusions, with the open-atom lift identity as the skeleton. Direct-route levers: a tie's weak dominator avoids BOTH lines, leaving EIGHTEEN basis triples; the two normals are provably non-parallel and the shared atom is pinned projectively to the plane intersection -- the class's rigidity kernel; Parseval gives one strict seed per line. STAGE-6 UPDATE (2026-08-08, round 4 landings): everything recorded at the one-line entry applies verbatim (the three-invariant criterion, the heaviness discharge of the trace invariant, both quantifier eliminations, the tie-side collapse, the rank-two in-plane dispatch, the leverage floor, the two-sided margin cap) -- the whole layer is pattern-generic. TWIN-SPECIFIC: the shared atom, this class's rigidity kernel and the obvious thing for a selector to reach for, is UNUSABLE at unit leverage -- all TEN card-3 subsets containing it fail (`Gtz.sharedAtomUnit_every_subset_with_shared_atom_fails`), because each pairs it with a partner on one of the two lines and that pair is flat against that line's normal. The line complement is not a selector either (`Gtz.mixedSurvivor_lineComplement_not_posDef`); at that witness the survivors are MIXED triples taking one atom from each line. And the second line never covers at the first normal: the shared atom together with the second line's private pair is pair-difference BLIND along the second normal's in-plane component, for EVERY choice of the first normal (`Gtz.twoMeetingLines_secondLine_planeCover_fails`), which is the two-meeting-lines rigidity in reading form.
NOT-REFUTED: no census row targets it. The stress-forcing filter door is CLOSED, not just unused: the pattern forces stress-freeNESS uniformly (`Gtz.stratumIsStressFree_twoMeetingLines`, TrichotomyLedger.lean:491), the opposite polarity to any stress-forcing mechanism, and the plane-pair law already consumed every coverable class (StressFreeMatroidStratification.lean:303). Only direct tie obstructions remain admissible here.
-/
axiom obligationHeavyWeakToStrictTwoMeetingLines :
    Gtz.TwoMeetingLinesTenthHeavyJointBlindTransversal

/-- The wired two-meeting-lines axiom reconstructs the former chartless
residual by spending the all-light, pair-cap and two-normal lift theorems. -/
theorem obligationHeavyWeakToStrictTwoMeetingLines_full :
    Gtz.PatternHeavyWeakToStrict
      (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  Gtz.patternHeavyWeakToStrict_twoMeetingLines_of_tenthHeavyJointBlindTransversal
    obligationHeavyWeakToStrictTwoMeetingLines

/-- **Discharged from the sharpened axiom.**  Same name, same statement; the
same pattern-generic collapse as at the one-line pattern. -/
theorem obligationTightDominatedCoverTwoMeetingLines :
    Gtz.PatternTightDominatedCoverProperty
      (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  Gtz.patternTightDominatedCoverProperty_of_heavyWeakToStrict _
    obligationHeavyWeakToStrictTwoMeetingLines_full

/-- **Discharged from the repaired axiom.**  Same name, same statement as
before: the same pattern-generic
`Gtz.stratumIsTieFree_of_tightDominatedCoverProperty` closes this stratum. -/
theorem obligationStratumTieFreeTwoMeetingLines :
    Gtz.StratumIsTieFree (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  Gtz.stratumIsTieFree_of_tightDominatedCoverProperty
    obligationTightDominatedCoverTwoMeetingLines

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the relabel bridge
`Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` closes the class statement
from identity-labelled tie-freeness at this pattern too. -/
theorem obligationTieFreeTwoMeetingLines :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4]]) :=
  Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree _ obligationStratumTieFreeTwoMeetingLines

/--
CURRENT STATUS: the open formula is `Gtz.ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines`. It lies on the fundamental domain, outside the allocated budget cells, the max-reading cover, the two fixed unsigned cells, and five additional one-inequality trace cells evaluated over every member of their exact `Z/3` mass orbit. The five representative triples are `{0,1,4}`, `{0,1,5}`, `{0,2,4}`, `{0,2,5}`, and `{0,4,5}`; with the two rotation-fixed triples they exhaust the seven independent orbit types. Its weak witness is one of the seventeen off-line triples, and no chart-heavy premise remains. `Gtz.chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff` proves exact equivalence with public A2. The former two-fixed-cell formula is now a theorem reconstructed by dispatching the moved atlas. No inhabitant of this final complement is currently proved. The following STATUS paragraph is retained as a historical pre-unsigned-cell snapshot and is superseded by this line.
STATUS: chart-covered, analytic half open. The covering half is the unconditional `Gtz.parameterizedChartCovers_threeLinesDirection` (Gtz/Design/RigidityBridge.lean:1098) with consumer `Gtz.stressFreeStratumIsTieFree_threeLines_of_chart` (:1135); the stratum is uniformly stress-free (`Gtz.stratumIsStressFree_threeLines`, Gtz/Reduction/TrichotomyLedger.lean:497). What is open is the off-lines, budget-and-reading-blind tenth-heavy residual `Gtz.ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines` on HALF the admissible parameter line, the fundamental domain `1 <= |slide|`. Five landed engines have fired before the axiom. First, the chart at `slide` is realized over the chart at `1/slide`, so only the fundamental domain remains. Second, `Gtz.exists_design_of_chartPoint` and the unconditional strict tenth floor remove every all-light point. Third, the allocated Cauchy--Schwarz certificate removes both canonical semialgebraic cells: the vertex triple `{0,1,3}` and the free triple `{2,4,5}`. Fourth, `Gtz.posDef_directionChartGap_threeLines_of_readingCover` removes any point admitting a card-three set that contains a maximal kappa reading at every probe. Fifth, the normal-axis exclusions prove that none of the three dependent lines `{0,1,2}`, `{0,3,4}`, `{1,3,5}` can even supply the weak antecedent. The live point is therefore tenth-heavy, lies outside all three strictness cells, and carries a weak witness among exactly the seventeen off-line triples. `Gtz.chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines_iff` proves the narrowed formula equivalent to the former A2 statement; it is not a stronger sufficient condition.
CONSUMERS: `obligationStressFreeHingeSixThree` (the split parent, now a theorem), hence the rank-three capstone.
WHY OPEN: the budget inequalities and the reading-cover condition are sufficient cells, not an exhaustive cover. The two exact rational witnesses prove both budget cells are inhabited, but no theorem says every tenth-heavy weak point enters a budget cell or admits one fixed card-three max-reading cover. Removing the three dependent witnesses narrows the finite search but does not select a strict triple among the seventeen survivors. The strict-triple producer `Gtz.directionChartIsTieFree_of_hasStrictTriple` remains false at a degenerate direction, and the reindexing producer only moves a certificate from one slide to another.
ATTACK: cover the complement of the two explicit allocation cells and the max-reading cover cell, PARAMETRICALLY in `slide`, or add further certificate cells and spend them through the same blind-residual IFF. The `Z/2` involution is ALL the symmetry available: the pattern automorphism group is `S3` on the triangle {0,1,3}, acting on the Menelaus modulus `J = slide` by 3-cycles trivially and by inversion on transpositions, so halving is the ceiling of the symmetry route and no further region carving is free. The two excluded slides are degenerations onto a collapsed atom or the M(K4) pattern; they are not gaps.
NOT-REFUTED: no census row targets it. The strict-triple refutation kills only that producer's premise at a degenerate direction, not this statement. No stress-forcing filter can apply (TrichotomyLedger.lean:497).
-/
axiom obligationChartTieFreeThreeLinesFundamentalDomain :
    Gtz.ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines

/-- The seven-orbit-trace-blind A2 axiom reconstructs the former
fundamental-domain statement by spending the complete unsigned atlas. -/
theorem obligationChartTieFreeThreeLinesFundamentalDomain_full :
    Gtz.ChartTieFreeThreeLinesFundamentalDomain :=
  Gtz.chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff.mp
    obligationChartTieFreeThreeLinesFundamentalDomain

/-- **Discharged from the sharpened axiom.**  Same name, same statement: half
the parameter line is now a THEOREM.  The chart at slide is realized over the
chart at `1/slide` (relabel = swap the triangle vertices 0 and 1, which forces
the side points 4 and 5 to swap; basis `!![0,1,0; 1,0,0; 0,0,slide]`, scale
`(1,1,1,1/slide,1,1)`), so `Gtz.directionChartIsTieFree_of_reindex` transports
tie-freeness across the involution and
`Gtz.chartTieFreeThreeLines_of_fundamentalDomain` closes the whole admissible
line from `1 <= |slide|` alone.  The pattern automorphism group is `S3` on the
triangle `{0,1,3}`, acting on the Menelaus modulus `J = slide` trivially by
3-cycles and by inversion on transpositions, so `Z/2` is ALL the symmetry
available and halving is the ceiling of this route. -/
theorem obligationChartTieFreeThreeLines :
    ∀ slide : ℝ, Gtz.IsAdmissibleThreeLinesParameter slide →
      Gtz.DirectionChartIsTieFree (Gtz.threeLinesDirection slide) :=
  Gtz.chartTieFreeThreeLines_of_fundamentalDomain
    obligationChartTieFreeThreeLinesFundamentalDomain_full

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the covering half is the unconditional
`Gtz.parameterizedChartCovers_threeLinesDirection`, so the class statement
follows from the slide-parametric chart residual by
`Gtz.stressFreeStratumIsTieFree_threeLines_of_chart`. -/
theorem obligationTieFreeThreeLines :
    Gtz.StressFreeStratumIsTieFree
      (Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4], [1, 3, 5]]) :=
  Gtz.stressFreeStratumIsTieFree_threeLines_of_chart obligationChartTieFreeThreeLines

/--
CURRENT STATUS: the open formula is `Gtz.KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict`. It is restricted to spanning trees and lies outside Layer A, the exchange star, and the seventeen-cell all-tree unsigned minor atlas. The pointer-window descent is fully spent before the axiom. Its positive-definite branch exposes a four-edge window whose pivot is at least one at every one of its four labels, including the incoming pointer. Its singular branch is restricted to the four vertex stars; the original PSD tree gap has two independent kernel directions, is a nonnegative scalar multiple of their cross-product atom, and the directions carry two distinct outside repair pointers with transverse strict-reading guarantees. The amplified-exchange producer now fires uniformly on all four stars: one opposite-triangle label strictly beats two distinct outgoing star labels in squared kernel reading, both repaired selections lie in the sixteen-tree family, and both quadratic readings are evaluated exactly. The universal refusal theorem proves that neither one-slot repair is positive definite: inside the original two-dimensional kernel there is always a nonzero vector orthogonal to the incoming direction, and the repaired gap reads there as minus the outgoing boost square. Consequently a positive reading on the amplified probe is a stratifier rather than the missing strict selector; the exhaustive branch still retains that reading and the strict inequality placing the incoming boost quotient below both outgoing quotients. The gauge-star branch now also retains its positive-axis wall coordinates and six division-free equations. The three balanced star certificates exhaust the maximal-axis split. Atlas silence therefore couples whichever one of `z 0`, `z 1`, or `z 2` is maximal to a weight strictly above `1/6` in that vertex star's exact four-slot cover; in particular the uniform-weight gauge wall is impossible. The path-corank branch is empty by two independent landed proofs: the twelve irreducible-Z pullbacks and the rank-one chart-coefficient sign law. `Gtz.kFourKnifeBandRefinedTreeStarRefusedMaxHeavyWall_iff` proves exact equivalence with the public refined knife band, so this is a formula sharpening rather than a new assumption. The exact rational Gershgorin washout point still shows that the bad-row or bad-budget system alone cannot decide coverage. No inhabitant of the fully exposed residual is currently proved. The following long STATUS paragraph is retained as a historical pre-unsigned-cell snapshot and is superseded by this line.
STATUS: the most rigid class; covering half PROVED (`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`, Gtz/Design/RigidityBridge.lean:796), direct class consumer `Gtz.stressFreeStratumIsTieFree_graphicKFour_of_chart` (:834). The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_graphicKFour`, Gtz/Reduction/TrichotomyLedger.lean:505). NOT VACUOUS: the stage-four audit's coordinate-diagonal design (the regular tetrahedron's six edge directions) realizes exactly this pattern. Open: `Gtz.KFourKnifeBandRefinedTenthHeavyWeakToStrict` -- a strictly dominating SPANNING TREE demanded ONLY at a tenth-heavy weakly dominated chart point where NEITHER covered region fires: Layer A (the twenty landed cells, named `Gtz.KFourLayerACellFires`, spent as `Gtz.kFourAtlas_hasStrictTriple_of_layerAFires`) nor the exchange star (`Gtz.KFourExchangeStarCellFires`, spent as `Gtz.kFourAtlas_hasStrictTree_of_exchangeStarCell`). Both quantifiers range over the sixteen spanning trees rather than the twenty card-3 subsets, which is sound because a weak dominator is never a dependent triple (`Gtz.kFourWeakAntecedent_yieldsSpanningTree` over the dichotomy `Gtz.cardThreeSubset_isSpanningTreeOrDependentTriple`). The all-light branch is discharged by the chart whitening, `Gtz.posDef_massMoment_kFourDirection`, and the strict tenth floor; `Gtz.kFourKnifeBandRefinedTenthHeavy_iff` proves this is equivalent to the former refined band. `Gtz.kFourKnifeBandWeakToStrict_of_refined` then recovers the round-2 band, and the boundary split `Gtz.directionChartIsTieFree_kFour_of_knifeBandWeakToStrict` closes the chart. CANONICAL BAND INHABITANT: `Gtz.bandResidualWitnessPoint` (mass (3,16,1,5,3,2), weight (3,1,1,1,3,1)/10; kernel-witnessed outside BOTH regions) -- NOT `Gtz.heavyPairRefuterPoint`, which the exchange star now COVERS (`Gtz.heavyPairRefuterPoint_exchangeStarCellFires`). Eleven positive reals against six FIXED rational chart vectors, sixteen trees, no design, no whitener, no square root in the residual statement.
CONSUMERS: `obligationChartTieFreeKFour` (now a theorem), hence `obligationTieFreeKFour`, `obligationStressFreeHingeSixThree`, and the rank-three capstone.
WHY OPEN: the only DIRECTION-GENERIC producer of `Gtz.DirectionChartIsTieFree` is `Gtz.directionChartIsTieFree_of_hasStrictTriple` (:176) -- the eight others are either K4-specific (the four selection bridges and the knife-band split in KFourChartClosure) or transport-only (`Gtz.directionChartIsTieFree_of_reindex` and its three-lines instances move a certificate between charts and cannot manufacture the first one) -- and its premise `Gtz.DirectionChartHasStrictTriple` is kernel-FALSE at a degenerate DIRECTION (a non-spanning family -- no refutation exists at any valid `kFourDirection` chart point, and ~19000 exact-rational adjudications found none); the antecedent-free form is still never landed as a named global. The class-level sibling `stressFreeStratumIsTieFree_graphicKFour_of_strictTriple` (:841) stays forbidden as a route.
ATTACK: DECIDED (spike, 2026-08-07): the DIRECT road; collar weld rejected (three nonexistent layers). LANDED SINCE (Gtz/Design/KFourChartClosure.lean, 2026-08-08): the whole contraction-descent brick set -- the rank-two Foster engine, `Gtz.rankTwoSlackLemma` (Lemma A), kappa-free `Gtz.sylvesterLift`, the twelve entrywise gap matrices, the dependent-triple PSD exclusion, `Gtz.kFourContractionHasWinner` (at EVERY chart point some tree through edge 5 has PD contracted block, no maximality needed), the det normal forms, and the consumption bridge -- PLUS the kernel REFUTATION of the max-conductance selection: `Gtz.kFourMaxEdgeHostsStrictTree_refuted` and `Gtz.kFourMaxEdgeDetPigeonhole_refuted` at `Gtz.maxEdgeRefuterPoint` (strict argmax edge 3, dominant masses on the dependent triangle {0,3,4}), while the chart obligation stays INTACT there (`Gtz.maxEdgeRefuterPoint_hasStrictTriple`, {0,1,4} dominates strictly). STAGE-3 UPDATE (2026-08-08): the mass-reading direction is ALSO kernel-refuted -- `Gtz.kFourDominantMassPairHostsStrictTree_refuted` at the dual witness `Gtz.heavyPairRefuterPoint` (same weights, triangle-closer mass 18 past the pair's series threshold 120/7) and `Gtz.kFourMaxAlphaEdgeHostsStrictTree_refuted` at the landed witness; with the max-conductance refutation these close every per-label scalar ordering, and per-class representative rules die at tetrahedron shells (exact witnesses, campaign record). STAGE-4 UPDATE (2026-08-08): the certificate atlas's Layer A is COMPLETE -- all TWENTY cells (four star + sixteen harmonic, entrywise gap lemmas for every spanning tree, engine `Gtz.harmonicSplitQuadraticForm_pos`) with total dispatch `Gtz.kFourAtlas_hasStrictTriple_of_anyCell`; Layer A is NOT a total atlas: `Gtz.heavyPairRefuterPoint` fires no Layer-A cell (its PD trees are exactly the six through edge 3), and the fresh-seed census leaves a 464-point exact leftover corpus (405 knife-edge; campaign record, stage-4 harm lane) -- the residual is the knife band ALONE, with the S4-invariant Sylvester triple (D1, D2, D3) the recommended certificate basis (PD-equivalent at 7712 instances, kernel equivalence pending). The surviving selections are now TWO: `Gtz.KFourEdgeDetArgmaxHostsStrictTree` and `Gtz.KFourSomeTreeLiftThreshold`. **STRUCK, AND DO NOT REOPEN: `Gtz.KFourLeverageEdgeHostsStrictTree` IS KERNEL-REFUTED IN THIS TREE** by `Gtz.kFourLeverageEdgeHostsStrictTree_refuted` (Gtz/Design/KFourLeverageRefuter.lean:154), which supplies a fresh chart point `Gtz.leverageRefuterPoint` whose max-leverage edge is 2 and kills all eight spanning trees through edge 2 by exact determinant negativity. Its former recommendation here rested on a purely numerical liveness record (15/15 mandatory + 467/467 corpus + 2900/2900 adversarial, leverage edge 5 at both then-known refuter points) -- the exact profile the campaign's generic-sample law warns about: a directed hunt found the witness the uniform record never reached. Its consumption bridge `Gtz.directionChartIsTieFree_kFour_of_leverageEdgeHosts` and its leverage layer (`Gtz.kFourMassTreeSum` = det M, `Gtz.kFourContractionTreePolynomial`, the trace identity, the pigeonhole) remain landed and reusable, but they now have no live antecedent. CLOSED DOOR: no linear-in-y_S tree-determinant aggregate exists (exact phantom-Y Farkas duals at 14/15 mandatory points and 467/467 corpus under 1500 adversarial weights; any aggregate must engage the toric product relations); det-argmax at the leverage edge (RHO-EDGE, 16/467) and the pair variant (RHO-PAIR, 269/467) are refuted; det-argmax and leverage-argmax do not compose (`wallKFourDetArgmaxHostLift` ledger complete). Sample points: `Gtz.tetrahedronChartPoint` (margin 1/2), the refuter witness, `Gtz.heavyPairRefuterPoint` (still mandatory as the leverage liveness witness and as a Layer-A-uncovered point, though the exchange star now COVERS it), and `Gtz.bandResidualWitnessPoint` (the canonical inhabitant of the surviving band, uncovered by BOTH regions) are the mandatory first tests of any candidate selection or knife-band cell. STAGE-5 UPDATE (2026-08-08): the knife-band CERTIFICATE BASIS is LANDED as a kernel equivalence -- `Gtz.posDef_iff_invariantPencilTriple` (positive definiteness of the symmetric 3x3 IS positivity of the three S4-invariant pencil coefficients D1/D2/D3; eigenvalue-free engine `Gtz.posDef_of_invariantPencilTriple`, exact-verified at 52,064 fresh tree-instances before Lean, firing demonstrated at `Gtz.heavyPairRefuter_gap_zeroOneThree_posDef`), so a Layer-B cell is now THREE FIXED POLYNOMIAL INEQUALITIES at a designated tree -- no frame, no per-tree Sylvester lift -- and closing this class is exactly the sentence "at every chart point some spanning tree has D1 > 0, D2 > 0, D3 > 0". The SELECTION half resisted round five: all four invariant-argmax designations are refuted with exact witnesses (D1/D2/D3-argmax at the leverage edge and D2-argmax globally), NO constant normalized floor exists on the band (best-tree floors span 36 orders of magnitude, minimum 1.10e-39; the binding invariant is D3 at 464/464 band points), and det-positivity does NOT pointwise imply hosting (1,371 exact det-positive-not-PD leverage through-trees; witness {1,2,5} at heavyPair with D3 > 0, D1 < 0). `wallKFourKnifeBandSelection` is hereby DECLARED in its narrowed post-engine form: on the knife band, produce a designated-tree family with moduli-dependent floors making the three invariant inequalities provable cellwise. **THE STAGE-5 ROUTE NAMED HERE IS DEAD.** It read "equivalently prove `Gtz.KFourLeverageEdgeHostsStrictTree` (alive at 6,153 cumulative exact points, zero failures)"; that statement is now kernel-refuted by `Gtz.kFourLeverageEdgeHostsStrictTree_refuted` (Gtz/Design/KFourLeverageRefuter.lean:154) and no designation may be taken from it. The narrowed obligation stands WITHOUT a nominated selector: on the knife band, produce a designated-tree family with moduli-dependent floors making D1, D2, D3 provable cellwise. Ledger = the stage-5 knife campaign record (52,064-instance equivalence verification, four argmax refutations with exact first witnesses, the 464-point bestFloor distribution, the det-half gap census). TRANSPORT: the engine is K4-specific only through the literal reference form L1; D2 = tr(adj(N) * L) is the transportable second-order invariant for the U(3,6) joint corner and the one-line 1/N corner (swap the reference form, recompute the three coefficient polynomials from the same det(N + t*L) expansion).
NOT-REFUTED: no census row targets it. The relaxed-weight refutation needs `0 <= weight`; chart points carry strict positivity. No stress-forcing filter can apply (TrichotomyLedger.lean:505 plus the tetrahedron inhabitant).
-/
axiom obligationKnifeBandRefinedKFour :
    Gtz.KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict

/-- The registered chart residual recovers the exact design-side whitening
family selector.  This is an equivalence, not an additional obligation. -/
theorem obligationKFourFamilySelection : Gtz.KFourFamilySelection :=
  Gtz.kFourFamilySelection_iff_treeStarRefusedMaxHeavyWall.mpr
    obligationKnifeBandRefinedKFour

/-- The fully exposed K4 wall axiom reconstructs the former refined knife band
by spending all seventeen cells, the full sixteen-tree obstruction ledger, the
twelve exact path-kernel couplings, the exhaustive path/star classifier, every
tree's nonzero kernel and outside repair pointer, the four-edge window
dichotomy, the four-pivot sharpening, the star rank-one collapse, the second
pointer theorem, and the automatic chart-heavy law. -/
theorem obligationKnifeBandRefinedKFour_full :
    Gtz.KFourKnifeBandRefinedWeakToStrict :=
  Gtz.kFourKnifeBandRefinedTreeStarRefusedMaxHeavyWall_iff.mp
    obligationKnifeBandRefinedKFour

/-- **Discharged from the sharpened axiom.**  Same name, same statement.  Three
covered families are now spent: Layer A, the exchange star, and all seventeen
all-tree minor certificate cells.  Failure at every tree cell also supplies an
  explicit dual witness, bad row, and polynomial bad-edge budget; every weak
  path also carries a nonzero pulled-back kernel direction.
The residual quantifiers range only
over spanning trees, and the redundant chart-heavy premise is gone.  The old
canonical witness is covered by the unsigned band-tree cell; this theorem does
not claim that the new residual is inhabited. -/
theorem obligationKnifeBandKFour : Gtz.KFourKnifeBandWeakToStrict :=
  Gtz.kFourKnifeBandWeakToStrict_of_refined obligationKnifeBandRefinedKFour_full

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the twenty Layer-A cells are spent as the theorem
`Gtz.kFourAtlas_hasStrictTriple_of_layerAFires`, and
`Gtz.directionChartIsTieFree_kFour_of_knifeBandWeakToStrict` closes the chart
by splitting every point along the Layer-A boundary -- covered points from
the atlas, band points from the residual. -/
theorem obligationChartTieFreeKFour : Gtz.DirectionChartIsTieFree Gtz.kFourDirection :=
  Gtz.directionChartIsTieFree_kFour_of_knifeBandWeakToStrict obligationKnifeBandKFour

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the covering half is the unconditional
`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`, so the class
statement follows from the chart residual by
`Gtz.stressFreeStratumIsTieFree_graphicKFour_of_chart`. -/
theorem obligationTieFreeKFour :
    Gtz.StressFreeStratumIsTieFree
      (Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) :=
  Gtz.stressFreeStratumIsTieFree_graphicKFour_of_chart obligationChartTieFreeKFour

/-- Kernel cross-checks that the sharpened K4 axiom really is DOWNSTREAM of each
selection route: every selection Prop discharges the knife-band residual, so
proving any LIVE one of them still closes the class -- the sharpening gave up no
route.  Off the chain: hypothesis-taking, so none reaches an axiom.

COUNT CORRECTED: these were described here as "three surviving endgame routes".
Only TWO survive.  The first example below takes
`Gtz.KFourLeverageEdgeHostsStrictTree`, whose NEGATION is proved in this tree by
`Gtz.kFourLeverageEdgeHostsStrictTree_refuted`
(Gtz/Design/KFourLeverageRefuter.lean:154).  The example itself stays sound and
useful -- it is hypothesis-taking, and it records that the bridge is real -- but
its hypothesis is unreachable, so that route cannot close the class.  The live
routes are `Gtz.KFourEdgeDetArgmaxHostsStrictTree` and
`Gtz.KFourSomeTreeLiftThreshold`. -/
example (hlev : Gtz.KFourLeverageEdgeHostsStrictTree) :
    Gtz.KFourKnifeBandWeakToStrict :=
  fun point _ hweak =>
    Gtz.directionChartIsTieFree_kFour_of_leverageEdgeHosts hlev point hweak

example (hhost : Gtz.KFourEdgeDetArgmaxHostsStrictTree) :
    Gtz.KFourKnifeBandWeakToStrict :=
  fun point _ hweak =>
    Gtz.directionChartIsTieFree_kFour_of_edgeDetArgmaxHosts hhost point hweak

example (hlift : Gtz.KFourSomeTreeLiftThreshold) :
    Gtz.KFourKnifeBandWeakToStrict :=
  fun point _ hweak =>
    Gtz.directionChartIsTieFree_kFour_of_someTreeLiftThreshold hlift point hweak

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
axiom obligationThresholdCellHingeRankFourAndUp :
    ∀ rank : ℕ, 4 ≤ rank →
      Gtz.GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : Gtz.WeightedDesign (rank * (rank + 1) / 2) rank,
          Gtz.IsTie design → Gtz.HasParallelPair design

/-- The `(6,3)` hinge assembled from the trichotomy and the five class
obligations -- the same assembly `Skeleton.RankThree` performs, available here
so the threshold-cell hinge can shed its rank-three instance. -/
theorem hingeHoldsSixThree_ofClassObligations : Gtz.HingeHoldsAtSize 6 3 :=
  Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge
    Gtz.twoPoleStratumSelection_six_unconditional
    (Gtz.balancedStratumCapstone_of_balancedStratumSelection
      Gtz.balancedStratumSelection_six_holds)
    obligationStressFreeHingeSixThree

/-- **Split, not weakened.**  Same name, same statement as the axiom it
replaces.  The rank-three instance of the threshold-cell hinge IS the `(6,3)`
hinge, whose stress-free arm is exactly the five class obligations -- so
assuming it as part of a general-rank axiom assumed the whole rank-three
frontier a second time, in a strictly stronger wrapper.  After the split the
axiom exists only at rank four and up, and rank three is DISCHARGED from the
class obligations through the trichotomy assembly above.  The general-rank
capstone therefore now pays for rank three with exactly the rank-three
currency, and no registry axiom subsumes another. -/
theorem obligationThresholdCellHinge :
    ∀ rank : ℕ, 3 ≤ rank →
      Gtz.GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : Gtz.WeightedDesign (rank * (rank + 1) / 2) rank,
          Gtz.IsTie design → Gtz.HasParallelPair design := by
  intro rank hrankAtLeastThree
  rcases Nat.lt_or_ge rank 4 with hrankBelowFour | hrankAtLeastFour
  · have hrankIsThree : rank = 3 := by omega
    subst hrankIsThree
    intro _hpredecessorCell design htie
    exact hingeHoldsSixThree_ofClassObligations design htie
  · exact obligationThresholdCellHingeRankFourAndUp rank hrankAtLeastFour

/-!
### SPLIT RECORD: `obligationSharpWindowAnchorReach`, split by rank

Retired as an axiom and re-proved below from `...RankThree` and
`...RankFourAndUp`.  Its original five fields are kept verbatim here because
they are the provenance of the two finer statements; the live fields are on
those.

STATUS: partial proof, and a THEOREM at rank three. At rank three the sharp window is the single cell size six, discharged by `Gtz.icosaDesign` with `Gtz.icosaDesign_hasStrictlyDominatingSubset` and `Gtz.parallelFreeReachesAnchor_six_three`. The anchor's STRICT half is free at every rank by positive rescaling, `Gtz.UniformPositionBridge.exists_strictAnchor_of_weakDominator`.
CONSUMERS: the general-rank capstone in `Skeleton.GeneralRank`, feeding every rung of `Gtz.UniformPositionBridge.gtzWeighted_succ_of_hinge_of_reach`.
WHY OPEN: the only `Gtz.ParallelFreeReachesAnchor` instance in the entire tree is the rank-three one. Above rank three what is missing is per-cell connectivity of the parallel-free locus, plus an assembly step that nothing in the tree performs: `Gtz.UniformPositionBridge.DiagonalTailAtCell` has ZERO producers AND ZERO consumers, so even proving it would leave it unwired. [SUPERSEDED 2026-08-08: it now has a PRODUCER, `Gtz.UniformPositionBridge.diagonalTailAtCell_of_two_le`, sharp at `extra = 1` via `not_diagonalTailAtCell_one`; consumers are still zero, so the unwired half of the sentence stands and the live field on `...RankFourAndUp` states the current position.]
ATTACK: `Gtz.UniformPositionBridge.windowAnchorReachFree_of_weakWitness` plus `exists_strictAnchor_of_weakDominator` already reduce this to a weak parallel-free dominator at each cell together with per-cell connectivity. Two concrete gaps remain: wire `DiagonalTailAtCell` and `Gtz.UniformPositionBridge.coreTailBookkeeping_feasible` into that weak witness (the Fin reindexing and the Parseval sum are unwritten), and close the tail-block diagonality matrix identity. [SUPERSEDED 2026-08-08: the diagonality identity is PROVED at general rank and general slot count (`Gtz.UniformPositionBridge.sum_tail_atomMatrix`, AnchorAssembly.lean:277-283, which records the nine-way split as ONCE blocked and now closed by the single cancellation). The genuinely unwritten step is the reindex-and-Parseval assembly the same file names at :402-413.]
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
STATUS: CLOSED. This is no longer an axiom. `Gtz.GeneralRankReach.sharpWindowAnchorReachRankFourAndUp` (Gtz/Uniform/SpectralWhitening.lean) carries this exact type, and its axiom pins are `[propext, Classical.choice, Quot.sound]`.
CONSUMERS: `obligationSharpWindowAnchorReach`, which stays a theorem, thus no capstone changed.
WHY CLOSED: the two residual Props of the reach assembly became theorems. `Gtz.GeneralRankReach.sharpWindowParallelFreeConnectivity_of_three_le` supplies the per-cell connectivity from the moment-hub schedule of Gtz/Uniform/MomentHubSchedule.lean, and `Gtz.GeneralRankReach.whiteningTransferAtRank_general` supplies the whitening from the continuous functional calculus, with no hypothesis.
ATTACK: none is necessary.
NOT-REFUTED: the rank-two refutations are not instances of this statement, because the sharp window is empty at rank two.
-/
theorem obligationSharpWindowAnchorReachRankFourAndUp :
    ∀ rank : ℕ, 4 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        ∃ anchor : Gtz.WeightedDesign size rank,
          Gtz.HasStrictlyDominatingSubset anchor
            ∧ Gtz.ParallelFreeReachesAnchor size rank anchor :=
  Gtz.GeneralRankReach.sharpWindowAnchorReachRankFourAndUp

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
  [`Skeleton.obligationBaseTripleTightUThreeSix,
   `Skeleton.obligationHeavyWeakToStrictOneLine,
   `Skeleton.obligationHeavyWeakToStrictTwoMeetingLines,
   `Skeleton.obligationChartTieFreeThreeLinesFundamentalDomain,
   `Skeleton.obligationKnifeBandRefinedKFour,
   `Skeleton.obligationSubThresholdBandHinge,
   `Skeleton.obligationThresholdCellHingeRankFourAndUp]

end Skeleton
