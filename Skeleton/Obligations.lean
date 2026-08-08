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

  - `obligationWeakToStrictUThreeSix` = `Gtz.LineFreeOffConicWeakToStrict`
    (the design-level weak-to-strict upgrade, `PosSemidef` antecedent kept);
  - `obligationReducedCoverOneLine` and
    `obligationReducedCoverTwoMeetingLines` =
    `Gtz.PatternReducedCoverProperty` at the two chartless patterns -- some
    card-3 subset and unit normal satisfy BOTH hypotheses of the landed
    uniform Schur producer, the campaign's RCP verbatim;
  - `obligationChartTieFreeThreeLines` = `Gtz.DirectionChartIsTieFree` at
    every admissible slide;
  - `obligationKnifeBandKFour` = `Gtz.KFourKnifeBandWeakToStrict`, strictness
    demanded ONLY off the named Layer-A region `Gtz.KFourLayerACellFires`, so
    the twenty proved atlas cells are SPENT, not re-assumed.

  Everything above each axiom survives as a THEOREM -- the old class
  statements `obligationTieFree*`, the intermediate
  `obligationStratumTieFree*` and `obligationChartTieFreeKFour`, and their
  assembly `obligationStressFreeHingeSixThree` -- so no downstream capstone
  changed.  Each step is a refinement in the sufficient direction (the finer
  Prop implies the coarser one by a kernel theorem; no converse is claimed),
  which is what makes the printed frontier the true attack surface rather
  than a convenient restatement.
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
STATUS: open -- THE EXACT U(3,6) RESIDUAL: `Gtz.LineFreeOffConicWeakToStrict`, the design-level weak-to-strict upgrade on the line-free off-conic stratum with the `PosSemidef` antecedent KEPT (load-bearing: the fiber margin infimum over masses and weights is zero at every direction tuple, so the antecedent-free sibling is out of reach). Everything between this Prop and the class statement is a theorem: `Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict` discharges `obligationTieFreeUThreeSix` below verbatim, converting stress-freeness to off-conic through `Gtz.stratumStressHasFullSupport_lineFree` (TrichotomyLedger.lean:524; the single MIXED class -- stress-free here means OFF-CONIC, and that excluded conic sublocus is exactly where the margin degenerates; the (4,3) tetrahedron and (5,3) diamond tie shadows live there).
CONSUMERS: `obligationTieFreeUThreeSix` (now a theorem), hence `obligationStressFreeHingeSixThree` and the rank-three capstone.
WHY OPEN: on a line-free stratum every distinct triple is a basis, so no pruning rule bites, and the deflation rule is provably inert (`Gtz.not_blindLabel_lineFree`, Gtz/Design/StratumTieFreeClasses.lean). The tree records that attacking this class FIRST is backwards (StratumTieFreeClasses.lean:207-215); it is sequenced LAST, after the four rigid classes.
ATTACK: start from the conic characterization, never from a selector. The formulation layer is now IN KERNEL (Gtz/Design/LineFreeConicBridge.lean): `Gtz.LineFreeOffConicWeakToStrict` (antecedent KEPT -- load-bearing here) reduces this obligation verbatim via `Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict`; the two-family assembly `Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies` is proved; the mass-reading clearance functionals (`Gtz.wallClearanceOf`, positive exactly on the open stratum -- clearance MUST read masses, the fiber margin infimum is zero at every direction tuple via mass collapse) are defined; and the exact rational icosa approximant (`Gtz.icosaApproximantDirection`: kernel-proved line-free, stress-free, off-conic, with `Gtz.icosaApproximantChartPoint_hasStrictTriple`) is the interior family's seed. STAGE-3 UPDATE (2026-08-08): the interior family is fully interfaced -- `Gtz.ClearanceBoundedInteriorFloor` (weak antecedent kept) reduces through `Gtz.interiorFamilyMarginFloor_of_clearanceBounded` into the assembly, the orbit split is spent once in kernel (`Gtz.clearanceBoundedInteriorFloor_of_baseTriple` pins the weak triple at {0,1,2} via the proved relabelling-invariance suite), and the icosa seed is quantitative (`Gtz.icosaApproximant_gap_floorThree`, moment matrix tau * identity). The collar is split per wall (`Gtz.boundaryCollarExcludesTies_wallClearance_of_perWall`); the attained mass wall provably lies ON the conic wall (`Gtz.not_hasNoCommonQuadric_of_atom_eq_zero`), the stress walk is quantified with explicit off-wall residual, and dust-ray witnesses cover both named surviving ties (`Gtz.tetraCorner_gap_posDef_on_dustRay` on (0,1/4], `Gtz.diamondCorner_gap_posDef_on_dustRay` on (0,1/16]). STAGE-4 UPDATE (2026-08-08): the instance at the scan-proposed constants (1/16, 1/4) is REFUTED IN KERNEL -- `Gtz.baseTripleClearanceBoundedFloor_sixteenth_quarter_refuted` and `Gtz.clearanceBoundedInteriorFloor_sixteenth_quarter_refuted` (exact rational Parseval refuter, Cayley Stiefel rows over square weights, line-free, off-conic via the first exact 6x6 Veronese determinant in the tree, clearance above 1/16, all twenty triples defeated at the 1/4 floor); the in-region margin record ladder (0.237 -> 0.1724 -> 0.1145 under heavy weight tilts) has not stabilized at any positive floor. STAGE-5 UPDATE (2026-08-08): the adversarial minimax DECIDED the interior question over `Gtz.wallClearanceOf` negatively, in kernel -- NO constant pair with cf <= 3/8 and mf >= 1/16 exists (`Gtz.baseTripleClearanceBoundedFloor_rectangle_refuted`, `Gtz.clearanceBoundedInteriorFloor_rectangle_refuted`) and NO Monotone clearance-graded floor reaching 1/16 by clearance 3/8 exists (`Gtz.interiorFamilyMarginFloor_monotoneGraded_refuted`); the escape is the dust-weight channel (raw weights below ~1/128 mask a jointly degenerating frame from every weight-compensated clearance leg; margin infimum 0 in EVERY wallClearanceOf band, exact witness with best margin in [7.619e-5, 7.620e-5] at exact wall clearance >= 1/4; a raw-weight floor restores the margin linearly, measured stall ~2.2 x weightFloor). Truth of tie-freeness is never threatened -- the escape runs along the open weight-simplex boundary where no design exists. Remaining: RE-FOUND the interior family on a weight-aware clearance functional (e.g. min of wallClearanceOf and a scaled minimum raw weight; the two-family assembly `Gtz.lineFreeOffConicWeakToStrict_of_twoFamilies` is already parametric in the functional, so this costs interfaces, not plumbing), with mandatory adversarial re-validation at the repaired region before any instance is proposed; PLUS the collar at the repaired region -- which now needs a dust-WEIGHT witness family (the landed tetra/diamond dust-MASS rays do not cover it; required witness floors are linear in the raw weight, the same margin ~ 2 x dustWeight law as the corner cascade -- the universal boundary law of this stratum). The joint three-coordinate corner of the collar stays WALLED as `wallUThreeSixJointCornerCollar` after three documented rounds (no uniform-margin mechanism exists at any positive floor; the margin dies linearly only along the full offset x dust-weight x dust-ratio cascade; the (5,3) exclusions are branch-(ii) objects needing a compactification bridge before they bite here).
NOT-REFUTED: no census row targets the class statement. What IS refuted are methods: every finite pure-triple or orbit selector, every constant, label-free or continuous selector, matroid exchange, bounded-radius search, weight-uniform threshold certificates (margin infimum zero), and Putinar/Schmuedgen. A stress-forcing pattern filter cannot apply here: it would assert every line-free design lies on a conic.
-/
axiom obligationWeakToStrictUThreeSix : Gtz.LineFreeOffConicWeakToStrict

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the class statement follows from the exact residual
`obligationWeakToStrictUThreeSix` by the tree's own reduction
`Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict`. -/
theorem obligationTieFreeUThreeSix :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern []) :=
  Gtz.stressFreeStratumIsTieFree_lineFree_of_weakToStrict obligationWeakToStrictUThreeSix

/--
STATUS: open -- THE EXACT ONE-LINE RESIDUAL: `Gtz.PatternReducedCoverProperty` at the one-line pattern. Every design of the stratum admits a card-3 subset and a unit normal satisfying BOTH hypotheses of the landed uniform Schur producer (strict normal surplus, strict plane cover) -- the campaign's RCP, verbatim. Everything between this Prop and the class statement is a theorem: `Gtz.stratumIsTieFree_of_reducedCoverProperty` closes the stratum by one producer application against the tie's own refusal, and the relabel bridge lifts it to the class. The property is UNCONDITIONED on ties deliberately: under a tie no producer pair can exist, so a tie-conditioned sibling could only be proved via tie-freeness itself. The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_oneThreePointLine`, Gtz/Reduction/TrichotomyLedger.lean:485), so no stress-freeness hypothesis survives anywhere in the chain, and the surplus half is automatic at the free triple against the line normal (`Gtz.oneLine_exists_freeAtom_overcovers_normal`) -- the genuinely open half is the plane cover.
CONSUMERS: `obligationStratumTieFreeOneLine` (now a theorem), hence `obligationTieFreeOneLine`, `obligationStressFreeHingeSixThree`, and the rank-three capstone.
WHY OPEN: of the six producers of `Gtz.StressFreeStratumIsTieFree` in the tree, three are chart instances at other patterns, the plane-pair filter is provably anti-aligned (the residual list IS the not-plane-pair-covered list, Gtz/Design/StressFreeMatroidStratification.lean:303), and the two generic chart forms need a chart nobody has built for this pattern.
ATTACK: build the chart following the shipped precedent -- Gtz/Design/RigidityBridge.lean:1-60 (PGL(3) simply transitive on four general lines, made rational, plus the per-atom scaling group) and the structure of `Gtz.directionChartCoversPrimitiveStratum_kFourDirection`. The pattern pins only three atoms projectively, so the chart carries genuine moduli and the analytic half is a parametric family. BUILD THIS CLASS FIRST of the two chartless ones: its boundary is diamond-FREE, so uniform-in-parameter arguments should survive. Corpora triage complete (2026-08-07): /tmp/gtz-p38/rigidity2 and /tmp/gtz-p35/zerochart are empty/dead; the w2 lane targeted the K4 tube route, nothing shortcuts the chart build. Direct-route levers: a tie's weak dominator avoids the line (`Gtz.not_dominates_of_atomBracket_eq_zero`), hence is one of the NINETEEN basis triples; the line's common orthogonal is the lever -- Parseval transfers the whole normal direction to the three free atoms, and positivity of the line weights makes the free triple exceed the identity STRICTLY along the normal, a strict seed present on every design of the stratum. Exact-rational non-vacuity sample with two strictly dominating triples now IN KERNEL: `Gtz.oneLineSampleDesign` (Gtz/Design/LineClassObstructions.lean) with `Gtz.oneLineSampleDesign_not_isTie`; the census ladder G1-G3/O1-O7 is landed in the same module (the relabel bridge `Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` closes this obligation from any identity-labelled tie-freeness proof). STAGE-3 UPDATE (2026-08-08): the producer layer is LANDED -- the pointwise normal seed `Gtz.exists_complementAtom_overcovers_normal` (one complement atom alone beats the squared normal), the uniform Schur producer `Gtz.posDef_of_normalSurplus_planeCover` (normal surplus + plane cover => PosDef gap, one completed square, direction-generic), and the tie-side `Gtz.isTie_yields_planeCover_failure`. The class residual is ONE statement, RCP: some card-3 subset satisfies both producer hypotheses. Constraints on any RCP proof (exact witnesses in the campaign record): the argmax-normal-conductance selection is refuted at the matched-normal knife, and NO uniform margin floor exists on the stratum (an explicit rational family collapses the margin like 1/N at the line-starved normal-matched weight corner) -- the proof must be sign-only; recommended attack is rank-2 slack in the plane with per-atom penalty deflations, worked at that corner first. STAGE-4 UPDATE (2026-08-08): the corner reduces to a dichotomy on min_i eps_i vs 1/2; leg B (all eps in the closed half [0, 1/2], including the E = I/2 knife) is PEN-PROVED via the Half-Plane Lemma (Bhatia-Davis range bound x_min x_max <= -V with a matroid equality-kill; campaign record, stage-4 rcp lane -- NOT yet in kernel); leg C is reduced with zero slack (gamma-elimination + von Neumann duality) to RCP-C1: all eps_i > 1/2 implies an admissible vertex dual y with VERT_k below mu_k (401 strict exact confirmations, zero violations, max cValue -23/799); plus the RCP-LIFT seam (corner-to-interior: A-triples are corner-redundant but NOT interior-redundant, 9/360). CLOSED DOOR: b-averaged and ALL line-data-only C-engines are provably insufficient -- they die on the isotropic band E = cI (exact witness: lines (1,0), (4,7), (-4,7), masses (363/980, 11/1960, 11/1960), c = 11/20; band (1/2, 4/7]); any C-certificate must read shadow data.
NOT-REFUTED: no census row targets it. The stress-forcing filter door is CLOSED, not just unused: the pattern forces stress-freeNESS uniformly (`Gtz.stratumIsStressFree_oneThreePointLine`, TrichotomyLedger.lean:485), so a filter asserting a forced nonzero stress is refutable at any design of the stratum, and the residual list is already exactly the not-plane-pair-covered list (StressFreeMatroidStratification.lean:303). Only direct tie obstructions remain admissible here.
-/
axiom obligationReducedCoverOneLine :
    Gtz.PatternReducedCoverProperty (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2]])

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: `Gtz.stratumIsTieFree_of_reducedCoverProperty` closes the
stratum from the reduced cover property by one application of the uniform
Schur producer `Gtz.posDef_of_normalSurplus_planeCover` against the tie's
second component. -/
theorem obligationStratumTieFreeOneLine :
    Gtz.StratumIsTieFree (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  Gtz.stratumIsTieFree_of_reducedCoverProperty _ obligationReducedCoverOneLine

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
STATUS: open -- THE EXACT TWO-MEETING-LINES RESIDUAL: `Gtz.PatternReducedCoverProperty` at the two-meeting-lines pattern, the SAME pattern-generic Prop as the one-line residual because the uniform Schur producer is direction-generic and consumes this class verbatim. Everything between this Prop and the class statement is a theorem (`Gtz.stratumIsTieFree_of_reducedCoverProperty` + the relabel bridge). Refinement in the sufficient direction only: the class statement does not require RCP, and this class is diamond-CARRYING, so any candidate proof must survive the weight-zero diamond boundary where margins die linearly -- sign-only, one strict seed per line (a tie's weak dominator avoids BOTH lines, the two normals are provably non-parallel). The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_twoMeetingLines`, Gtz/Reduction/TrichotomyLedger.lean:491).
CONSUMERS: `obligationStratumTieFreeTwoMeetingLines` (now a theorem), hence `obligationTieFreeTwoMeetingLines`, `obligationStressFreeHingeSixThree`, and the rank-three capstone.
WHY OPEN: same producer situation as the one-line class -- no chart exists for this pattern and the plane-pair filter is structurally inapplicable. Two concurrent lines are the closest residual pattern to the plane-pair boundary: the two line planes cover five of the six atoms, and it is exactly the sixth that escapes the escape law.
ATTACK: same chart-building precedent as the one-line class (RigidityBridge.lean:1-60 plus the :796 covering structure); the pattern pins five atoms up to the two line moduli, so the chart is SMALLER than the one-line chart -- but build it SECOND: this class is diamond-CARRYING (`Gtz.diamondCarryingResidualFamiliesSix`, StressFreeMatroidStratification.lean:580), a positive-dimensional (5,3) tie family through `Gtz.diamondDesign` sits on its weight-zero boundary, margins die linearly there and no uniform-in-weights certificate exists; the boundary leg must route the diamond shadow through the proved five-label exclusions, with the open-atom lift identity as the skeleton. Direct-route levers: a tie's weak dominator avoids BOTH lines, leaving EIGHTEEN basis triples; the two normals are provably non-parallel and the shared atom is pinned projectively to the plane intersection -- the class's rigidity kernel; Parseval gives one strict seed per line.
NOT-REFUTED: no census row targets it. The stress-forcing filter door is CLOSED, not just unused: the pattern forces stress-freeNESS uniformly (`Gtz.stratumIsStressFree_twoMeetingLines`, TrichotomyLedger.lean:491), the opposite polarity to any stress-forcing mechanism, and the plane-pair law already consumed every coverable class (StressFreeMatroidStratification.lean:303). Only direct tie obstructions remain admissible here.
-/
axiom obligationReducedCoverTwoMeetingLines :
    Gtz.PatternReducedCoverProperty
      (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the same pattern-generic
`Gtz.stratumIsTieFree_of_reducedCoverProperty` closes this stratum too. -/
theorem obligationStratumTieFreeTwoMeetingLines :
    Gtz.StratumIsTieFree (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  Gtz.stratumIsTieFree_of_reducedCoverProperty _ obligationReducedCoverTwoMeetingLines

/-- **Discharged from the sharpened axiom.**  Same name, same statement as the
axiom it replaces: the relabel bridge
`Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` closes the class statement
from identity-labelled tie-freeness at this pattern too. -/
theorem obligationTieFreeTwoMeetingLines :
    Gtz.StressFreeStratumIsTieFree (Gtz.lineFamilyPattern [[0, 1, 2], [0, 3, 4]]) :=
  Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree _ obligationStratumTieFreeTwoMeetingLines

/--
STATUS: chart-covered, analytic half open. The covering half is the unconditional `Gtz.parameterizedChartCovers_threeLinesDirection` (Gtz/Design/RigidityBridge.lean:1098) with consumer `Gtz.stressFreeStratumIsTieFree_threeLines_of_chart` (:1135); the stratum is uniformly stress-free (`Gtz.stratumIsStressFree_threeLines`, Gtz/Reduction/TrichotomyLedger.lean:497). What is open is `Gtz.DirectionChartIsTieFree (Gtz.threeLinesDirection slide)` at every admissible slide (`Gtz.IsAdmissibleThreeLinesParameter`: slide != 0 and slide != -1, RigidityBridge.lean:883) -- twelve numbers, one more than the K4 chart.
CONSUMERS: `obligationStressFreeHingeSixThree` (the split parent, now a theorem), hence the rank-three capstone.
WHY OPEN: the sole producer of `Gtz.DirectionChartIsTieFree` routes through `Gtz.DirectionChartHasStrictTriple`, which is FALSE at a degenerate direction; no direct certificate exists at any slide.
ATTACK: inherit whatever certificate format closes the K4 chart, PARAMETRICALLY in the slide from the start; partition the admissible line into finitely many intervals with exact algebraic endpoints. The two excluded slides are the degenerations onto a collapsed atom (a parallel pair, outside every stress-free stratum) or the M(K4) pattern (the K4 class); they are not gaps.
NOT-REFUTED: no census row targets it. The strict-triple refutation kills only that producer's premise at a degenerate direction, not this statement. No stress-forcing filter can apply (TrichotomyLedger.lean:497).
-/
axiom obligationChartTieFreeThreeLines :
    ∀ slide : ℝ, Gtz.IsAdmissibleThreeLinesParameter slide →
      Gtz.DirectionChartIsTieFree (Gtz.threeLinesDirection slide)

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
STATUS: the most rigid class; covering half PROVED (`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`, Gtz/Design/RigidityBridge.lean:796), direct class consumer `Gtz.stressFreeStratumIsTieFree_graphicKFour_of_chart` (:834). The stratum is uniformly stress-free (`Gtz.stratumIsStressFree_graphicKFour`, Gtz/Reduction/TrichotomyLedger.lean:505). NOT VACUOUS: the stage-four audit's coordinate-diagonal design (the regular tetrahedron's six edge directions) realizes exactly this pattern. Open: `Gtz.KFourKnifeBandWeakToStrict` -- strictness demanded ONLY at weakly dominated chart points where no Layer-A cell fires (the twenty landed cells, named `Gtz.KFourLayerACellFires`, are spent as the theorem `Gtz.kFourAtlas_hasStrictTriple_of_layerAFires`; the boundary split `Gtz.directionChartIsTieFree_kFour_of_knifeBandWeakToStrict` closes the chart). The uncovered set is the stage-four knife band: 464 exact leftover points, 405 knife-edge, canonical inhabitant `Gtz.heavyPairRefuterPoint` -- the mandatory first test of any candidate proof. Eleven positive reals against six FIXED rational chart vectors, twenty triples, no design, no whitener, no square root in the statement.
CONSUMERS: `obligationChartTieFreeKFour` (now a theorem), hence `obligationTieFreeKFour`, `obligationStressFreeHingeSixThree`, and the rank-three capstone.
WHY OPEN: the sole producer of `Gtz.DirectionChartIsTieFree` is `Gtz.directionChartIsTieFree_of_hasStrictTriple` (:176), whose premise `Gtz.DirectionChartHasStrictTriple` is kernel-FALSE at a degenerate DIRECTION (a non-spanning family -- no refutation exists at any valid `kFourDirection` chart point, and ~19000 exact-rational adjudications found none); the antecedent-free form is still never landed as a named global. The class-level sibling `stressFreeStratumIsTieFree_graphicKFour_of_strictTriple` (:841) stays forbidden as a route.
ATTACK: DECIDED (spike, 2026-08-07): the DIRECT road; collar weld rejected (three nonexistent layers). LANDED SINCE (Gtz/Design/KFourChartClosure.lean, 2026-08-08): the whole contraction-descent brick set -- the rank-two Foster engine, `Gtz.rankTwoSlackLemma` (Lemma A), kappa-free `Gtz.sylvesterLift`, the twelve entrywise gap matrices, the dependent-triple PSD exclusion, `Gtz.kFourContractionHasWinner` (at EVERY chart point some tree through edge 5 has PD contracted block, no maximality needed), the det normal forms, and the consumption bridge -- PLUS the kernel REFUTATION of the max-conductance selection: `Gtz.kFourMaxEdgeHostsStrictTree_refuted` and `Gtz.kFourMaxEdgeDetPigeonhole_refuted` at `Gtz.maxEdgeRefuterPoint` (strict argmax edge 3, dominant masses on the dependent triangle {0,3,4}), while the chart obligation stays INTACT there (`Gtz.maxEdgeRefuterPoint_hasStrictTriple`, {0,1,4} dominates strictly). STAGE-3 UPDATE (2026-08-08): the mass-reading direction is ALSO kernel-refuted -- `Gtz.kFourDominantMassPairHostsStrictTree_refuted` at the dual witness `Gtz.heavyPairRefuterPoint` (same weights, triangle-closer mass 18 past the pair's series threshold 120/7) and `Gtz.kFourMaxAlphaEdgeHostsStrictTree_refuted` at the landed witness; with the max-conductance refutation these close every per-label scalar ordering, and per-class representative rules die at tetrahedron shells (exact witnesses, campaign record). STAGE-4 UPDATE (2026-08-08): the certificate atlas's Layer A is COMPLETE -- all TWENTY cells (four star + sixteen harmonic, entrywise gap lemmas for every spanning tree, engine `Gtz.harmonicSplitQuadraticForm_pos`) with total dispatch `Gtz.kFourAtlas_hasStrictTriple_of_anyCell`; Layer A is NOT a total atlas: `Gtz.heavyPairRefuterPoint` fires no Layer-A cell (its PD trees are exactly the six through edge 3), and the fresh-seed census leaves a 464-point exact leftover corpus (405 knife-edge; campaign record, stage-4 harm lane) -- the residual is the knife band ALONE, with the S4-invariant Sylvester triple (D1, D2, D3) the recommended certificate basis (PD-equivalent at 7712 instances, kernel equivalence pending). The surviving selections are now THREE, sharpest first, all with LANDED consumption bridges: `Gtz.KFourLeverageEdgeHostsStrictTree` (the max-(m_c Q_c / w_c) leverage edge hosts a strictly dominating tree; alive at 15/15 mandatory + 467/467 corpus + 2900/2900 adversarial, kernel-live at both refuter points with leverage edge 5; bridge `Gtz.directionChartIsTieFree_kFour_of_leverageEdgeHosts`, leverage layer `Gtz.kFourMassTreeSum` = det M, `Gtz.kFourContractionTreePolynomial`, trace identity, pigeonhole), `Gtz.KFourEdgeDetArgmaxHostsStrictTree`, `Gtz.KFourSomeTreeLiftThreshold`. CLOSED DOOR: no linear-in-y_S tree-determinant aggregate exists (exact phantom-Y Farkas duals at 14/15 mandatory points and 467/467 corpus under 1500 adversarial weights; any aggregate must engage the toric product relations); det-argmax at the leverage edge (RHO-EDGE, 16/467) and the pair variant (RHO-PAIR, 269/467) are refuted; det-argmax and leverage-argmax do not compose (`wallKFourDetArgmaxHostLift` ledger complete). Sample points: `Gtz.tetrahedronChartPoint` (margin 1/2), the refuter witness, and `Gtz.heavyPairRefuterPoint` (doubly mandatory: the only Layer-A-uncovered point AND the leverage liveness witness) are the mandatory first tests of any candidate selection or knife-band cell. STAGE-5 UPDATE (2026-08-08): the knife-band CERTIFICATE BASIS is LANDED as a kernel equivalence -- `Gtz.posDef_iff_invariantPencilTriple` (positive definiteness of the symmetric 3x3 IS positivity of the three S4-invariant pencil coefficients D1/D2/D3; eigenvalue-free engine `Gtz.posDef_of_invariantPencilTriple`, exact-verified at 52,064 fresh tree-instances before Lean, firing demonstrated at `Gtz.heavyPairRefuter_gap_zeroOneThree_posDef`), so a Layer-B cell is now THREE FIXED POLYNOMIAL INEQUALITIES at a designated tree -- no frame, no per-tree Sylvester lift -- and closing this class is exactly the sentence "at every chart point some spanning tree has D1 > 0, D2 > 0, D3 > 0". The SELECTION half resisted round five: all four invariant-argmax designations are refuted with exact witnesses (D1/D2/D3-argmax at the leverage edge and D2-argmax globally), NO constant normalized floor exists on the band (best-tree floors span 36 orders of magnitude, minimum 1.10e-39; the binding invariant is D3 at 464/464 band points), and det-positivity does NOT pointwise imply hosting (1,371 exact det-positive-not-PD leverage through-trees; witness {1,2,5} at heavyPair with D3 > 0, D1 < 0). `wallKFourKnifeBandSelection` is hereby DECLARED in its narrowed post-engine form: on the knife band, produce a designated-tree family with moduli-dependent floors making the three invariant inequalities provable cellwise -- equivalently prove `Gtz.KFourLeverageEdgeHostsStrictTree` (alive at 6,153 cumulative exact points, zero failures; its hosting tree supplies the designation, its bridge is landed, and it is now reducible to a det floor plus two cheap invariant checks); ledger = the stage-5 knife campaign record (52,064-instance equivalence verification, four argmax refutations with exact first witnesses, the 464-point bestFloor distribution, the det-half gap census). TRANSPORT: the engine is K4-specific only through the literal reference form L1; D2 = tr(adj(N) * L) is the transportable second-order invariant for the U(3,6) joint corner and the one-line 1/N corner (swap the reference form, recompute the three coefficient polynomials from the same det(N + t*L) expansion).
NOT-REFUTED: no census row targets it. The relaxed-weight refutation needs `0 <= weight`; chart points carry strict positivity. No stress-forcing filter can apply (TrichotomyLedger.lean:505 plus the tetrahedron inhabitant).
-/
axiom obligationKnifeBandKFour : Gtz.KFourKnifeBandWeakToStrict

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

/-- Kernel cross-checks that the sharpened K4 axiom really is DOWNSTREAM of all
three surviving endgame routes: each selection Prop discharges the knife-band
residual, so proving any one of them still closes the class -- the sharpening
gave up no route.  Off the chain: hypothesis-taking, so none reaches an
axiom. -/
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
  [`Skeleton.obligationWeakToStrictUThreeSix,
   `Skeleton.obligationReducedCoverOneLine,
   `Skeleton.obligationReducedCoverTwoMeetingLines,
   `Skeleton.obligationChartTieFreeThreeLines,
   `Skeleton.obligationKnifeBandKFour,
   `Skeleton.obligationSubThresholdBandHinge,
   `Skeleton.obligationThresholdCellHingeRankFourAndUp,
   `Skeleton.obligationSharpWindowAnchorReachRankFourAndUp]

end Skeleton
