/-
# GTZ -- the Goreinov-Tyrtyshnikov-Zamarashkin problem, formalized

Root module: imports the whole development, layer by layer.  The layers below
are a strict hierarchy -- every import points downward, never up -- so the
directory an file sits in is exactly its depth in the dependency order.  See
README.md for the problem, the architecture, and the status ledger.
-/

-- Core: the problem: designs, domination, the two statements
import Gtz.Core.Basic
import Gtz.Core.Sanity

-- LinAlg: design-free matrix kit: rank-one Schur, PSD transfer, 2x2, completion
import Gtz.LinAlg.BernsteinPositivity
import Gtz.LinAlg.Completion
import Gtz.LinAlg.CongruenceRobustness
import Gtz.LinAlg.EigenvalueSubdifferential
import Gtz.LinAlg.ElliptopeInterval
import Gtz.LinAlg.GordanAlternative
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ResolventPerturbation
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.SignForcing
import Gtz.LinAlg.TwoByTwo

-- Design: WeightedDesign facts: trace identity, leverage, margins, compactness
import Gtz.Design.BhatiaDavis
import Gtz.Design.CapSlack
import Gtz.Design.ClosureObtuse
import Gtz.Design.CollaredCompact
import Gtz.Design.DeflationCertificate
import Gtz.Design.DiamondPrimitive
import Gtz.Design.DominationGates
import Gtz.Design.DowndateInterlacing
import Gtz.Design.FrameConservation
import Gtz.Design.LeverageBound
import Gtz.Design.MarginTransfer
import Gtz.Design.RhoNormalForm
import Gtz.Design.SignSelectedAggregate
import Gtz.Design.StressCertificate
import Gtz.Design.SymmetryReduction
import Gtz.Design.TraceIdentity
import Gtz.Design.WhiteningDistortion

-- Reduction: the ladder: crystallization, Naimark duality, deflation, the lifting lemma
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.ChargeSelection
import Gtz.Reduction.Compression
import Gtz.Reduction.Crystallization
import Gtz.Reduction.Deflation
import Gtz.Reduction.DescentLadder
import Gtz.Reduction.LiftingLemma
import Gtz.Reduction.Naimark
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.RankTwo
import Gtz.Reduction.RatCertificate
import Gtz.Reduction.CertificateBall
import Gtz.Reduction.RatCertificateInstance
import Gtz.Reduction.BranchTwoRational
import Gtz.Reduction.BranchTwoMinimal
import Gtz.Reduction.BranchTwoCompleteness
import Gtz.Reduction.PsdCongruenceConsumer
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions

-- Corner: the exact (k+1)-cycle corner and its cap dictionary
import Gtz.Corner.AggregatePushoff
import Gtz.Corner.CapCriterion
import Gtz.Corner.CapDictionary
import Gtz.Corner.CornerFiber
import Gtz.Corner.CornerPerturbation
import Gtz.Corner.CornerResolvent
import Gtz.Corner.CoveringMargin
import Gtz.Corner.IdempotentSplitting
import Gtz.Corner.QuantitativeCorner
import Gtz.Corner.TiedQuadruple

-- Planar: the planar shadow: pushoff, the GAP-S master, tight graphs, stress
import Gtz.Planar.BallPerturbation
import Gtz.Planar.BlochDictionary
import Gtz.Planar.CertificateFrame
import Gtz.Planar.ChordTheorem
import Gtz.Planar.CollinearStratum
import Gtz.Planar.Completeness
import Gtz.Planar.DustControl
import Gtz.Planar.EulerPairing
import Gtz.Planar.LawCounterexample
import Gtz.Planar.LeafTangency
import Gtz.Planar.LocalLaw
import Gtz.Planar.MomentBound
import Gtz.Planar.MomentCovector
import Gtz.Planar.PThreeStratum
import Gtz.Planar.PlanarPlatform
import Gtz.Planar.Pushoff
import Gtz.Planar.Seam
import Gtz.Planar.SilenceDictionary
import Gtz.Planar.SplittingRule
import Gtz.Planar.StressFrame
import Gtz.Planar.TightGraph
import Gtz.Planar.WedgeChain

-- Certificates: Nullstellensatz payloads and their geometric consumption
import Gtz.Certificates.CFiveCertificate
import Gtz.Certificates.CertificateAnchor
import Gtz.Certificates.CyclicStress
import Gtz.Certificates.FrameBridge
import Gtz.Certificates.FrameEncoding
import Gtz.Certificates.GeometricExclusion
import Gtz.Certificates.LawEquivalence
import Gtz.Certificates.PFourCertificate
import Gtz.Certificates.PositivstellensatzObstruction
import Gtz.Certificates.ResidueDissolution
import Gtz.Certificates.TriangleClosure

-- Quantitative: the analytic layer -- collar rates, gates, constants (partly open)
import Gtz.Quantitative.CapArgmax
import Gtz.Quantitative.CapBoundaryConstant
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Quantitative.ChartEmptinessCertificate
import Gtz.Quantitative.CheapAtomGate
import Gtz.Quantitative.ClassRouteCost
import Gtz.Quantitative.CollarFloor
import Gtz.Quantitative.CollarRate
import Gtz.Quantitative.ComplexRankThreeFloor
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Quantitative.EqualShareSixThree
import Gtz.Quantitative.EqualShareSixThreeMargin
import Gtz.Quantitative.ExtremalBasisActivity
import Gtz.Quantitative.FirstOrderLaw
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.GTransformGate
import Gtz.Quantitative.GapStabilityFacts
import Gtz.Quantitative.HeavyAtomDichotomy
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.Interface
import Gtz.Quantitative.MarginContinuity
import Gtz.Quantitative.MinorSumIdentities
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.OddRankDeterminantUpgrade
import Gtz.Quantitative.OneObjectNarrowing
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Quantitative.PlanarTightFrameRigidity
import Gtz.Quantitative.ProjectionChartLegs
import Gtz.Quantitative.ProjectionOnePointMarginal
import Gtz.Quantitative.RankTwoRealnessCount
import Gtz.Quantitative.RealnessEngine
import Gtz.Quantitative.SevenThreeCBFloor
import Gtz.Quantitative.SevenThreeCapsGates
import Gtz.Quantitative.SevenThreeConservation
import Gtz.Quantitative.SevenThreeInvolution
import Gtz.Quantitative.SevenThreeMaxVolume
import Gtz.Quantitative.SevenThreeMiddleBand
import Gtz.Quantitative.SevenThreeNoGo
import Gtz.Quantitative.SevenThreeRigidity
import Gtz.Quantitative.SignReadingCell
import Gtz.Quantitative.StrictDomination
import Gtz.Quantitative.SubsetDeterminantBound
import Gtz.Quantitative.TauOrderStatistics
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Quantitative.TwoMomentCertificate
import Gtz.Quantitative.VolumeAverageLaw
import Gtz.Quantitative.VolumeSelectionFailure
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.WeightedBandCovering
import Gtz.Quantitative.WeightedTripleCriterion
import Gtz.Ties.StratumFirstOrder
import Gtz.Ties.StratumSharpMaximum
import Gtz.Reduction.MixedCharPolynomial

-- Complex: the complex refutations: weighted (4,2) and (6,3) are false over C
import Gtz.Complex.ComplexPadding
import Gtz.Complex.ComplexWitness

-- Ties: exact ties and the corank-one classification
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Ties.CorankOneTieExistence
import Gtz.Ties.DiamondTie
import Gtz.Ties.DominationWithoutCertificate
import Gtz.Ties.NonTetrahedralTie
import Gtz.Ties.RepeatedAtomExclusion
import Gtz.Ties.SelectionObstruction
import Gtz.Ties.SplitTetraLocalBalance
import Gtz.Ties.SplitClassTieFamily
import Gtz.Ties.SplitTetrahedronTie
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Ties.TetrahedronTie
import Gtz.Ties.TieEigenvector

-- the axiom ledger for everything above
import Gtz.Design.GraphicInstance
import Gtz.Quantitative.CollarExponent
import Gtz.Reduction.RankInductionStep
import Gtz.Design.LeverageCapDecision
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Ties.SevenThreeTieLocus
import Gtz.Complex.SharpConstantLedger
import Gtz.Reduction.ExchangeRepair
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Reduction.StrengthenedInductionHypothesis
import Gtz.Complex.PerRankConstantLedger
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.DiagonalRungs
import Gtz.Quantitative.GlobalMinimumRankThree
import Gtz.Design.EqualityLocus
import Gtz.Complex.AtomSplitting
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.WeightFloorWindow
import Gtz.Reduction.HeavyTraceFrame
import Gtz.Ties.StratumLocalCovering
import Gtz.Complex.HesseMarginAttained
import Gtz.Complex.AttainmentRankThree
import Gtz.Complex.SpikePaddingLadder
import Gtz.Ties.TotalTieCorankOne
import Gtz.Design.PrimitiveTightClassification
import Gtz.Quantitative.SpreadCertificateSixThree
import Gtz.Ties.CriticalTieMultiplier
import Gtz.Design.NearPencilStrictDomination
import Gtz.Design.NearPencilTransport
import Gtz.Design.StratumEmptinessLedger
import Gtz.Field.WeightedDesign
import Gtz.Design.ProjectionChart
import Gtz.Field.CorankOne
import Gtz.Complex.SizeAxis
import Gtz.Quantitative.CriticalQuadric
import Gtz.Design.VolumeSamplingAverage
import Gtz.Quantitative.ExpectedCharPolynomial

-- the axiom ledger for everything above
import Gtz.Audit
import Gtz.Quantitative.PositivstellensatzRankThree
import Gtz.Reduction.CompactnessReduction
import Gtz.Quantitative.InteriorExclusion

-- the chart stationarity arc: the first-order system in projection-chart coordinates,
-- its range/kernel multiplier split, the unconditional chart identities, the two-block
-- branch, the witnesses that make the bundle inhabited, the strengthening that quantifies
-- over every tight selection, and that strengthening's covering form
import Gtz.Quantitative.ChartStationary
import Gtz.Quantitative.ChartMultiplierSplit
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.ChartTwoBlock
import Gtz.Quantitative.ChartInstances
import Gtz.Quantitative.ChartStrongStationary
import Gtz.Quantitative.ChartCovering

-- the chart scaffolding under that arc: the descent lemma deriving the covering condition
-- from minimality along a Cayley curve, the compactness of the closed chart domain with
-- attainment of the chart objective on it, and the spectral factorisation discharging
-- ChartPointHasDesign.  Scaffolding only -- no cell is closed by any of the three
import Gtz.Quantitative.ChartDescentFromMinimality
import Gtz.Reduction.ChartAttainment
import Gtz.Reduction.ChartPointFactorisation

-- the July 2026 sweep: nine lanes attacking the residuals that block rank three, plus
-- the isolated-block leaf.  Appended rather than filed into the layer blocks above
-- because two of them import upward out of their own directory, so their position in
-- this list would misstate the hierarchy the header describes.  Grouped by directory,
-- alphabetical within it.  Read each file's own PROVED / NOT PROVED header before
-- citing it: MOST OF THESE LAND A WEAKENING OR A NAMED WALL, NOT THE TARGET.
-- Design: the line-pattern hinge -- (a) the pattern enumeration and the two hinge
-- assemblies, whose completeness rests on an enumeration verified OUTSIDE Lean;
-- (b) the tie-free stratum classes, WALLED with zero of the 32 classes discharged
import Gtz.Design.LinePatternEnumeration
import Gtz.Design.StratumTieFreeClasses
-- Quantitative: two new decision cells (no advance on covering); PARTITION-BELOW-ONE
-- discharged; the uniform max-volume Gram floor 31/150 -> 37/150, clearing the
-- field-blind ceiling but short of 1/3; the metric reformulation with its Veronese
-- no-go and exact extremal; the (7,3) syzygy bricks, walled by counting at a factor
-- five; the (6,3) pen ledger, walled on a Radon interval of length 1/4; the nu-coordinate
-- reformulation, which REFUTES the quarter conjecture; the spread-floor region, whose
-- (7,3) target is vacuous above the Welch ceiling
import Gtz.Quantitative.DecisionAtlasCellsSevenThree
import Gtz.Quantitative.IsolatedBlockExclusion
import Gtz.Quantitative.SevenThreeM7March
import Gtz.Quantitative.SevenThreeMetricBound
import Gtz.Quantitative.SevenThreeSyzygy
import Gtz.Quantitative.SixThreeNuCovering
import Gtz.Quantitative.SixThreePenLedger
import Gtz.Quantitative.SpreadFloorRegionSevenThree

-- the attainment cluster: the all-heavy minimising counterexample, UNCONDITIONAL at (6,3)
-- because both smaller rungs are gtzWeighted_of_le_five; the deflation floors 3/5 and 2/3
-- with the lane's exact ceiling (below one on the whole all-heavy class, so the lane is
-- structurally spent at the frontier); and the weld joining Gtz.chartObjective to
-- Gtz.HasChartDominatingSubsetAtValue, which occurred in disjoint files, so the shipped
-- attainment theorem and the shipped descent theorems could not compose.  NO CELL IS
-- CLOSED: every (7,3) statement still carries the open GtzWeighted 6 3.  Both files
-- import upward out of Gtz/Quantitative/, hence their position here rather than in the
-- layer blocks above.
import Gtz.Reduction.AllHeavyMinimiser
import Gtz.Reduction.ChartAttainmentWeld

-- the dual-leverage cluster: Gtz.exists_naimarkDual_loewnerEquiv was GENERALISED IN PLACE
-- (Gtz/Reduction/SplitTransfer.lean) to also return the leverage dictionary, rather than
-- landing a third copy of the Naimark construction; a downstream module cannot derive that
-- conjunct, because the complement flip is stated only for subsets of size k and is
-- therefore silent about co-singletons whenever m > k + 1.  What the dictionary buys is
-- UNCONDITIONAL and does not depend on the open GtzWeighted 6 3: a design with a failing
-- co-singleton already has a dominating k-subset, because the DUAL deflation lands at
-- (6,4) resp. (5,3) -- corank two, a theorem -- where the primal deflation would land on
-- the open (6,3).  The residual (7,3) and (6,3) obligations are correspondingly narrowed
-- to the doubly-heavy stratum, and lonelyAxisDesign shows that narrowing is PROPER.
-- NEITHER CELL IS CLOSED.
import Gtz.Reduction.NaimarkLeverage

-- the line-count cluster: HasAtMostLines, the iterated parallel merge, and the two (7,3)
-- tie strata it swallows.  UNCONDITIONAL -- the ladder bottoms out at corank one and
-- corank two, both theorems, so nothing here consumes the open GtzWeighted 6 3.  But it
-- also does not approach it: gtzWeightedAll_three_of_hasAtMostLines_rankAddThree proves
-- that raising the free line count by one, uniformly in the rank, IS the conjecture, so
-- the merge ladder is FINISHED at rank + 2 and the residual is the generic case.  The
-- diamond leverages (2 and 13/4 four times) give the first strict all-heaviness of the
-- diamond primitive, which the tree had only in non-strict form; that in turn REFUTES the
-- conjecture that every all-heavy (7,3) tie is a split simplex, and shows that narrowing
-- the (5,3) hinge to all-heavy designs does not restore it.  NO CELL IS CLOSED.
-- LineCountReduction imports upward out of Gtz/Reduction/, hence its position here.
import Gtz.Design.DiamondLeverage
import Gtz.Reduction.LineCountReduction

-- the argmax/floor and private-atom cluster.  ArgmaxFloorDictionary proves that the floor
-- statement and the unconditional lower bound on argmax-dominated values are the SAME
-- statement, so deleting the GtzWeighted premise from the shipped argmax theorem and
-- quantifying over designs IS the conjecture -- a NO-GO promoting to theorem what
-- Gtz/Quantitative/InteriorExclusion.lean asserted twice in prose.  Note the scope: the
-- equivalence is ARGMAX-ONLY, so it does not close the bundled interior lane, and the best
-- unconditional replacements it yields are 1/3 strictly at (7,3) and 3/5 at (6,3), the
-- latter from the landed deflation floor and therefore free of the open GtzWeighted 6 3.
-- PrivateAtomLocalisation weakens the shipped isolated-BLOCK localisation to a per-ATOM
-- privacy condition and derives the cross-mass inequality it generalises to.  Its below-one
-- consumers are DEAD: a nonempty private part already forces 1 <= value, so the (7,3)
-- two-private-atom bound and the three-triple PATH classification of the source scratch are
-- VACUOUS and are deliberately not landed -- see that file's header.  NO CELL IS CLOSED.
import Gtz.Quantitative.ArgmaxFloorDictionary
import Gtz.Quantitative.PrivateAtomLocalisation

-- the equal-share and traceless-chart cluster.  PairRungAggregate carries the shipped chart
-- pair conservation law across the weight congruence into the atom coordinates the
-- compatibility predicates are stated in -- the two layers had no bridge -- and reads off
-- that every all-heavy rank-three design owns a STRICTLY positive pair minor, stronger than
-- the shipped positive-triple-SUM statement.  EqualShareSevenThree closes, on the (7,3)
-- equal-share stratum only, the refutation channel of
-- Gtz.not_gtzWeightedAll_three_of_no_compatibleTriangle: a compatible triangle always
-- exists there.  BOTH ARE EDGE-HALF RESULTS AND NEITHER SETTLES ANYTHING -- compatibility
-- is NECESSARY for domination, the cubic tie leg is untouched, and the stratum is a measure
-- zero slice.  VeroneseRankFiveNoGo strengthens the shipped Veronese barrier
-- Gtz.not_abstractMetricTripleBound_sevenThree by adding the rank bound every real Y-Gram
-- satisfies for free: the shipped refuting witness has rank six, this one has rank at most
-- five, so the obvious escape from that barrier is closed.  It is a NO-GO about routes and
-- advances no cell.
import Gtz.Quantitative.EqualShareSevenThree
import Gtz.Quantitative.PairRungAggregate
import Gtz.Quantitative.VeroneseRankFiveNoGo

-- the BARRIER corpus: seven modules, every one of them a NEGATIVE result naming a family of
-- proof strategies that cannot work.  NONE OF THEM ADVANCES ANY CELL; they exist so that no
-- future agent re-attempts a lane this campaign has already paid for.  Read each file's own
-- PROVED / NOT PROVED header before citing it, and note in particular:
--   LiftedCoveringPresentation removes scope caveat (i) from the shipped Positivstellensatz
--     obstruction by lifting the two-leg disjunction, and calibrates the lifted support
--     notion to GtzWeightedAll 3 exactly.  It does NOT recover the degree reading, caveat
--     (ii), and its support floor is FOUR, not the five the source scratch conjectured.
--   TieRowLaw supplies the e_3 pair row law the shipped ChartHadamard header says is
--     missing, then shows the rung it opens points the WRONG WAY: pair-conditioned averaging
--     of the tie leg is strictly negative under AllHeavy at every weight and size.
--   DominationMatroidRefutation kills greedy/exchange/basis-augmentation selection outright.
--   GraphicRankThreeCap caps the graphic slice at six directions above size six.
--   TiltConcentration proves the tilt family is a CONSEQUENCE of strict GTZ -- the lane is
--     circular -- and TiltLevelOneSignLaw reduces its fate to the campaign's OPEN
--     non-total-tie question, so neither settles EcpStar.
--   ClassicalConstantAttained is FRAME-SIDE ONLY and constructs no WeightedDesign; its
--     bridge from a symmetric trace-k idempotent to a Parseval frame is NOT mechanized, and
--     cannot be made rational.  Its "attainment" is of the CLASSICAL constant 1/13 and is
--     unrelated to the chart-minimiser sense of Gtz/Reduction/ChartAttainment.lean.
-- TiltConcentration must precede TiltLevelOneSignLaw; the other five are independent.
import Gtz.Certificates.LiftedCoveringPresentation
import Gtz.Design.GraphicRankThreeCap
import Gtz.Ties.DominationMatroidRefutation
import Gtz.Quantitative.ClassicalConstantAttained
import Gtz.Quantitative.TieRowLaw
import Gtz.Quantitative.TiltConcentration
import Gtz.Quantitative.TiltLevelOneSignLaw

-- Crux assembly: the (6,3) counterexample NORMAL FORM.  SixThreeCrux bundles eight
-- constraints on one design and is inhabited IF AND ONLY IF GtzWeighted 6 3 fails, with no
-- open hypothesis on either side; the whole first-order layer (strong stationarity bundle,
-- argmax field, tight covering) is DERIVED in its namespace rather than carried as fields.
-- Read three things before citing it.
--   It is a REFORMULATION.  An equivalence cannot decide the cell it reformulates; what it
--     buys is that all eight constraints may be assumed at once without re-derivation.
--   The carrier is the DESIGN and the bundle is derived on its CHART point.  The objective
--     mismatch of Gtz/Reduction/CompactnessReduction.lean stands: a design-margin minimiser
--     is NOT a chart-objective minimiser, so this file's material does not transfer to
--     Gtz.exists_collared_allHeavy_minimiser_sevenThree.
--   The chart-side coverage combinatorics STOPS at two argmax blocks.  Three is reached on
--     the QUADRIC side by the shipped Gtz.three_le_card_activeSubsetImage_sixThree, from a
--     datum no crux carries -- the file header names why.
-- SevenThreeCrux has SEVEN fields, not eight: the equal-share exclusion has no (7,3) source,
-- and its production theorem carries the open GtzWeighted 6 3.
import Gtz.Quantitative.SixThreeCrux

-- Fourth-moment realness: the projective-2-design floor on the share-weighted fourth
-- moment of the direction Gram, sum_{c,d} s_c s_d gamma_cd^4 >= 3k/(k+2), UNCONDITIONAL at
-- every rank and size (no all-heavy, no uniform share, no nondegeneracy).  At rank three
-- the constant is 9/5.  Landed beside it is the FIELD-BLIND floor 2k/(k+1) -- the same
-- certificate with one summand deleted -- and the strict gap between the two for rank >= 2.
-- Read three things before citing it.
--   Realness is consumed at exactly ONE step, Gtz.sum_veroneseMomentTensor_swap, which holds
--     because the atom u u^T is a SYMMETRIC matrix.  The file header names it.
--   NOTHING over the complex numbers is formalised.  What is proved is the cost of deleting
--     the swap summand; identifying 2k/(k+1) as THE complex constant is a citation.
--   Sharpness is NOT proved, and there is no domination consequence -- this is substrate.
-- The constant is guarded: specialised to (7,3) uniform share it re-derives the shipped
-- Gtz.fourth_moment_ge_of_uniformShare with the SAME 49/5, by an independent route.
import Gtz.Quantitative.FourthMomentRealness

-- The switching / two-graph layer: the SECOND quantum of realness, after the fourth moment.
-- Gtz.switchedDesign is the action of per-atom sign flips on WeightedDesign at every rank
-- (Parseval survives because atomMatrix is quadratic), and domination is invariant under it
-- -- the legitimacy lemma that makes the sign pattern a GAUGE rather than data.  On top of
-- it: Gtz.edgeSign, Gtz.tripleParity, and the bridge
--   discriminantTie = excessGap + 2 * tripleParity * |p_ab p_ac p_bc|,
-- which isolates the ENTIRE non-sign-blind content of the tie leg in one +-1 bit, and prices
-- it at 4|product| (Gtz.abs_discriminantTie_sub_excessGap).  The two-graph axiom
-- Gtz.tripleParity_fourSet_product holds with NO hypothesis.
-- Read three things before citing it.
--   The vector-level switching invariance was ALREADY SHIPPED as Gtz.triangleProduct_smul in
--     Gtz/LinAlg/SignForcing.lean; what is new here is the DESIGN-level action and the
--     dictionary to discriminantTie.  Nothing there is re-derived.
--   NO CLAIM IS MADE ABOUT THE COMPLEX CASE.  The realness is argued in prose only; the
--     mechanized measure of it in this repo is SignForcing's field door (obtuse bound 4 over
--     R^3 against 7 over C^3), not anything proved here.
--   The SHARP COUNT of negative triangles at six and seven lines is NOT reached and is
--     WALLED in the file header with the two declined routes.  Section 8 proves only that no
--     single atom can have all of its triangles incoherent.
-- Guarded at four reference points in exact rational arithmetic: the (4,3) and (7,3) tie
-- strata both return discriminantTie = 0 EXACTLY at parity -1, and at the icosahedron the
-- parity decides domination outright.
import Gtz.Quantitative.SwitchingTwoGraph
