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
import Gtz.Design.CorankThreeHinge
import Gtz.Design.DeflationCertificate
import Gtz.Design.DiamondPrimitive
import Gtz.Design.DominationGates
import Gtz.Design.DowndateInterlacing
import Gtz.Design.FrameConservation
import Gtz.Design.LeverageBound
import Gtz.Design.MarginTransfer
import Gtz.Design.MultiLineSeven
import Gtz.Design.RhoNormalForm
import Gtz.Design.RigidityBridge
import Gtz.Design.SignSelectedAggregate
import Gtz.Design.SpGraphicCap
import Gtz.Design.StressCertificate
import Gtz.Design.SymmetryReduction
import Gtz.Design.TraceIdentity
import Gtz.Design.WhiteningDistortion

-- Reduction: the ladder: crystallization, Naimark duality, deflation, the lifting lemma
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.KFourDetFloor
import Gtz.Reduction.KFourMixtureLaw
import Gtz.Reduction.KFourSosCore
import Gtz.Reduction.KFourTreeAlgebra
import Gtz.Reduction.KFourUniversalFace
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
import Gtz.Certificates.CollarChartSoundness
import Gtz.Certificates.CollarChartSoundnessChart43210
import Gtz.Certificates.CollarDictionaryIdentities
import Gtz.Certificates.CollarLinePositivity
import Gtz.Certificates.CollarMarginIdentities
import Gtz.Certificates.CollarRealClosure
import Gtz.Certificates.CollarWindowComposite
import Gtz.Certificates.CollarWindowCriterion
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
import Gtz.Quantitative.ProjectionBasisCoordinates
import Gtz.Quantitative.ProjectionGapQuadratic
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
import Gtz.Ties.NonUniformLeverageTie
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

-- The sign layer at the (6,3) crux, plus the realness law of a real Gram.  Two independent
-- pieces of substrate for the sign-side rungs.
--   THE PARITY-FREE GATE.  Gtz.dominates_of_excessGap_nonneg_of_discriminantTie_nonneg drops
--     the parity hypothesis of Gtz.dominates_of_coherent_of_excessGap_nonneg for what the
--     parity was only ever used to supply, so the coherent cell becomes one special case and
--     the vanishing-pairing cell Gtz.dominates_of_excessGap_nonneg_of_exists_atomPairing_eq_zero
--     a second, disjoint one.  Against Gtz.SixThreeCrux.hasNoDominatingTriple it contraposes to
--     THE SQUEEZE, Gtz.SixThreeCrux.discriminantTie_neg_of_excessGap_nonneg: at a crux a
--     nonnegative sign-blind gap forces a strictly negative tie leg.  Unwound
--     (Gtz.SixThreeCrux.isIncoherent_of_excessGap_nonneg) that single inequality says the
--     triple is incoherent, ALL THREE of its pairings are nonzero, and its gap is capped by
--     twice the pairing magnitude.  X0's disjunction, the coherent reading, the
--     vanishing-pairing reading and the quantitative cap are all corollaries of it.
--   THE REALNESS LAW.  Gtz.atomBracket_sq is Cauchy-Binet at rank three -- the Gram
--     determinant is the SQUARE of the bracket -- and Gtz.atomBracket_sq_eq_discriminantTie_add
--     shifts it onto the discriminant system's own six scalars.  Squaring returns the
--     campaign's E2 (Gtz.four_mul_atomPairingProduct_sq_eq) with its coplanar specialisation.
-- Read four things before citing it.
--   X0'S THIRD DISJUNCT IS VACUOUS.  Gtz.dominates_of_coherent_of_excessGap_nonneg carries NO
--     nonzero-pairing hypothesis, so the dichotomy needs no zero-pairing escape clause; the
--     vanishing-pairing case lands in the gap disjunct outright.
--   THE REALNESS INEQUALITY Gtz.two_mul_abs_atomPairingProduct_le_of_incoherent IS SLACK.  It
--     is an equality EXACTLY on the coplanar locus and nowhere else -- at the tetrahedron it
--     reads 2 <= 18 and at the icosahedron 54/(5*sqrt 5) <= 54/5.  A true constraint, NOT a
-- The chart reading law and the covering criterion. The total mass reading is
-- a weighted mean of the kappa readings, so no probe is negative for every
-- selection, a maximal selection of two or more labels is pointwise strict,
-- and a selection that reaches the maximal kappa reading at every probe is
-- positive definite outright. The three-lines instance reduces the chart
-- obligation to a covering selection about six explicit quadratic forms.
import Gtz.Design.ChartReadingLaw
--     finished lever.
--   NOTHING OVER THE COMPLEX NUMBERS IS FORMALISED.  The prose records that the same expansion
--     carries 2*Re(p_ab p_bc p_ca) over C, so the two-valuedness of a real Gram determinant is
--     the realness content; that identification is a citation, not a theorem here.
--   NO COUNT AND NO GLOBAL CONTRADICTION.  Every statement about the crux is PER-TRIPLE.
--     Nothing here bounds how many triples can be incoherent, nothing bounds the pairing
--     magnitude at a crux beyond the cap above, and nothing transports to the Naimark dual.
-- Guarded at both ends: at the icosahedron X0's disjunction is satisfied by its GAP leg at all
-- twenty triples (Gtz.icosaDesign_excessGap_neg), so coherence forcing alone constrains the
-- icosahedral sign pattern NOT AT ALL; and at the (4,3) tie the parity-free gate FIRES on an
-- INCOHERENT triple (Gtz.dominates_tetraDesign_of_parityFreeGate), which the coherent cell
-- cannot reach, with the squeeze's conclusion failing there by exactly zero.
import Gtz.Quantitative.SixThreeCruxSigns

-- The disjoint two-block branch, KILLED on the chart side.  Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily
-- collapses the shipped disjunction three_le_card_chartArgmaxFamily_or_disjoint_partition onto
-- its left branch: the argmax family of a (6,3) crux carries at least THREE triples, matching
-- the (7,3) floor that counting already gave.  Stated generally: at size = 2 * rank the argmax
-- family of a strictly interior global minimiser whose chart is a DESIGN's, at a NEGATIVE value,
-- is never contained in {C, C-complement} -- so it never has two members, and no set of rank
-- atoms is isolated from it.
-- THIS SUPERSEDES A STANDING OPENNESS CLAIM.  The SixThreeCrux header, and this file's own
-- SixThreeCrux cluster above, say the branch is open chart-side and reachable only from
-- Gtz.IsQuadricStationaryData.  It was already closed, by
-- Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue in
-- Gtz.Quantitative.TwoBlockEliminationCertificate, which is phrased as TWO COMPLEMENTARY BLOCKS
-- and never says "disjoint" or "isolated" -- which is why a grep for either word missed it.
-- Nothing here ports the quadric chain; what was missing was the WELD, that at size = 2 * rank
-- a two-member argmax family IS a complementary pair.
-- Landed beside it, and NEW: the chart-side SATURATED-ATOM law, which
-- Gtz.Quantitative.ClassRouteCost records as absent.  A saturated atom's multiplier row is a
-- chart eigenvector of eigenvalue value + t_c, idempotence makes that 0 or 1, and negativity
-- picks 0 -- so the atom's weight is EXACTLY -value and it is a lightest atom.  It is an
-- EQUATION, sharper in form than the quadric 1 <= value, and it EXCLUDES NOTHING on its own:
-- -value <= t_c holds everywhere already.  What DOES cost blocks is having two of them: the
-- ClassRouteCost double count leaves only rank*|family| - size above the coverage floor, so at
-- (6,3) two saturated atoms force a FOURTH argmax triple, and a three-member family carries at
-- most one saturated atom.
-- Read two things before citing any of it.
--   ADMISSIBILITY IS LOAD-BEARING.  Gtz.chartTwoBlockUniformProjection_isChartStationaryData is
--     a (4,2) two-block datum with uniform weights at value = -1/4 = -1/size, NEGATIVE.  It is
--     inadmissible, and that is the only reason it does not refute the theorems here.
--   THREE IS A FLOOR, NOT A CONTRADICTION.  The (6,3) covering census has 2069 classes with two
--     or more members; this closes ONE of them.
import Gtz.Quantitative.ChartDisjointBlockExclusion

-- Gtz.Quantitative.CoherentCountFloor -- THE SHARP COHERENT COUNT.  The switching layer's own
-- header records, as a wall rather than an omission, that it "does not produce a NUMBER" for how
-- many triangles at a vertex must be coherent, and names two declined routes.  Route (i) is
-- executed here.  The mechanism is one identity: read at the design level the shipped gauge
-- Gtz.switchSign is MINUS the shipped Gtz.edgeSign (Gtz.switchSign_eq_neg_edgeSign, no
-- hypothesis, the vanishing pairing included), so after switching at a base the sign of an
-- off-base edge IS the parity of its triangle through that base
-- (Gtz.edgeSign_baseSwitchedDesign).  The coherence-through-base graph is then literally the
-- positive-edge graph of an honest design, a totally incoherent neighbourhood is pairwise obtuse
-- with the base, and the real obtuse cap 3 + 1 in R^3 bounds it by THREE
-- (Gtz.card_le_three_of_forall_incoherent_through_base, sharp at the tetrahedron).  Greedy
-- independence over a bare Finset of ordered pairs (Gtz.exists_independent_of_edges) turns the
-- cap into the count: Gtz.card_coherentPairsThroughBase_ge gives m - 4 coherent triangles through
-- EVERY atom of a rank-three design with nonzero pairings -- 2 at m = 6, 3 at m = 7 -- and the
-- family form Gtz.card_coherentPairsThroughBase_ge_of_family degrades gracefully, an orthogonality
-- costing one triangle rather than the whole count.  Composed with the substrate squeeze:
-- Gtz.SixThreeCrux.two_le_card_coherentPairsThroughBase_and_forall_negative -- two coherent
-- triangles through every crux atom, each with a strictly POSITIVE oriented product, a strictly
-- NEGATIVE sign-blind gap, and a tie leg strictly below twice that product; the (7,3) sibling
-- sits at three.  The vanishing-pairing branch is content, not caveat:
-- Gtz.SixThreeCrux.pairMinor_neg_of_common_orthogonalPartner says an atom orthogonal to two
-- others forces those two to span an INCOMPATIBLE edge, because excessGap collapses to
-- heavyExcess * pairMinor when two pairings vanish.  Landed alongside, and reusable far beyond
-- this rung: Gtz.tripleParity_eq_product_through_base, the four-set axiom SOLVED -- the parity of
-- any triangle is the product of the three parities joining it to any base, so the whole
-- two-graph is determined by its star at one vertex.
-- Read three things before citing any of it.
--   NO GLOBAL COUNT IS CLOSED.  Only the summed form Gtz.sum_card_coherentPairsThroughBase_ge is
--     landed.  Dividing by three -- each triangle counted once per vertex, hence m(m-4)/3, i.e. 4
--     of the 20 at m = 6 -- needs a three-to-one fibre count that is NOT performed.
--   THE COUNT DOES NOT NARROW THE TWO-GRAPH.  The recorded enumeration at six points leaves eight
--     isomorphism classes surviving every combinatorial constraint, the icosahedral one at five
--     coherent triangles per vertex, comfortably inside any band this route reaches.
--   THE NONVANISHING HYPOTHESIS IS REAL.  A crux is not known to have all pairings nonzero, and
--     Gtz.IsPairwiseObtuse is STRICT, so the cap genuinely breaks at a zero pairing.  The honest
--     statement without hypotheses is the dichotomy
--     Gtz.SixThreeCrux.two_le_card_coherentPairsThroughBase_or_exists_orthogonalPair.
import Gtz.Quantitative.CoherentCountFloor

-- Gtz.Quantitative.CoherentCountFloor, ADDENDUM: THE GLOBAL COUNT IS NOW CLOSED TOO, so the
-- first caveat of the cluster above -- "NO GLOBAL COUNT IS CLOSED" -- is SUPERSEDED and should
-- not be cited.  Section 8 of the module carries the three-to-one fibre count the caveat said was
-- not performed: Gtz.coherentFlags (a base together with a coherent pair through it) fibres over
-- Gtz.coherentTripleSets with at most three flags per triangle, one per vertex
-- (Gtz.card_filter_flagAtoms_le_three, whose determinacy step is the ordered-pair lemma
-- Gtz.orderedPair_eq_of_pairFinset_eq), so Gtz.card_coherentTripleSets_ge divides the summed count
-- and gives m(m-4) <= 3 * card -- at least FOUR of the twenty triangles at (6,3)
-- (Gtz.four_le_card_coherentTripleSets_sixThree) and SEVEN of the thirty-five at (7,3).  The other
-- two caveats stand unchanged: the count does not narrow WHICH two-graph a crux carries, and the
-- nonvanishing hypothesis is real.  A third is added here -- the global count is a bare
-- CARDINALITY and says nothing about how the coherent triangles are distributed, so it is not a
-- covering statement and produces no dominating triple.

-- Gtz.Quantitative.ActiveOverlapPatternsSixThree: the OVERLAP CLASSIFICATION of a three-member
-- active family.  Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily put a floor of three under the
-- argmax family of a (6,3) crux; this module says what three covering triples of six atoms can be.
-- Three-set inclusion-exclusion (Gtz.card_union_three_add_pairwiseOverlapSum) plus the fact that
-- distinct equal-card blocks cannot overlap fully leaves EXACTLY THREE SHAPES, and
-- Gtz.overlapPattern_trichotomy_sixThree is the disjunction, stated in ordering-free invariants so
-- that no relabelling is needed at the point of use:
--   TRIANGLE  overlaps 1,1,1, empty core, private parts 1,1,1;
--   CHAIN     overlaps 2,1,0, empty core, private parts 0,1,2 -- and the disjoint pair is a
--             COMPLEMENTARY pair (Gtz.eq_compl_of_card_inter_eq_zero_sixThree);
--   STAR      overlaps 2,1,1, core one atom, private parts 1,1,2 -- and the core IS
--             Gtz.HasSaturatedAtom (Gtz.hasSaturatedAtom_triple_iff).
-- The private counts come from one identity, Gtz.card_privateParts_eq_pairwiseOverlapSum_sixThree:
-- TOTAL PRIVATE MASS EQUALS TOTAL OVERLAP MASS, three at the core-free patterns and four at the
-- star.  Its corollary Gtz.exists_nonempty_blockPrivatePart_sixThree says every pattern has a
-- private atom, which is what makes Gtz.Quantitative.PrivateAtomLocalisation applicable at all;
-- Gtz.private_of_mem_blockPrivatePart_of_isActiveFamily is the bridge to that file's quantifier and
-- Gtz.overlapAbsSum_ge_of_isActiveFamily_triple the cross-mass inequality it yields.
-- The crux weld is Gtz.SixThreeCrux.exists_overlapPattern_of_card_chartArgmaxFamily_eq_three, with
-- Gtz.SixThreeCrux.le_pairwiseOverlapSum_chartArgmaxFamily as the unconditional floor that survives
-- inside a larger family.  At (7,3) the identity drops to 2 + core and the shapes become PATH,
-- SPLIT and CORE; below one the outer two die -- the split's third block is ISOLATED and the core
-- is SATURATED -- leaving Gtz.pathPattern_of_isActiveFamily_of_value_lt_one_sevenThree, the PATH
-- CLASSIFICATION the header of Gtz.Quantitative.PrivateAtomLocalisation records as dropped.
-- Read four things before citing any of it.
--   THE STAR IS NOT EXCLUDED AT A CRUX.  The chart-side saturation law is an EQUATION, not an
--     exclusion: Gtz.SixThreeCrux.weight_eq_neg_chartObjective_of_starPattern pins the core atom's
--     weight to -chartObjective and closes NOTHING, since six weights at or above -chartObjective
--     summing to one are consistent for every value in the window.  The crux statement therefore
--     keeps the star as an explicit third disjunct.
--   THE TWO SIDES ARE NOT INTERCHANGEABLE.  The star DOES die below one on the QUADRIC side, by
--     Gtz.one_le_value_of_hasSaturatedAtom_of_isActiveFamily -- that is
--     Gtz.triangle_or_chain_of_isActiveFamily_of_value_lt_one_sixThree.  A Gtz.SixThreeCrux carries
--     Gtz.IsChartStationaryData and never Gtz.IsQuadricStationaryData, so that theorem does NOT
--     apply to a crux and the private-atom kit does not reach one either.
--   NON-VACUITY OF THE BELOW-ONE QUADRIC COROLLARIES IS OPEN.  The header of
--     Gtz.Quantitative.PrivateAtomLocalisation records, as a verified-but-UNLANDED fact, that a
--     nonempty private part already forces 1 <= value -- and every pattern here has one.  If that
--     is right the three-member below-one hypothesis is contradictory and those two corollaries are
--     vacuously true.  The CLASSIFICATION itself carries no such hypothesis and is not vacuous.
--   NOTHING HERE EXCLUDES A TRIANGLE OR A CHAIN, on either side, and NOTHING HERE CONSTRAINS AN
--     ARGMAX FAMILY OF FOUR OR MORE MEMBERS beyond the unconditional overlap floor: three distinct
--     members of a larger family need not cover, and the classification consumes covering.
import Gtz.Quantitative.ActiveOverlapPatternsSixThree

-- Gtz.Quantitative.ChartDuality: THE CHART DUAL, and the exact boundary of what transports
-- across it.  The campaign ledger's TIER D asked for a dual design whose atom pairings are the
-- NEGATIVES of the primal's (D1), whose leverages are 1/t_c - l_c (D2), whose two-graph is the
-- COMPLEMENT of the primal's (D3), and whose chart gap adds to the primal's to give a diagonal
-- (D5).  All four are proved here at every size and rank from ONE construction:
-- 1 - Gtz.projectionOfDesign is symmetric, idempotent, of trace m - k, so
-- Gtz.exists_orthonormalFrame_of_symmetric_idempotent factors it and
-- Gtz.designOfOrthonormalFrame reattaches the ORIGINAL weights.  Gtz.IsChartDual names the
-- relation, Gtz.exists_isChartDual builds it, Gtz.IsChartDual.symm makes it an involution, and
-- at (6,3) the dual rank is again three -- the cell is literally self-dual.
-- The load-bearing readings: Gtz.dotProduct_chartDual_of_ne (D1, SAME zero set),
-- Gtz.leverageOf_chartDual and Gtz.atomShare_chartDual (D2, s' = 1 - s),
-- Gtz.tripleParity_chartDual (D3, THE ANTI-PARITY LAW), Gtz.chartPointGap_add_chartDual (D5).
-- Read three things before citing any of it.
--   THERE ARE NOW TWO DUALS AND THEY ARE DIFFERENT DESIGNS.  Gtz.dualDesign of
--     Gtz/Reduction/SplitTransfer.lean is built from a different isometry precisely so that the
--     LOEWNER FLIP Gtz.exists_naimarkDual_loewnerEquiv holds; it does NOT have negated pairings.
--     The chart dual has negated pairings and does NOT satisfy the flip -- proved, not conjectured,
--     by Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates at the new rational
--     all-heavy (6,3) witness Gtz.orthoSplitDesign.  ALWAYS SAY WHICH DUAL YOU MEAN.
--   THE LEDGER'S D4 BAND IS THEREFORE UNAVAILABLE.  Its antecedent asked one object to carry both
--     the parity flip and the crux's allHeavy / non-dominating transport; no object does.
--   THE ANTI-PARITY LAW NEEDS NONVANISHING PAIRINGS, because the shipped edgeSign convention sends
--     zero to +1.  The sign-blind half, Gtz.atomPairingProduct_chartDual, is hypothesis-free.
--     Gtz.exists_antiParityPartner_sixThree is the repaired form of the anti-parity partner: it
--     quantifies over PAIRWISE DISTINCT triples, because Gtz.tripleParity_degenerate makes the
--     unrestricted version UNSATISFIABLE.
import Gtz.Quantitative.ChartDuality

-- Gtz.Quantitative.ActiveOverlapPatternsSixThree, ADDENDUM: the private-mass identity now has a
-- SET-LEVEL form.  The three private parts are pairwise disjoint
-- (Gtz.disjoint_blockPrivatePart_first_second and its two siblings), so
-- Gtz.card_union_blockPrivateParts_eq_pairwiseOverlapSum_sixThree upgrades the counting identity to
-- a statement about the union, and Gtz.card_union_blockPrivateParts_of_trianglePattern_sixThree
-- reads off that AT THE TRIANGLE THE PRIVATE ATOMS THEMSELVES FORM A TRIPLE -- by coverage exactly
-- the complement of the triple of meeting points, so the triangle splits the six atoms into two
-- triples canonically.  NEITHER OF THOSE TWO TRIPLES IS KNOWN TO BE AN ARGMAX BLOCK, and nothing
-- here says it is; the split is a structural refinement of the pattern, not a new active family.

-- Gtz.Quantitative.ExcessGapCensus -- the excess-gap census at the (6,3) crux.  The rung was
-- commissioned to produce a LOWER bound on #(triples with excessGap >= 0); it does not exist, and
-- the refutation is a theorem here rather than prose.  What the cluster proves:
--   THE CENSUS OF THE ICOSAHEDRON IS EMPTY, Gtz.censusTripleSets_icosaDesign_eq_empty -- every one
--     of its twenty triples has sign-blind gap exactly -14/5.  Gtz.icosaDesign_allHeavy and the new
--     Gtz.icosaDesign_hasNoParallelPair give it two of the crux's sign-blind fields, and excessGap
--     reads ONLY the three heavy excesses and the three squared pairings, so no hypothesis
--     expressible in sign-blind data can force a census triple to exist.
--   THE QUARTER WINDOW, Gtz.SixThreeCrux.excessGap_lt_quarter_mul_heavyExcess_prod -- at a crux
--     excessGap < u_a u_b u_c / 4 at EVERY triple with no hypothesis, i.e. the normalized edge sum
--     q_ab + q_ac + q_bc exceeds 3/4 everywhere.  Sharp: the chain closes with equality at
--     q = 1/4 on all three edges, the split-tetrahedron tie.
--   THE CENSUS CEILING, Gtz.SixThreeCrux.card_censusTripleSets_le_sixteen and its per-atom form at
--     eight of ten, by composing the substrate squeeze with the shipped coherent floors.
--   THE TWO-SIDED SIGN BAND -- the upper halves are new.  For ANY (6,3) design with nonvanishing
--     pairings the coherent triples number between four and sixteen
--     (Gtz.card_coherentTripleSets_mem_band_sixThree) and between two and eight through every atom
--     (Gtz.card_coherentPairsThroughBase_mem_band_sixThree).  The ceilings run the shipped floors
--     on the ANTI-PARITY PARTNER, whose coherent triples are exactly this design's incoherent ones.
--   THE SET-LEVEL INVARIANCE, Gtz.tripleParity_congr_of_eq_triple and
--     Gtz.excessGap_congr_of_eq_triple -- both sign-blind scalars are functions of the
--     three-element SET, which is what the existentially-ordered triple families needed.
-- WHAT THIS CLUSTER DOES NOT CLOSE:
--   NO CENSUS FLOOR AT ANY THRESHOLD.  The icosahedral theorem says none is available from
--     sign-blind data at all, so a sector table keyed on the census runs at threshold T = 0 and
--     gains nothing.  A floor is reachable only to an argument consuming two-graph realizability.
--   NO TWO-GRAPH CLASS IS EXCLUDED.  The band [2,8] is SHARP at both ends and leaves twelve of the
--     sixteen isomorphism classes standing; the icosahedron sits at five coherent per vertex,
--     comfortably inside it.
--   NOTHING ABOUT IsEmpty for either crux, and no bound on the census from below at any atom.
--   Gtz.IsCoSingletonSpreadLemma IS STATED, NOT PROVED.  The co-singleton cap
--     Gtz.SixThreeCrux.not_posSemidef_coSingleton_sub_five is CONDITIONAL on it.
import Gtz.Quantitative.ExcessGapCensus

-- Gtz.Quantitative.ExcessGapCensus, ADDENDUM: THE D6 OBLIGATION IS DISCHARGED, so the caveat above
-- is superseded and must not be cited.  Gtz.isCoSingletonSpreadLemma is a THEOREM and
-- Gtz.SixThreeCrux.not_posSemidef_coSingleton_sub_five is UNCONDITIONAL: no co-singleton of a (6,3)
-- crux reaches five times the identity.  The route needs no square root -- whiten the co-singleton
-- ALREADY SCALED by the uniform weight 1/5, which is positive definite, so
-- Gtz.exists_congruence_to_one supplies the congruence directly; re-index the five surviving atoms
-- by the order isomorphism of {c}^c and read them through Gtz.whitenedFamilyDesign as a genuine
-- Gtz.WeightedDesign 5 3, where Gtz.gtzWeighted_corank_two 3 applies; transport the floor back with
-- Gtz.posSemidef_congr_right.  With the crux field hasStrictlyDominatingCoSingletons this is the
-- two-sided window Gtz.SixThreeCrux.coSingletonWindow.
-- STILL NOT CLOSED: the window EXCLUDES NOTHING BY ITSELF.  It constrains each of the six
-- co-singletons separately and is consistent with every weight vector a crux could carry; the
-- upper end is genuinely attained at the (6,3) diamond ties, so it is a true constraint with no
-- slack rather than a contradiction in waiting.

-- Gtz.Quantitative.TwoGraphCollision: THE SIGN LAYER OF THE (6,3) CELL, AS ONE DECIDABLE OBJECT,
-- WITH EVERY KNOWN CONSTRAINT PROVED AND APPLIED.  A two-graph on six atoms is its LINK at atom 0
-- -- ten parities, a Nat below 1024 -- because Gtz.tripleParity_eq_product_through_base is
-- hypothesis-free, so the four-set cocycle law holds DEFINITIONALLY and no switching gauge has to
-- be fixed at the design level.  Gtz.sectorIncoherent decodes an arbitrary triple as the
-- exclusive-or of three link bits and Gtz.sectorIncoherent_linkWordOf proves the decode agrees with
-- Gtz.tripleParity at EVERY triple of every design, degenerate ones included.
--   THE THREE LEVERS, ALL PROVED.  L1 is the shipped Gtz.card_le_three_of_forall_incoherent_through_base.
--     L2, NEW, is Gtz.card_le_three_of_forall_coherent_through_base: the same cap with the parities
--     reversed, obtained by running L1 on the anti-parity partner Gtz.exists_antiParityPartner_sixThree.
--     L3, NEW and the deepest, rests on Gtz.sum_erasePair_weight_mul_atomPairing -- THE EDGE LAW,
--     the Parseval identity read at an off-diagonal entry with the two diagonal terms split off,
--     sum_e t_e p_ce p_ed = p_cd (1 - s_c - s_d).  Multiplying by p_cd makes each summand the
--     oriented triple product of {c,d,e}, whose sign IS the parity, so a uniformly signed edge
--     forces s_c + s_d off one (Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge and
--     Gtz.one_lt_atomShare_add_atomShare_of_incoherentEdge) and three such edges in a perfect
--     matching contradict Gtz.sum_atomShare_eq_rank.
--   THE RESIDUE.  Gtz.card_residualSectors: 842 OF THE 1024 TWO-GRAPHS SURVIVE, in eight of the
--     sixteen isomorphism classes; Gtz.card_leverOneSectors records 948 for L1 alone and
--     Gtz.card_leverOneAndTwoSectors 872 for L1 and L2, so the two new levers are worth 76 and 30
--     patterns.  Gtz.SixThreeCrux.linkWord_mem_residualSectors puts every crux with nonvanishing
--     pairings inside Gtz.residualSectors, ONE explicit decidable object for X7 and for any later
--     campaign.
-- THIS DOES NOT CLOSE THE (6,3) CELL, AND THE RESIDUE IS SHARP RATHER THAN MERELY BEST-KNOWN.
--   THE SECTOR TABLE DOES NOT EMPTY: 842 of 1024 survive, and this is now the WHOLE known
--     combinatorial lane, not a stage of it -- all three levers are proved above.
--   EVERY ONE OF THE EIGHT SURVIVING CLASSES IS REALISED BY A DESIGN, by an explicit six-tuple of
--     integer directions with exact positive rational Parseval coefficients, so NO CORRECT
--     SIGN-ONLY ARGUMENT CUTS ANY OF THEM.  Representatives are pinned both ways by
--     Gtz.sectorSurvives_survivingClassRepresentatives and
--     Gtz.not_sectorSurvives_killedClassRepresentatives.
--   NO SURVIVING CLASS HAS A MAGNITUDE MARGIN: the per-class infimum of the domination margin is
--     exactly one, measured to eighty digits, so there is no per-class inequality to mechanize.
--   THE WHOLE TABLE LIVES IN THE NONVANISHING BRANCH.  All three levers need pairings that do not
--     vanish and a crux is NOT known to satisfy that; two DISJOINT orthogonal pairs block all
--     thirty L1 tests at once and revert the table to all 1024 patterns.  The hypothesis is carried
--     explicitly and is not removable by anything here.
--   THE COMPLEMENT FILTER IS NOT APPLIED: it would need the complement two-graph to be carried by
--     another CRUX, and Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates says the chart
--     dual is not the Naimark dual.
--   NOTHING ABOUT IsEmpty for either crux.
import Gtz.Quantitative.TwoGraphCollision

-- Gtz.Quantitative.TwoGraphCollision, ADDENDUM (section 8): ONE PIECE OF THE VANISHING-PAIRING
-- BRANCH IS REACHED, so the caveat above is sharpened rather than superseded.  At an ORTHOGONAL
-- edge the edge law's right-hand side is identically zero, so the four star products must CANCEL
-- and the edge CANNOT BE SIGN-SATURATED AT ALL, in either parity --
-- Gtz.not_forall_coherent_of_orthogonalEdge and Gtz.not_forall_incoherent_of_orthogonalEdge,
-- strictly stronger than the share inequalities the nonvanishing case gives.  So L3's obstruction
-- survives an orthogonality ON a matching edge.
-- STILL NOT CLOSED: L1 and L2 genuinely FAIL at a vanishing pairing rather than merely resisting
-- proof, because Gtz.card_le_succ_of_isPairwiseObtuse_on demands STRICT obtuseness and the
-- non-strict cap in R^3 is six, not four.  Gtz.SixThreeCrux.linkWord_mem_residualSectors therefore
-- still carries the global nonvanishing hypothesis, and nothing here removes it.

import Gtz.Quantitative.SixThreeExclusionFrontier

-- Gtz/Quantitative/SixThreeExclusionFrontier.lean -- THE TERMINAL MODULE OF THE (6,3)
-- EXCLUSION CAMPAIGN.  It contracts Gtz.SixThreeCrux as far as the landed material allows
-- and names what survives.  Four things land here.  (1) THE SHARP WINDOW: the crux's chart
-- value lies in [-4/27, 0), not the shipped [-1/6, 0) -- free from data the crux already
-- carries, via Gtz.neg_four_div_twentySeven_le_value_of_isChartStationaryData, with the
-- (7,3) sibling at -10/77 against -1/7.  (2) THE UNIFIED STAR LAW: an edge whose four
-- triples all carry the SAME parity has its own pairing nonzero AND its two shares off one,
-- under STAR-nonvanishing alone -- where the shipped saturated-edge lemmas asked for GLOBAL
-- nonvanishing and the shipped orthogonal-edge lemmas covered only the vanishing edge.  One
-- statement subsumes all four.  (3) THE ZERO-PAIRING BRANCH, given content: at a crux an
-- orthogonal edge with nonvanishing star carries BOTH parities among its four triples.
-- (4) THE FRONTIER Gtz.SixThreeCrux.frontier, hypothesis-free, and the design-level
-- REFUTATION TARGET Gtz.IsSixThreeRefutationCandidate, whose emptiness SUFFICES for the
-- wall cell and -- with the (7,3) half -- for GtzOriginal n 3 at every positive n.
-- WHAT THIS DOES NOT CLOSE, AND THE CAPITALS ARE THE POINT: IsEmpty Gtz.SixThreeCrux IS
-- STILL OPEN, AND NOTHING HERE APPROACHES IT.  The frontier is a CONJUNCTION THAT IS NOT
-- CONTRADICTORY.  THE SIGN LANE IS CLOSED IN BOTH DIRECTIONS: all three levers are proved
-- and they leave Gtz.card_residualSectors = 842 of the 1024 two-graphs in eight isomorphism
-- classes, each realised by an explicit design, so no correct sign-only argument cuts any of
-- them.  THE CENSUS LANE IS EMPTY BY THEOREM (Gtz.censusTripleSets_icosaDesign_eq_empty).
-- THE ZERO-PAIRING BRANCH IS NOT CLOSED EITHER -- it is merely no longer a black hole.
-- THE SINGLE HIGHEST-VALUE MISSING INEQUALITY IS A LOWER BOUND ON |chartObjective| AT A
-- CRUX; without it the domination margin's constrained infimum is exactly one in every
-- surviving sign class, so there is NO per-sector magnitude inequality to mechanize.

import Gtz.Reduction.StressWalk

-- Gtz/Reduction/StressWalk.lean -- CRYSTALLIZATION ONE ATOM BELOW THE SHIPPED CAP, AND WITH
-- IT THE ARROW THE TREE WAS MISSING.  Gtz.exists_null_direction asks its perturbation to
-- annihilate SEVEN functionals -- the six upper-triangle Parseval coordinates AND the total
-- mass -- so Gtz.crystallization stops at M(k) = k(k+1)/2 + 1 and at rank three cannot reach
-- (7,3).  Gtz.exists_parsevalNullDirection DROPS THE MASS FUNCTIONAL by composing
-- Gtz.momentMap with LinearMap.fst: six functionals on seven unknowns always have a kernel,
-- so EVERY (7,3) design carries a stress and the hypothesis relaxes to k(k+1)/2 < m.  The
-- price is that the mass drifts, and the whole content is that the drift is AFFINE -- along
-- w(s) = t + s*stress the mass is exactly 1 - s*A with A = sum stress -- so after normalising
-- the sign of A the walk that terminates is also the walk that does not gain mass, landing at
-- W in (0,1].  Parseval is preserved EXACTLY along the whole line.  A mass BELOW one is a
-- GIFT, not a loss: Gtz.Dominates reads the WEIGHT-FREE Gtz.subsetSum, so a triple dominating
-- the shrunken atoms gives W*S >= I hence S >= (1/W)*I >= I --
-- Gtz.posSemidef_sub_one_of_smul_sub_one, which is where W <= 1 is spent.
--   THE FLAGSHIP: Gtz.gtzWeighted_seven_three_of_six_three, demanding nothing beyond (6,3)
--     where the pre-existing Gtz.gtzWeighted_seven_three_of_six_three_of_heavy still demanded
--     Gtz.GtzWeightedHeavy 7 3.  With the shipped converse the two cells are EQUIVALENT
--     (Gtz.gtzWeighted_six_three_iff_seven_three), so the campaign may fight at whichever
--     carries more structure -- and RANK THREE IS NOW ONE OBJECT AS AN IFF,
--     Gtz.rank_three_iff_six_three, sharpening Gtz.rank_three_iff_the_two_residuals from a
--     conjunction of two cells to a single cell.  Gtz.liftingLemma_two_iff_six_three does the
--     same for Gtz.liftingLemma_two_iff_the_two_residuals.
--   THE CAP DROPS AT EVERY RANK: Gtz.crystallizationSharp at M'(k) = k(k+1)/2, so rank four's
--     single object falls from (11,4) to (10,4) (Gtz.gtzWeightedAll_four_of_ten) and
--     Gtz.gtzWeightedAll_of_veroneseTop states one object per rank at the Veronese dimension.
--     At rank two M'(2) = 3 and every size at or below three is already a theorem, so
--     Gtz.gtzWeightedAll_two_of_walk reproves weighted rank two from the pigeonhole -- and a
--     transitive walk over ConstantInfo.value? (allowOpaque := true) confirms its proof term
--     never reaches Gtz.gtz_rank_two, against a POSITIVE CONTROL in which
--     Gtz.rank_three_of_the_two_residuals correctly does.
--   THE ALL-HEAVY WINDOW DROPS BY THE SAME ATOM, and this is the STRONGEST rank-three
--     reduction in the tree: Gtz.gtzWeightedAll_of_heavy_bounded reaches its cap through
--     Gtz.crystallization and that call is the ONLY place the cap enters -- the deflation
--     induction beneath it merely DECREASES the size -- so running it under
--     Gtz.crystallizationSharp gives Gtz.gtzWeightedAll_of_heavyVeroneseWindow and hence
--     Gtz.rank_three_of_heavy_six_three: rank three from the ALL-HEAVY (6,3) cell ALONE.
--     That is STRICTLY STRONGER than the plain arrow, because Gtz.GtzWeightedHeavy 6 3 is a
--     weaker hypothesis than Gtz.GtzWeighted 6 3, and it sharpens all three of
--     Gtz.rank_three_of_heavy_residuals (heavy at six AND seven), Gtz.rank_three_of_heavy_top
--     (heavy at seven) and Gtz.gtz_original_rank_three_of_heavy.  So the AllHeavy conjunct of
--     Gtz.IsSixThreeRefutationCandidate is not a restriction of the search but a property of
--     it: the whole rank-three conjecture now sits on all-heavy (6,3) designs.
--     AND THAT CHAIN IS INDEPENDENT OF SENGUPTA-PAUTOV.  Its size-five rung is discharged by
--     Gtz.gtzWeightedAll_two_of_walk rather than by the shipped Gtz.gtz_rank_two, so the
--     transitive walk from Gtz.rank_three_of_heavy_six_three reaches 39692 constants and
--     NEITHER Gtz.gtz_rank_two NOR Gtz.exists_dominating_pair_of_heavy, where the same walk
--     from Gtz.rank_three_of_the_two_residuals reaches both (POSITIVE CONTROL).
-- THIS PROVES NOTHING ABOUT (6,3).  It deletes the SECOND open cell of the rank-three
-- frontier and leaves the first exactly as open as it was: IsEmpty Gtz.SixThreeCrux is
-- untouched and remains the wall.  The frontier shrinks in COUNT, from two objects to one,
-- not in difficulty.
-- THERE IS NO ALL-HEAVY VARIANT OF THE ARROW ITSELF, and it should not be attempted -- which
-- is NOT in tension with the heavy WINDOW result above, since that one reruns the shipped
-- deflation induction under the sharper cap and never transports all-heaviness ALONG the
-- walk.  What fails is Gtz.GtzWeightedHeavy 6 3 -> Gtz.GtzWeightedHeavy 7 3: the reduced
-- atoms are scaled by sqrt(W) <= 1, so leverages SHRINK and all-heaviness is destroyed.  A
-- measured (7,3) design of three axis spikes and four whitened planar atoms, all leverages
-- above one, walks to W = 6/7 with support five and a reduced atom of leverage EXACTLY one
-- [exact rational, outside Lean].  So Gtz.gtzWeighted_seven_three_of_six_three_of_heavy is
-- not subsumed.
-- THE ARGUMENT HAS NO COMPLEX ANALOGUE, BY A DIMENSION COUNT: the stress exists because seven
-- rank-one symmetric matrices cannot be independent in Sym_3(R), of dimension six, whereas
-- Herm_3(C) has real dimension nine and 7 < 9 leaves seven complex atoms with NO stress at
-- all.  Same mechanism as Gtz.hermitianMomentFloor_lt_realMomentFloor, and consistent with
-- Gtz.complexGtzWeighted_six_three_fails: the arrow proved here is a REAL theorem and cannot
-- transport a false complex (6,3) into a complex (7,3).

import Gtz.Quantitative.SixThreeCruxPropagation

-- Gtz/Quantitative/SixThreeCruxPropagation.lean -- IsEmpty Gtz.SevenThreeCrux IS NOW DERIVED
-- RATHER THAN ASSUMED, so every terminus of the exclusion campaign loses its second open
-- antecedent.  Gtz.isEmpty_sevenThreeCrux_of_gtzWeighted_six_three does the work; the two
-- termini Gtz.gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidate_sharp and
-- Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate_sharp then stand on
-- the (6,3) BOX SEARCH ALONE, and Gtz.gtzWeightedAll_three_of_isEmpty_sixThreeCrux is the
-- two-crux assembly Gtz.gtzWeightedAll_three_of_isEmpty_cruxes on ONE crux.
-- NOTHING HERE APPROACHES IsEmpty Gtz.SixThreeCrux, which is still the wall and still open.
-- The (7,3) crux is not refuted either -- it is shown to be a CONSEQUENCE of the (6,3) cell,
-- so a counterexample hunt may now run at (6,3) exclusively and lose nothing.

import Gtz.Reduction.RankThreeFromSixThree

-- Gtz/Reduction/RankThreeFromSixThree.lean -- WHAT THE DELETED ANTECEDENT BUYS DOWNSTREAM.
-- Gtz/Quantitative/SixThreeCruxPropagation.lean spent the arrow on the two termini; this
-- spends it on everything else the tree had phrased at (7,3), at a PAIR of cells, or at a
-- DICHOTOMY.  Every theorem is a composition and every original is left untouched.
--   THE ALL-HEAVY MINIMISER DICHOTOMY COLLAPSES.  Gtz.exists_allHeavy_minimiser_of_not_rank_three
--     offers a minimising counterexample at (6,3) OR at (7,3); its (7,3) branch was reachable
--     only through the missing arrow, so Gtz.exists_allHeavy_minimiser_of_not_rank_three_sharp
--     hands back the (6,3) branch alone.  A counterexample hunt no longer has two shapes.
--   A THIRD CELL JOINS THE EQUIVALENCE CLASS, AND IT IS AT ANOTHER RANK.
--     Gtz.gtzWeighted_six_three_iff_seven_four: Naimark duality at m = 7 sends rank three up
--     to (7,4) via Gtz.gtzWeighted_seven_four_of_seven_three, and Gtz.gtzWeighted_of_spike
--     sends (7,4) back down to (6,3).  That loop did not close before.  The tree's lowest
--     rank-four entry into rank three was Gtz.gtzWeightedAll_three_of_eight_four; it is now
--     Gtz.gtzWeightedAll_three_of_seven_four, one size lower and an iff rather than an arrow.
--   THE DOUBLY-HEAVY AND LINE-COUNT RESIDUALS MOVE TO SIZE SIX.
--     Gtz.gtzWeightedAll_three_of_doublyHeavy_six_three and Gtz.gtzWeightedAll_three_of_sixLines
--     pose their narrowings on TWENTY triples instead of thirty-five.  Both ride
--     Gtz.rank_three_of_heavy_six_three; Gtz.gtzWeightedHeavy_six_three_of_doublyHeavy was
--     already in the tree at size six and had nowhere to go, because the only heavy-to-rank
--     arrow, Gtz.rank_three_of_heavy_top, starts at seven.
--   CRUXES DESCEND.  Gtz.isEmpty_sevenThreeCrux_of_isEmpty_sixThreeCrux and its contrapositive
--     Gtz.nonempty_sixThreeCrux_of_nonempty_sevenThreeCrux: any (7,3) crux is accompanied by a
--     (6,3) crux.  THE CONVERSE IS NOT PROVED and does not follow -- 
--     Gtz.nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three carries GtzWeighted 6 3 as a
--     hypothesis, so it cannot be run at a design that refutes it.  One direction only.
-- NOTHING HERE TOUCHES IsEmpty Gtz.SixThreeCrux.

import Gtz.Quantitative.OrthogonalEdgeSectors

-- Gtz/Quantitative/OrthogonalEdgeSectors.lean -- THE SIGN LAYER WITH ONE PAIRING ALLOWED TO
-- VANISH.  Gtz.residualSectors and Gtz.SixThreeCrux.linkWord_mem_residualSectors need all
-- FIFTEEN pairings nonzero and a crux supplies none of them; the vanishing branch had the
-- mathematics (Gtz.not_forall_coherent_of_orthogonalEdge and its sibling) but no aggregate,
-- and Gtz/Quantitative/SixThreeExclusionFrontier.lean recorded the consequence as PROSE --
-- "measured on the sector table outside Lean, one orthogonal edge leaves 840".  It is now a
-- theorem, Gtz.card_residualSectorsOrthEdgeZeroOne, and the branch is one decidable object.
--   WHAT MADE IT WORK WAS RELOCALIZING L2.  L1's cap
--     Gtz.card_le_three_of_forall_incoherent_through_base already took PER-EDGE nonvanishing;
--     L2's went through Gtz.exists_antiParityPartner_sixThree, whose hypothesis is GLOBAL.
--     Gtz.card_le_three_of_forall_coherent_through_base_local unpacks it --
--     Gtz.exists_isChartDual_sixThree is hypothesis-free and the two transport laws consume
--     one edge each -- and that is the step the branch was missing.  A base and a four-set
--     span five of six atoms, so a configuration avoids the edge exactly when the OMITTED
--     atom is 0 or 1: TEN of the thirty.  ORTH needed no repair; it was already local.
--   THE LEDGER, ALL BY decide +kernel: L1 alone 994, L2 alone 994, both 964, ORTH alone 896,
--     all three 840 -- against 842 in the nonvanishing branch.
--   L3 IS ABSENT AND MUST BE.  A matching edge carries the third lever only where
--     Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge applies, and that needs the edge's OWN
--     pairing nonzero, not merely its star; every perfect matching either contains {0,1} or
--     matches 0 elsewhere and then THAT edge's star runs through {0,1}, so the honest count of
--     usable matchings here is ZERO.  Nothing is lost --
--     Gtz.sectorCount_orthEdgeZeroOne_matchingThroughEdge_redundant grants L3 at the three
--     matchings through the vanishing edge anyway and finds it removes NO two-graph, a count
--     of zero and hence set containment rather than a cardinality coincidence.  But the FULL
--     fifteen-matching test must not be imported: Gtz.sectorCount_orthEdgeZeroOne_not_hasNoSaturatedMatching
--     counts 24 branch survivors it would exclude on matchings whose edges have a star through
--     {0,1}, so an unexamined reuse of the generic lever would report 816 instead of 840.
--   THE TWO RESIDUES ARE INCOMPARABLE, so 840 against 842 is a coincidence of size and NOT a
--     containment: Gtz.sectorCount_orthEdgeZeroOne_not_residual counts 72 two-graphs the
--     vanishing branch admits and the generic one forbids, and
--     Gtz.sectorCount_residual_not_orthEdgeZeroOne counts 74 the other way.
--   THE AGGREGATE.  Gtz.linkWordOf_mem_residualSectorsEdgeZeroOneFree places EVERY (6,3)
--     design inside one explicit 914-element object under FOURTEEN nonvanishing hypotheses
--     instead of fifteen, the pairing at {0,1} left completely free.  Dropping one hypothesis
--     costs 72 patterns and does not cost the lane.
-- THE EDGE IS NAMED and nothing here quantifies over WHICH pairing vanishes; the link word is
-- read at atom 0, so relabelling moves it and the fifteen sets are not translates inside one
-- encoding.  Two or more vanishing pairings are out of scope.  Like the generic branch, this
-- one DOES NOT EMPTY, so no sign-only argument cuts it either.

-- Gtz/Quantitative/OrthogonalEdgeSectors.lean, ADDENDUM -- DO NOT DO THE OTHER FOURTEEN.
-- The strength of the branch is in the edge being NAMED, and quantifying over which pairing
-- vanishes destroys almost all of it.  Measured outside Lean on the same encoding this module
-- mechanizes: all fifteen single-edge branches have cardinality exactly 840, as S(6)-equivariance
-- of the constraint set predicts, so one representative determines every count -- but the fifteen
-- SETS are pairwise distinct and their UNION is 992 of 1024, which also swallows
-- Gtz.residualSectors whole (992 again with the generic branch thrown in).  So the unconditional
-- reading, "exactly one pairing vanishes, at an unknown edge", would exclude 32 two-graphs where
-- the named-edge statement excludes 184, and the fourteen further clause sets it would cost are
-- not worth spending.  Their INTERSECTION is 192, and that is not a new object either: it is
-- exactly the two-graphs with no saturated star at any of the fifteen edges, the 192 already in
-- this campaign's ledger.  Proving edge-independence INSIDE Lean rather than measuring it needs
-- an ingredient the tree does not have -- an action of Equiv.Perm (Fin 6) on
-- Gtz.WeightedDesign 6 3 with transport of Gtz.tripleParity along it; Equiv.Perm appears in
-- Gtz/Design/LinePatternEnumeration.lean only as an abstract relabelling of PATTERNS.

import Gtz.Quantitative.ChartValueZeroLocus
-- Gtz/Quantitative/ChartValueZeroLocus.lean -- THE CHART-VALUE-ZERO LOCUS, and route C as ONE
-- named obligation.  Chart value zero is the ONLY level at which the chart-to-quadric bridge of
-- Gtz/Quantitative/ChartMultiplierSplit.lean is exact, so it is the only level at which the
-- design-side quadric machinery is even addressable from chart data.  This module mechanizes
-- what is true there.
--   THE HEADLINE, Gtz.not_saturatedAtom_of_chartValueZero: NO ATOM OF A VALUE-ZERO CHART
--     STATIONARITY DATUM IS SATURATED, at every size above one and every rank.  This completes a
--     trichotomy the tree had two thirds of.  The shipped Gtz.sq_value_add_weight_of_saturatedAtom
--     makes a saturated atom's eigenvalue value + t_c idempotent, hence 0 or 1.  At a NEGATIVE
--     value the root 0 survives, giving the shipped EQUATION
--     Gtz.weight_eq_neg_value_of_saturatedAtom_of_negativeValue, which
--     Gtz/Quantitative/ChartDisjointBlockExclusion.lean's header correctly calls rigidity and not
--     exclusion.  At value 1/2 the root 1 survives, which is that file's own two-atom witness.  At
--     value ZERO the root 0 asks for t_c = 0 against strict interiority and the root 1 asks for
--     t_c = 1 against any second positive weight, so BOTH die.  Both hypotheses are needed and the
--     tree witnesses each root elsewhere, so the exclusion is a property of the level and not of
--     the shape of the datum.  The census-facing form Gtz.not_hasSaturatedAtom_of_chartValueZero
--     removes from a covering class census exactly the classes with a saturated atom.
--     READ THE HYPOTHESIS.  This does NOT close the recorded chart-side saturated-atom wall, which
--     is a statement about a CRUX and a crux has value strictly NEGATIVE, never zero.  There the
--     four recorded attempts stand refuted exactly as before: the law is an equation, the weight is
--     -chartObjective, and Gtz.SixThreeCrux.weight_mem_window_of_saturatedAtom below only reads it
--     against the sharp window.  What is new is a DIFFERENT regime, the one the bridge is exact on.
--   THE TIE HALF, Gtz.not_posDef_subsetSum_sub_one_of_chartValueZeroAdmissible: admissibility at
--     level zero -- every rank-subset carrying a supported unit probe of nonpositive chart
--     quotient -- forbids a STRICT dominator, at every size and rank, with no stationarity bundle.
--     A strict dominator makes the projection block positive semidefinite (it dominates) with
--     nonzero determinant (Gtz.det_projectionBlock_sub_weightDiagonal rescales the design gap's
--     determinant by the positive weight product, and Gtz.det_gramGap_eq_det_transposeGap
--     identifies the two Gram gaps through Matrix.det_one_sub_mul_comm), hence positive definite,
--     hence strictly positive on the probe's nonzero restriction.
--   ROUTE C IS NOW ONE NAMED OBLIGATION.  Gtz.IsChartValueZeroLimit is the object a deformation
--     argument must produce -- a (6,3) design with a value-zero stationarity datum, admissible at
--     level zero, carrying a dominating triple, all-heavy and parallel-free -- and the two leaves
--     Gtz.HasChartValueZeroLimitAtEveryCrux and Gtz.HasNoChartValueZeroLimit compose into
--     IsEmpty Gtz.SixThreeCrux and hence Gtz.GtzWeighted 6 3.
--   AND THE SECOND LEAF IS THE SHIPPED HINGE.  Gtz.isTie_of_isChartValueZeroLimit shows the limit
--     object is an EXACT TIE -- its domination field is one half, the admissibility exclusion above
--     is the other -- and it has no parallel pair, so Gtz.hasNoChartValueZeroLimit_of_hingeHoldsAtSize
--     empties the class from Gtz.HingeHoldsAtSize 6 3.  Route C's second leaf is therefore not a
--     new question; it is the hinge, which is OPEN at six and which
--     Gtz.not_hingeHoldsAtSize_five_three proves FALSE at (5,3), so no size-generic argument
--     reaches it.
--   AND THE OBSTRUCTION IS LOCATED, Gtz.exists_isTie_allHeavy_not_hasParallelPair_fiveThree: one
--     size down the class "exact tie, all-heavy, no parallel pair" is INHABITED by the shipped
--     diamond, all three properties being theorems of the tree.  So any argument emptying
--     Gtz.IsChartValueZeroLimit from those three properties alone would prove something false at
--     (5,3), and whatever strength the leaf has beyond the plain hinge must come from the two
--     fields the diamond is not known to carry -- the value-zero stationarity datum and
--     admissibility at level zero.  That is where the next attempt should be aimed.
--   WHAT THE BRIDGE DOES AND DOES NOT BUY.  Gtz.exists_multiplier_of_chartValueZero packages the
--     three shipped bridge conclusions plus the gap-trace law, and
--     Gtz.one_le_leverageOf_of_chartValueZero derives NON-STRICT all-heaviness for free, so at value
--     zero Gtz.AllHeavy carries only the strict upgrade -- exactly the absence of unit-length atoms,
--     by Gtz.allHeavy_iff_forall_leverageOf_ne_one_of_chartValueZero.  But the quadric-side kills
--     Gtz.one_le_value_of_saturatedAtom, Gtz.rank_le_value_of_disjointPair_activeSubsetImage and
--     Gtz.three_le_card_activeSubsetImage_sixThree all consume the full
--     Gtz.IsQuadricStationaryData bundle, and the bridge manufactures only three of its
--     CONCLUSIONS -- never atomStationarity, activeSubset_card, tightDir_isEigenvector or
--     activeWeight_sum_one.  Gtz.exists_chartValueZero_bridge_and_dominates records the consequence
--     as a theorem: a genuine (6,3) design carries a value-zero datum, receives the whole package,
--     and DOMINATES.  Value zero plus the bridge contradicts nothing, and the value-zero class is
--     not a counterexample class -- it is the boundary.
--   PARALLEL-FREENESS IS INDISPENSABLE, Gtz.exists_chartValueZero_stationary_allHeavy_hasParallelPair:
--     delete it and the interface's other demands are met by the shipped split-tetrahedron datum,
--     whose atoms 2 ~ 3 and 4 ~ 5 repeat a tetrahedron direction.
--   THE NEGATIVE-VALUE READING, Gtz.SixThreeCrux.weight_mem_window_of_saturatedAtom and its (7,3)
--     twin: composing the shipped saturated-atom equation with the shipped sharp windows puts a
--     saturated crux atom's weight in (0, 4/27] at (6,3) and (0, 10/77] at (7,3).  The value-zero
--     exclusion is the limiting case, where the window closes on the endpoint interiority forbids.
--   NOT PROVED, AND IT IS THE HARD LEAF.  Nothing here produces a value-zero limit.  Every crux is
--     a global minimiser of the SAME Gtz.chartObjective over the SAME compact domain, so all cruxes
--     carry one value in [-4/27, 0) and no minimising sequence has values tending to zero: leaf one
--     is a deformation statement, not a subsequence extraction.  IsEmpty Gtz.SixThreeCrux is
--     untouched.

import Gtz.Reduction.StressConditionalWalk
-- Gtz/Reduction/StressConditionalWalk.lean -- THE STRESS-CONDITIONAL WALK, and the conic that
-- manufactures a stress.  Gtz.exists_rescaledReducedDesign spends its size hypothesis
-- rank*(rank+1)/2 < size in exactly ONE place -- manufacturing a Parseval-preserving direction out
-- of a finrank count -- so Gtz.exists_rescaledReducedDesign_of_stress takes that direction as a
-- HYPOTHESIS and runs at EVERY size, in particular at (6,3), where 3*4/2 = 6 leaves the count
-- nothing to say.
--   THE PAYOFF, Gtz.exists_dominating_sixThree_of_stress: a (6,3) design carrying ANY nonzero
--     stress is DOMINATED, with no open hypothesis.  The walk lands at size at most five and
--     Gtz.gtzWeighted_of_le_five closes it.  This is the transport of the reduction tool from the
--     cell it was built for onto the terminal cell of rank three.
--   THE GEOMETRY, Gtz.exists_stress_of_commonQuadric.  A stress is a dependency among the six
--     Veronese images inside the SIX-dimensional Sym_3(R); dually six vectors of a six-dimensional
--     space are dependent as soon as they all annihilate one functional, and the functionals are
--     the symmetric forms under the Frobenius pairing <g g^T, Q> = g^T Q g.  So a conic through all
--     six directions manufactures a stress, and Gtz.exists_dominating_of_commonQuadric turns it
--     into a dominating triple.  The proof never mentions hyperplanes: it appends Q to the six
--     images, applies the seven-in-six count Gtz.exists_dependency_of_symmetric_family, and pairs
--     the relation with Q, whose own coefficient dies against its nonzero Frobenius norm.
--   THE DEGENERATE CASE WITH NO CONIC VOCABULARY, Gtz.exists_dominating_of_twoPlanes: if every atom
--     is orthogonal to one of two fixed nonzero normals -- in particular if the six atoms split
--     into two COPLANAR TRIPLES -- the design is dominated.  The atoms may be pairwise
--     non-parallel, so Gtz.HasParallelPair does not see this; Gtz.not_hasParallelPair_of_no_stress
--     records the converse containment, that a parallel pair IS a stress.
--   NO COMPLEX ANALOGUE, and this is orientation prose rather than a theorem of the module.  Over C
--     the Veronese images are Hermitian and live in a NINE-dimensional real space, so six of them
--     carry no forced dependency -- the same dimension gap 6 = dim Sym_3(R) against
--     9 = dim Herm_3(C) that powers Gtz.hermitianMomentFloor_lt_realMomentFloor.

import Gtz.Quantitative.SixThreeStressExclusion
-- Gtz/Quantitative/SixThreeStressExclusion.lean -- A (6,3) CRUX CARRIES NO STRESS: the new crux
-- field, in three vocabularies.  A crux is not dominated, so
-- Gtz.exists_dominating_sixThree_of_stress gives Gtz.SixThreeCrux.stress_eq_zero at once, and its
-- six Veronese images are linearly independent in Sym_3(R) -- hence, there being exactly six of
-- them, a BASIS of it (Gtz.SixThreeCrux.linearIndependent_veronese).
--   GEOMETRIC, Gtz.SixThreeCrux.no_commonQuadric: THE SIX DIRECTIONS OF A (6,3) CRUX LIE ON NO
--     CONIC OF RP^2.  Strictly stronger than the shipped field hasNoParallelPair, which it reproves
--     as Gtz.SixThreeCrux.not_hasParallelPair_via_stress, and strictly stronger again by
--     Gtz.SixThreeCrux.not_twoPlanes, whose line-pair configurations carry no parallel pair at all.
--   ALGEBRAIC, Gtz.SixThreeCrux.det_hadamardSquareGram_ne_zero and .rank_hadamardSquareGram_eq_six:
--     the shipped cap Gtz.rank_hadamardSquareGram_le_six is ATTAINED at a crux.  A nonvanishing
--     determinant is a legitimate saturation polynomial for an elimination run.
--   PARAMETRIC, Gtz.SixThreeCrux.weight_unique: Parseval has a UNIQUE solution at a crux, so the
--     weights are DETERMINED by the atoms and six unknowns leave any search over the crux locus.
--   THE BRIDGE BETWEEN THE VOCABULARIES is the Frobenius identity
--     Gtz.trace_transpose_mul_self_momentCombination, which reads the Hadamard-square Gram's
--     quadratic form as a squared Frobenius norm and upgrades the shipped one-way
--     Gtz.hadamardSquareGram_mulVec_eq_zero to the equivalence
--     Gtz.hadamardSquareGram_mulVec_eq_zero_iff: the kernel of the Hadamard square IS the syzygy
--     space, not merely a superset.
--   WHERE REALNESS IS SPENT, and this is orientation prose rather than a theorem.  The exclusion is
--     inherited from the walk, whose landing theorem Gtz.gtzWeighted_of_le_five is FALSE over C --
--     Gtz.complexGtzWeighted_iff_size_le_rank_add_one pins the complex rank-three threshold at size
--     at most four.  The complex refuting witness DOES carry a stress (its antipodal spike pair has
--     equal Hermitian images), so the walk RUNS over C and concludes nothing.

import Gtz.Quantitative.ChartSecondOrder
-- Gtz/Quantitative/ChartSecondOrder.lean -- SECOND-ORDER DATA AT A CHART MINIMISER, the first in
-- the tree.  Everything previously extracted from Gtz.SixThreeCrux.isChartMinimiser was FIRST
-- order; a crux is a GLOBAL minimiser, so every feasible curve carries a second-order inequality
-- too, and this module extracts the weight-slice half of that family.
--   WHY THE WEIGHT SLICE.  Gtz.chartDomain is a PRODUCT, so at a fixed chart the weights range over
--     the whole simplex and Gtz.chartPointGap is AFFINE there; the perturbed block is M - step * D
--     with D the direction's restricted diagonal.  The Grassmannian directions are NOT touched --
--     the projection variety contains no line, so they carry curvature this module never sees.
--   THE MECHANISM IS MARGIN-FREE, Gtz.not_posSemidef_sub_smul_of_mulVec_ne_zero: if the first-order
--     effect vanishes at a tight vector but the perturbation MOVES that vector, then
--     M - step * D fails to be positive semidefinite for EVERY nonzero step, both signs, every
--     size.  Exact algebraic non-definiteness, not a Taylor estimate, so no inequality carrying
--     slack appears anywhere in the chain.
--   THE OTHER BLOCKS ARE HELD BY RAYLEIGH ALONE, Gtz.lambdaMinMat_sub_smul_lt_of_lt: an INACTIVE
--     block sits strictly below the value already and stays there as long as the step does not eat
--     its own gap.  That is an explicit finite family of strict inequalities, satisfied for every
--     small enough step but SUPPLIED as the hypothesis hstepSmall rather than derived -- turning it
--     into an existential over the step is the one analytic step this module does not take.  So
--     Gtz.chartObjective_lt_of_perturbedWeight uses no continuity anywhere, and the ACTIVE half
--     carries no margin at all.  Gtz.lambdaMinMat_sub_smul_le_of_dotProduct_zero records the flat
--     special case, where the condition collapses to inactivity itself.
--   THE DERIVED FACT AT A CRUX, Gtz.SixThreeCrux.exists_tight_annihilated_of_flatDirection: no
--     feasible weight direction can be flat at every ARGMAX block AND move every active tight
--     vector -- some argmax block has its tight vector ANNIHILATED, vanishing at first order not
--     being enough.  This is the weight-slice second-order condition, mechanized.
--   THE TIE-RIGIDITY CERTIFICATE route C consumes, Gtz.eq_zero_of_flatDirection_of_span_top: when
--     the first-order functionals SPAN there is no flat direction at all, the condition above is
--     vacuous and the point is weight-slice rigid.  The check is a rank computation on the
--     eigen-square rows.  Its contrapositive Gtz.span_ne_top_of_card_add_one_lt, and the count
--     Gtz.exists_flatDirection_of_card_add_one_lt behind it, supply a flat direction from the
--     member count alone -- the all-ones vector consuming the extra dimension.
--   NOT PROVED, and recorded rather than hidden: an unconditional floor on the argmax family beyond
--     the shipped Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily.  Turning the derived fact into
--     5 <= |A| needs, on top of what is here, that a real vector space is not a finite union of
--     proper subspaces, plus the support analysis of the tight vectors.
--   THE MECHANISM IS FIELD-BLIND, again orientation prose: every step runs verbatim over C with
--     u u^* in place of u u^T, so nothing here can close the cell alone.

import Gtz.Quantitative.DesignQuadraticFloors
-- Gtz/Quantitative/DesignQuadraticFloors.lean -- THE MOMENT DICTIONARY, and two quadratic-form
-- floors.  Gtz.dominates_iff_forall_moment_ge turns Gtz.Dominates into "the moment image MISSES the
-- open half-space sum_{c in C} y_c < |x|^2", and Gtz.not_dominates_iff_exists_moment_lt exhibits
-- the failure witness as a single probe direction.  Pinning the reading down as a theorem also
-- settles what it can see: each condition is the minimum of a LINEAR functional over the moment
-- body, hence a condition on its CONVEX HULL alone -- never on the image's topology, its
-- self-intersections, or the dimension of the domain it came from.
--   THE UNIFORM LOEWNER FLOOR, Gtz.posSemidef_bound_smul_subsetSum_sub_one: if every weight is at
--     most bound, the full unweighted atom sum dominates (1/bound) . 1.  Sharpens the shipped
--     Gtz.posDef_fullExcess from "positive definite" to an explicit constant, and its equality case
--     is the shipped Gtz.subsetSum_univ_eq_size_smul_one_of_weight_eq_sizeInv.
--   THE PAIRING-MASS FLOOR, Gtz.leverage_lt_sum_sq_atomPairing_compl: wherever the co-singleton at
--     an atom STRICTLY dominates, that atom's leverage is outweighed by the squared pairings from
--     it to all the others.  Feed the atom itself into its co-singleton's positive-definite gap.
--     Strictly stronger than what Parseval alone gives -- the shipped bilinear identity
--     Gtz.sum_weight_mul_atomPairing_mul_atomPairing yields the same bound discounted by one minus
--     the atom's share -- and the hypothesis cannot be dropped: an orthogonal design has vanishing
--     off-diagonal pairings and positive leverages, and there the co-singleton is singular.  A
--     (6,3) crux carries Gtz.HasStrictlyDominatingCoSingletons, so the floor holds at all six of
--     its atoms.  Both floors are degree two in the Gram entries, hence usable by an algebraic
--     search.

import Gtz.Quantitative.SixThreeFrontierSharp
-- Gtz/Quantitative/SixThreeFrontierSharp.lean -- THE SHARPENED (6,3) FRONTIER, and the campaign's
-- one-antecedent terminus.  Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateSharp
-- takes a SINGLE open hypothesis -- that no (6,3) weighted design satisfies an explicit design-level
-- predicate -- and returns GtzOriginal atomCount 3 for every positive atomCount.  The shipped
-- Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate needed that search AND
-- IsEmpty Gtz.SevenThreeCrux; the stress walk deleted the second, and Gtz.rank_three_iff_six_three
-- states the collapse as an iff.  Read plainly the terminus quantifies over ALL rank-three
-- configurations of ANY size; what is NOT proved, here or anywhere in this tree, is that the box is
-- empty.  GtzWeighted 6 3 and IsEmpty Gtz.SixThreeCrux remain OPEN, and every conjunct below is a
-- necessary condition on a hypothetical counterexample, never an exclusion of one.
--   Gtz.SixThreeCrux.frontierSharp -- the layer Gtz.SixThreeCrux.frontier did not have, EXTENDING it
--     rather than replacing it, so the full frontier is the two theorems conjoined.  The stress layer
--     (a crux carries no stress, so its six Veronese images are a BASIS of Sym_3(R)) with its
--     algebraic face det(hadamardSquareGram) != 0 -- a single polynomial NONVANISHING, hence a
--     saturation variable an algebraic search can use -- and its geometric face, no conic of RP^2
--     through the six directions.  The quadratic floor at every atom.  All-heaviness as a strictly
--     positive chart gap diagonal, and the first characteristic coefficient strictly positive at all
--     twenty triples, which cuts admissibility to two branches per triple rather than three.
--   Gtz.IsSixThreeRefutationCandidateSharp -- the shipped box plus the new DESIGN-LEVEL conjuncts,
--     no chart in any of them.  THE TWO BOXES ARE THE SAME BOX, and
--     Gtz.isSixThreeRefutationCandidateSharp_iff proves it, so that nobody reads the sharpened
--     frontier as a reduction of the search space: every new conjunct is a CONSEQUENCE of the
--     shipped box, a stress or a common conic each producing a dominating triple that the box's own
--     no-domination clause forbids, and the quadratic floor following from all-heaviness with the
--     strictly dominating co-singletons.  What it buys is a reduction of the WORK at each point of
--     an unchanged box -- four extra facts made explicit, one a polynomial nonvanishing -- and
--     Gtz.gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidateSharp shows emptying it
--     still suffices.
--   THE ROUTE-BY-ROUTE LEDGER lives in the module docstring: A landed as a reduction; B walled
--     structurally, the chart-KKT variety being positive-dimensional so real solving never starts;
--     C landed in part with leaf two identified as the shipped Gtz.HingeHoldsAtSize 6 3 and leaf one
--     open and NOT a compactness extraction; D refuted as a cell, its tool surviving as the stress
--     layer; E killed, every domination condition being the minimum of a LINEAR functional and hence
--     blind to everything but a contractible convex hull; F landed in part, open, and field-blind.
--   THE SINGLE NEXT QUESTION IS UNCHANGED: a positive lower bound on |chartObjective| at a crux.
--     What this run adds is where NOT to look -- the stress layer is SLACK at the wall, the
--     closest-to-crux all-heavy configuration being stress-free with a healthy margin while the
--     exact ties are the stress-carrying objects.  Measured outside Lean, and recorded as such.

import Gtz.Quantitative.ChartDiamondValueZero
-- Gtz/Quantitative/ChartDiamondValueZero.lean -- THE DIAMOND CHART DATUM AT VALUE ZERO, five atoms.
-- Gtz.IsChartStationaryData is a HYPOTHESIS bundle of thirteen fields, and which SIZES inhabit it is
-- decided by none of them.  Before this file the bundle was known inhabited at four atoms
-- (Gtz.chartTetraProjection, Gtz.chartCorankOneProjection) and at six (Gtz.chartSplitSixProjection,
-- Gtz.chartTwoBlockTripleProjection); at FIVE it was measured outside Lean and never mechanized.
--   Gtz.diamondChart_isChartStationaryData -- all thirteen fields at five atoms, rank three, value
--     exactly zero, eight active triples, chart exact in Q(sqrt 6), every atom strictly heavy
--     (leverages 2 and 13/4).  Gtz.exists_isChartStationaryData_five_value_eq_zero is the size-five
--     inhabitation as an existence statement, the sibling of the shipped
--     Gtz.exists_isChartStationaryData_weight_ne at four atoms.
--   WHY IT MATTERS.  A value-zero obligation is size-non-generic exactly when a five-atom object can
--     already satisfy it, and this is that object.  Any strengthening of the value-zero leaves that
--     hopes to be size-generic has to survive it.
--   THE MULTIPLIER IS NOT TRIVIAL.  Its five eigenvalues are 1/20, 1/20, 1/10 on the chart's range
--     and 8/15, 4/15 on its kernel, so Gtz.diamondChartProjection_mul_multiplier_comm is a genuine
--     commutation rather than an artefact of a scalar assembly -- unlike the (6,3) octahedron, whose
--     assembly is I/6.  Nor is the multiplier family determined by the point: a whole segment of
--     multipliers satisfies all thirteen fields, and Gtz.diamondChartMultiplierWeight is the unique
--     member whose ratio multiplier/normSquare is the constant 1/120.
--   THE ARITHMETIC IS SPECTRAL, NOT TABULAR, and that is reusable.  The chart is a sum of rank-one
--     atoms of PAIRWISE-ORTHOGONAL explicit directions, never an entry table, so symmetry,
--     idempotence, the trace and the commutation carry no matrix index at all --
--     Gtz.mul_atomMatrix_of_mulVec_smul and Gtz.atomMatrix_mul_of_mulVec_smul turn "this vector is an
--     eigenvector" into "this matrix absorbs that atom" on either side.  The entry-table definition
--     was tried first and abandoned: inside this import environment its ext/fin_cases idempotence
--     proof does not finish at four million heartbeats, where the same proof over plain Mathlib costs
--     sixteen seconds.
--   ADMISSIBILITY TOO.  Gtz.diamondChart_isChartArgmaxValue proves the second chart-side field: no
--     triple beats the value.  Eight of the ten triples attain zero exactly, carrying their own tight
--     direction, and the two triangles sit at -1/5.  So the diamond is the COMPLETE chart-side
--     value-zero object at five atoms, and both size-five facts a size-generic value-zero obligation
--     would have to survive are theorems rather than measurements.
--   ONE SIZE- AND RANK-GENERIC BRICK RIDES ALONG.  Gtz.dotProduct_chartStationaryGap_mulVec_tightDir:
--     a tight direction's Rayleigh quotient against the gap IS the value.  The bundle gives the
--     eigen-equation coordinatewise ON the subset and vanishing OFF it; together they pin the
--     quotient, and nothing in Gtz.ChartStationary said so.  It is the pointwise content behind
--     trace (Xi * W) = value, and this campaign adds by extension only, so it is stated here.
--   CONIC VACUITY AT FIVE ATOMS.  Gtz.exists_commonQuadric_of_five_atoms: dim Sym_3(R) = 6 > 5, so
--     EVERY five-atom family in R^3 lies on a conic.  Strengthening a value-zero or tie-freeness
--     obligation by "the atoms admit no common quadric" therefore makes it unfalsifiable at (5,3) --
--     the diamond's refutation of the plain hinge would evaporate, and so would every scrap of
--     evidence FOR the strengthened form.  A conic-strengthened hinge is a SIZE-SIX question.
--     Contrast Gtz.SixThreeCrux.no_commonQuadric, where the same count is 6 = 6 and the conclusion
--     reverses.
--   WHAT IS NOT HERE.  The bridge to Gtz.projectionOfDesign Gtz.diamondDesign, which needs
--     whitener * whitenerᵀ = (fullLaplacian)⁻¹; without it the three DESIGN-side fields of
--     Gtz.IsChartValueZeroLimit -- a dominating triple, AllHeavy, no parallel pair -- are not reached.

-- SECOND ORDER: THE STEP, THE CURVATURE, AND THE COMPRESSION FORM.  Gtz.ChartSecondOrder names
-- three things it does not carry; this module carries all three.
--   THE STEP, DERIVED.  Gtz.exists_pos_step_feasible_and_gapPreserving manufactures, at any chart
--     point with strictly positive weights, a strictly positive step that keeps the weights
--     nonnegative AND leaves every inactive block's own gap unspent.  Those are exactly the slots
--     that Gtz.chartObjective_lt_of_perturbedWeight and
--     Gtz.SixThreeCrux.exists_tight_annihilated_of_flatDirection SUPPLY rather than derive -- the
--     shipped docstring says so in as many words.  The construction is a finite minimum and nothing
--     else: the shipped Gtz.exists_pos_le_forall_mem for the two floors, the shipped
--     Gtz.chartWeightCap for one cap covering every block and every unit vector at once.  No
--     continuity, no compactness, no limit.
--   THE CONSUMER FORM.  Gtz.SixThreeCrux.exists_tight_annihilated_of_flatWeightDirection: a flat
--     weight direction at a crux annihilates the tight vector of SOME argmax block, with no side
--     condition beyond flatness.  Gtz.eigenSquareRow_dotProduct joins it to the shipped
--     flat-direction producer Gtz.exists_flatDirection_of_card_add_one_lt, whose functionals are
--     plain vectors.  Distinct from Gtz.exists_chartTangentCurve_descent, which is FIRST order and
--     needs every active slope strictly negative; this is the complementary flat case.  Read
--     through full support, Gtz.SixThreeCrux.exists_argmax_direction_eq_zero_of_flatWeightDirection
--     says a flat direction VANISHES on some argmax block -- the shape an index argument consumes,
--     but NOT the index theorem, which additionally needs that a real vector space is not a finite
--     union of proper subspaces.  The shipped floor stays Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily.
--   THE GRASSMANNIAN HALF.  Gtz.trace_mul_grassmannAcceleration computes the curvature
--     Gtz.ChartSecondOrder declares out of scope: trace (Xi A) = -2 trace (Xi (2P - 1) B B) for any
--     curve of projections, so it depends on the VELOCITY alone and the free part of the
--     acceleration cancels (Gtz.trace_assembly_mul_acceleration_eq_of_sameVelocity).
--     Gtz.trace_assembly_mul_chartStationaryGap is a COROLLARY of the shipped
--     Gtz.trace_projection_mul_multiplier_of_isChartStationaryData, not a second proof of it.
--     HONEST SIGN: at a crux the value is negative, so the averaged curvature trace is POSITIVE --
--     the Grassmannian directions are stabilising and cannot by themselves contradict minimality.
--     NON-VACUITY, discharged before anything is built on the identity:
--     Gtz.blockDiagonal_velocitySquare_of_grassmannTangent plus
--     Gtz.exists_acceleration_of_blockDiagonal_velocitySquare solve the curve constraint at EVERY
--     Grassmannian tangent velocity, and Gtz.exists_grassmannCurvature_datum_nontrivial exhibits an
--     explicit instance with nonzero velocity and nonzero conclusion.
--   THE COMPRESSION FORM.  Gtz.tightCompression is the right first-order object at a MULTIPLE least
--     eigenvalue, where the scalar test u . D u is wrong (the Gtz.icosaDesign trap).
--     Gtz.mulVec_eq_zero_of_posSemidef_of_tightCompression_eq_zero generalises
--     Gtz.mulVec_eq_zero_of_posSemidef_of_dotProduct_zero to a frame and asks nothing of it --
--     not orthonormality, not injectivity.  Gtz.tightCompression_replicateCol_eq_zero_iff is the
--     simple-case equivalence.
--   FIELD-BLIND, as the whole second-order layer is: every step runs verbatim over C.
import Gtz.Quantitative.ChartSecondOrderStep

-- THE INDEX FLOOR ON THE ARGMAX FAMILY.  Gtz.Quantitative.ChartSecondOrder states, in its own
-- words, that turning its second-order condition into 5 <= |A| "needs, on top of what is here,
-- that a real vector space is not a finite union of proper subspaces, plus the support analysis
-- of the tight vectors", and Gtz.Quantitative.ChartSecondOrderStep repeats the reservation twice.
-- This module supplies both ingredients and lands the floor.
--   THE UNION-OF-SUBSPACES LEMMA WAS NOT MISSING, ONLY UNLOCATED.  It is Mathlib's
--     Subspace.exists_eq_top_of_iUnion_eq_univ (Mathlib/GroupTheory/CosetCover.lean), stated over
--     any INFINITE division ring.  Gtz.exists_le_of_forall_exists_mem packages it in the form a
--     covering argument consumes -- a submodule each of whose members lies in one of finitely many
--     submodules lies wholly inside one of them -- by transporting the cover into the submodule.
--   THE COUNT.  Gtz.exists_flatPair_of_card_add_one_lt produces two flat directions separated by a
--     pivot coordinate, so their independence is exhibited rather than computed;
--     Gtz.SixThreeCrux.exists_argmax_le_vanishingSubmodule upgrades the shipped escape from "each
--     flat direction vanishes SOMEWHERE" to "they all vanish on ONE common argmax block"; and
--     Gtz.eq_zero_of_vanishing_of_sumZero_of_rowFlat kills the pair on the three atoms left over,
--     using a THIRD argmax block whose eigen-square row is non-constant there.  The third block
--     exists because Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily already puts three in the
--     family and {C, C complement} has only two members, so the proof CONSUMES the shipped floor.
--   WHAT THE MULTIPLIER LAYER BUYS, PRICED EXACTLY.  A constant assembly diagonal exhibits the
--     all-ones vector as a multiplier combination of the eigen-square rows, so a flat direction is
--     automatically feasible for the simplex (Gtz.sum_eq_zero_of_flat_of_assemblyDiagonal).  That
--     frees one functional and is the whole difference between the two landed floors:
--     Gtz.SixThreeCrux.four_le_card_chartArgmaxFamily_of_fullSupport without it, and
--     Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_assemblyDiagonal with it.
--   THE HYPOTHESES, AND WHY THEY ARE HYPOTHESES.  Both floors carry what the shipped escape
--     carries: a unit tight eigenvector at EVERY one of the twenty triples, and FULL SUPPORT.
--     Full support is what turns annihilation into vanishing; the honest ladder is |A| >= 2 + s
--     with s the smallest tight support, and only s = 3 is proved here.  The SUPPORT-TWO rung
--     needs a different proof -- three independent flat directions and a rank-two kill -- and is
--     not built.  The assembly identity is a hypothesis because the shipped
--     Gtz.SixThreeCrux.exists_multiplier_isChartStationaryData supplies a constant diagonal for ITS
--     OWN tight directions at the argmax blocks only, while the escape needs one at every triple;
--     Gtz.assemblyDiagonal_of_isChartStationaryData_of_rowEq and
--     Gtz.eigenSquareRow_eq_mul_self_of_support say exactly which compatibility closes that gap,
--     and it can fail at a MULTIPLE least eigenvalue.
--   NON-VACUITY, discharged before the floors are built:
--     Gtz.exists_twoAtomKill_datum_nontrivial satisfies every side condition of the kill together
--     with a NONZERO direction, and Gtz.exists_assemblyDiagonal_datum_nontrivial realises the
--     constant assembly diagonal at a two-block (6,3)-shaped family.
--   THE MEASURED FLOOR IS NOT ASSUMED.  Numerical campaigns report no admissible chart-stationary
--     point below eight argmax blocks; that is a measurement with a known component bias and is
--     proved nowhere.  It appears only as the explicit, undischarged hypothesis of
--     Gtz.SixThreeCrux.six_le_card_chartArgmaxFamily_of_assemblyDiagonal_of_ne_five.
--   FIELD-BLIND, as the whole second-order layer is: every step runs verbatim over C.
import Gtz.Quantitative.ChartArgmaxIndexFloor

-- Gtz/Reduction/ConverseBridge.lean -- THE MISSING ARROW: classical GTZ implies the weighted form,
-- so the campaign's frame is an EQUIVALENCE rather than a one-way reduction.
--   WHAT WAS MISSING.  Gtz.original_of_weighted and Gtz.original_of_weighted_single run one way,
--     weighted ==> original, via Gtz.rowDesign at the uniform weight 1/n.  Nothing ran the other
--     way: no theorem in the tree took Gtz.GtzOriginal as a HYPOTHESIS.  So a weighted (6,3)
--     counterexample did not, in the kernel, refute the 1997 conjecture.  It does now.
--   THE HEADLINE.  Gtz.gtzWeightedAll_iff_forall_gtzOriginal : GtzWeightedAll k is EQUIVALENT to
--     "for every positive n, GtzOriginal n k".  In counterexample form,
--     Gtz.exists_not_gtzOriginal_of_forall_not_dominates turns any failing (m,k) design into an
--     explicit size N at which the literal 1997 statement fails.
--   THE FOUR STEPS.  (1) ROUNDING, the only analytic step: non-domination is a STRICT inequality
--     at a witness probe, there are finitely many subsets, and ONE archimedean choice of scale
--     preserves all of them at once under rounding the weights to floor(scale*t_c).  No continuity,
--     no compactness, no Lipschitz constant -- Gtz.continuous_designMargin and the MarginContinuity
--     machinery are NOT used, and whether a topological route would also close is untested.
--     (2) WHITENING: rounded weights break Parseval, and one invertible congruence repairs it;
--     because Gtz.Dominates is a congruence statement the congruence cancels on both sides, so
--     domination of the repaired design is exactly the RAW Loewner comparison S_C >= F and no
--     matrix square root is built.  (3) REPLICATION to the flat weight, where a k-subset either
--     repeats an atom -- killed by the shipped Gtz.not_dominates_of_repeated_atom_general -- or is
--     a faithful copy of a k-subset of the original.  (4) READING OFF THE MATRIX on the uniform
--     slice, where Gtz.scaledAtomRows inverts Gtz.rowDesign.
--   DOWNSTREAM, three rank-three termini stop being sufficient conditions and become
--     CHARACTERISATIONS of the 1997 conjecture: Gtz.isEmpty_sixThreeCrux_iff_gtzOriginal_rank_three,
--     Gtz.nonempty_sixThreeCrux_iff_not_gtzOriginal_rank_three, and
--     Gtz.forall_not_isSixThreeRefutationCandidateSharp_iff_gtzOriginal_rank_three.
--   AND AT EVERY RANK.  Gtz.gtzWeighted_veroneseTop_iff_forall_gtzOriginal composes the arrow with
--     the crystallization Gtz.gtzWeightedAll_of_veroneseTop: the single cell k(k+1)/2 decides the
--     1997 conjecture at rank k both ways.  Its rank-three instance IS the six-three statement
--     (3*(3+1)/2 = 6 on Nat), so those two are not independent facts; rank four is new.
--   REUSE RATHER THAN RE-PROOF.  The whitened design is the shipped Gtz.whitenedFamilyDesign with
--     Gtz.whitenedDesign_subsetSum_eq and Gtz.sum_atomMatrix_conj; the atom count is the shipped
--     Gtz.size_pos_of_design.  Only the domination EQUIVALENCE is new, and its hypothesis is bare
--     positive definiteness where Gtz.exists_whitenedDesign_of_framePinched demands the pinch.
--   HONEST SCOPE.  The construction is SIZE-CHANGING: a counterexample at (m,k) produces one at
--     (N,k) with only N >= m guaranteed, and N is not effective -- it comes from exists_nat_gt off
--     the per-gate ratios slack/gapValue.  NOTHING here proves or disproves a fixed-size arrow
--     GtzOriginal n k ==> GtzWeighted n k.  That is all the equivalence needs, since both sides
--     quantify over all sizes.
--   NON-VACUITY (P4) is checked at build time by five unnamed examples, two of which reprove
--     shipped weighted theorems by the NEW route off the ORIGINAL rank-one and rank-two statements.
import Gtz.Reduction.ConverseBridge

-- Gtz/Quantitative/EdgeOrbitSectors.lean -- THE VANISHING PAIRING AT AN UNKNOWN EDGE: the
-- named-edge sign branch becomes edge-independent by relabelling, not by fifteen case sets.
--   WHAT THE NAMED-EDGE BRANCH ASKED FOR.  Gtz/Quantitative/OrthogonalEdgeSectors.lean proves
--     the vanishing branch only at the NAMED edge {0,1}, and its header says the general case
--     "needs an ingredient the tree does not have: an action of Equiv.Perm (Fin 6) on
--     Gtz.WeightedDesign 6 3 together with the transport of Gtz.tripleParity along it", while
--     warning that a successor "should not spend the fourteen further clause sets it would take".
--     That sentence is half STALE and half superseded, and the halves are worth separating.
--     The ACTION half was already FALSE WHEN WRITTEN: Gtz.relabelDesign is in the TRACKED HEAD
--     version of Gtz/Ties/SelectionObstruction.lean, while OrthogonalEdgeSectors.lean is one of
--     the modules written on top of that HEAD, so its companion claim that Equiv.Perm "appears
--     in Gtz/Design/LinePatternEnumeration.lean only as an abstract relabelling of PATTERNS,
--     never as an action on designs" was already wrong -- the action was one directory away.
--     The TRANSPORT half was accurate: no sign-layer transport existed anywhere, and that is
--     what is supplied here.  Either way no clause set is spent.
--   THE ACTION WAS ALREADY SHIPPED.  Gtz.relabelDesign (Gtz/Ties/SelectionObstruction.lean) has
--     carried Gtz.subsetSum_relabelDesign and Gtz.dominates_relabelDesign_iff since before this
--     campaign, and Gtz/Design/PrimitiveTightClassification.lean already transports
--     Gtz.atomBracket, Gtz.IsTie and Gtz.HasLinePattern along it.  Only the SIGN layer was
--     missing, and Gtz.atomPairing_relabelDesign, Gtz.edgeSign_relabelDesign and
--     Gtz.tripleParity_relabelDesign are each `rfl` -- those three functions are built from one
--     another by formulas that never mention an index.  Gtz.allHeavy_relabelDesign_iff completes
--     the layer on the design side: a consumer of the orbit form receives a RELABELLED design,
--     and that is what says the crux field Gtz.SixThreeCrux.isAllHeavy survives the move.
--   THE HEADLINE, in orbit form.  Gtz.exists_relabel_linkWord_mem_residualSectorsOrthEdgeZeroOne:
--     a design whose pairings are nonzero away from ONE edge, wherever that edge is, relabels
--     into the SAME 840-element object the named-edge branch produces.  The witness is explicit
--     (Gtz.pairPerm, two transpositions) and the statement returns it together with the two
--     equations that identify it.  Gtz.exists_pairPerm is the two-point transitivity behind it.
--   WHY RELABELLING BEATS FORGETTING.  In the relabelled frame 184 two-graphs stay forbidden; in
--     the design's own frame only 32 do.  Relabelling does not forget WHERE the pairing vanishes,
--     which the named-edge header identifies as where all the information sits -- it moves the
--     label instead.
--   THE EDGE-FORGETTING FORM, for a consumer who cannot relabel.  Gtz.relabelLinkWord moves a
--     two-graph rather than a design and Gtz.linkWordOf_relabelDesign says the two agree, so the
--     fifteen branches and the generic branch have a computable union:
--     Gtz.card_unionEdgeBranchSectors = 992 by decide +kernel, and
--     Gtz.linkWordOf_mem_unionEdgeBranchSectors places every design with at most one vanishing
--     pairing inside it WITH NO RELABELLING IN THE CONCLUSION.  This mechanizes two measurements
--     of the named-edge header at once -- the fifteen-fold union is 992, and it is still 992 with
--     the generic branch thrown in, which is how the definition here is written.
--   SELF-TEST OF THE ENCODING.  Gtz.relabelLinkWord_pairPerm_zero_one: at the canonical edge the
--     relabelling is the identity and so is the induced action, over all 1024 two-graphs; hence
--     Gtz.edgeBranchSectors_zero_one identifies the canonical branch with the shipped set.
--   WHAT IS NOT HERE.  The UNIFORM per-edge cardinality over all thirty ordered edges is NOT
--     landed: it was built and measured at over two minutes of kernel time, and was dropped
--     rather than charged to every future build.  Gtz.card_edgeBranchSectors_zero_two and
--     Gtz.card_edgeBranchSectors_two_three confirm the measured 840 at the two shapes a
--     relabelling can take -- an edge sharing an atom with {0,1} and an edge disjoint from it.
--   THE RESIDUE DOES NOT SHRINK.  992 is larger than the 842 of the nonvanishing branch, not
--     smaller, and nothing here approaches IsEmpty Gtz.SixThreeCrux.  What the orbit form removes
--     is the fifteen-fold case split, not the residue.
--   NON-VACUITY (P4).  A hypothesis quantifying over an UNKNOWN edge could in principle be
--     satisfiable at no design at all, so it is discharged rather than assumed:
--     Gtz.hasAtMostOneVanishingPairing_icosaDesign, off the shipped
--     Gtz.icosaDesign_atomPairing_sq_of_ne, and the concrete consequence
--     Gtz.linkWordOf_icosaDesign_mem_unionEdgeBranchSectors.
import Gtz.Quantitative.EdgeOrbitSectors

-- GAP 7, THE HINGE AT SIX POINTS, ATTACKED ON BOTH OF ITS TWO INPUTS.
--   Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree reduces
--   Gtz.HingeHoldsAtSize 6 3 to exactly two things: the combinatorial completeness of
--   Gtz.linePatternListSix, and one tie-freeness obligation per non-near-pencil entry of
--   Gtz.lineFamiliesSix.  Two modules, one per input.  NEITHER INPUT IS DISCHARGED.
--
--   Gtz.Design.LinePatternSixCases -- THE ENUMERATION (gap 7a).  Purely combinatorial: no
--     design, no Parseval, no bracket, no real number, because
--     Gtz.patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete already removed the
--     analysis upstream.  FOUR of the nine isomorphism classes are discharged, ordered by
--     longest line -- #0 no dependent triple, #1 one three-point line, #6 one four-point
--     line, #8 the near pencil.  The residual splits along the largest line into
--     Gtz.LinearSpaceFourPointLineCasesSix (ONE class, #7: a four-point line with a
--     dependent triple outside it) and Gtz.LinearSpaceThreePointLineCasesSix (FOUR classes,
--     #2 through #5: no four-point line, at least two three-point lines).  Every route to
--     the enumeration still takes those as explicit undischarged hypotheses; the
--     contribution is that they cover five classes and not nine.  The coarser
--     Gtz.LinearSpaceMultiLineCasesSix (six classes) and Gtz.LinearSpaceMiddleCasesSix
--     (seven) are kept as the shallower cuts and everything stated against them is derived.
--     The reusable half is the transport kit: Gtz.lineFamilyPattern_map_iff,
--     Gtz.agreesOnDistinctTriples_comp_relabel_of_forall,
--     Gtz.isSpanningLinearSpacePattern_comp_relabel, the axiom-free
--     Gtz.agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete, and the case closer
--     Gtz.exists_relabel_agreesOnDistinctTriples_of_labelledFamily, which lets a structural
--     case name six labels and never write an Equiv.Perm.  #1 and #6 are the two worked
--     templates; a further case differs only in which lines it names.
--
--   Gtz.Quantitative.HingeStressNarrowing -- THE LEDGER (gap 7b).  ZERO of the eight entries
--     is discharged.  There were eight open obligations, sixteen after
--     Gtz.stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage splits each at the
--     unit-leverage face, and there still are.  What changes is what each may assume.
--     Gtz.exists_posDef_sixThree_of_stress_sum_ne_zero upgrades the shipped
--     Gtz.exists_dominating_sixThree_of_stress from PosSemidef to PosDef when the stress has
--     nonzero coordinate sum -- the shipped form cannot exclude a tie, because a tie already
--     has a weakly dominating triple, which is why the hinge lane never consumed it.  So
--     every stress of a (6,3) tie is balanced, and each of the four ledger shapes gains that
--     hypothesis for free: Gtz.stratumIsTieFreeAmongHeavy_of_balancedStress_sixThree and its
--     three siblings.  Orthogonal to the ledger's own narrowing, which constrains atom
--     LENGTHS where this one constrains DEPENDENCIES.
--
--   THREE OF THE EIGHT ENTRIES ARE SHARPENED FROM A STRATUM TO A SUBLOCUS.
--     Gtz.PatternForcesStress names the entries whose pattern alone manufactures a stress
--     through a line-pair quadric covering all six labels: [[0,1,2],[3,4,5]], the
--     four-point line [[0,1,2,3]], and [[0,1,2,3],[0,4,5]].  The four-point line is the one
--     worth noticing -- its second plane is not a line of the pattern at all, since any two
--     vectors lie in a plane and no line carries both labels off the four-point line.  On
--     those three a tie must carry a nonzero stress of zero coordinate sum, so what is owed
--     is not "no tie on the stratum" but "no tie on the codimension-one sublocus".  The
--     other five entries admit no covering pair and get nothing.
--
--   WHAT A TIE MUST LOOK LIKE.  Gtz.sq_eq_one_of_parallel_of_isTie_sixThree: a parallel pair
--     of a (6,3) tie has ratio squared one, so the two atoms have EQUAL LENGTH -- a
--     sharpening of Gtz.HingeHoldsAtSize's own conclusion.  And
--     Gtz.exists_smallerTie_size_four_or_five_of_stress_of_isTie_sixThree: a STRESSED (6,3)
--     tie restricts to a tie on four or five atoms carrying the SAME vectors, the first
--     descent this lane has had.  It does not bottom out: U(3,4) and the (5,3) diamond both
--     host ties.
--
--   NOTHING HERE APPROACHES Gtz.GtzWeighted 6 3.  The hinge is one lane among several, and
--     both of its inputs remain open.  Gtz.hingeHoldsAtSize_of_lineSizeCases_sixThree and
--     Gtz.hingeHoldsAtSize_of_multiLineCases_balancedStress_sixThree record the shape the
--     two inputs have been reduced to, not a proof of either.
import Gtz.Design.LinePatternSixCases
import Gtz.Quantitative.HingeStressNarrowing
-- ---------------------------------------------------------------------------------------
-- THE QUANTITATIVE BRIDGE AT (6,3): BOTH LANES, STATED PRECISELY FOR THE FIRST TIME
--
-- Gap 3 of the ledger reads "quantitative bridge, collar lane -- HALF-BUILT ... Open input:
-- the modulus lower bound", and gap 4 reads "quantitative bridge, value lane -- ABSENT ...
-- the precise closing implication has never been stated".  These two modules state both
-- implications.  Neither lane closes anything, and in both the reason is now a theorem
-- rather than a difficulty.
--
--   THE COLLAR LANE'S OPEN INPUT IS NOT WEAKER THAN ITS TARGET.
--     Gtz.exists_dominates_of_hasCollarTubeLawAtFloor: the htube slot of
--     Gtz.collared_two_piece_law, instantiated at the tree's own designMargin, tieLocus and
--     collaredSet with the rate and radius merely EXISTENTIAL, already forces domination.
--     Gtz.gtzWeightedHeavy_of_forall_hasCollarTubeLaw: the per-floor family of those slots
--     gives GtzWeightedHeavy m k outright, hence at (6,3) the whole of rank three through
--     the shipped Gtz.rank_three_of_heavy_six_three.  The mechanism is that Gtz.tieLocus is
--     {margin <= 0} and not {margin = 0}; at rank five, where the collar layer was
--     calibrated, Gtz.gtzWeighted_of_le_five closes that gap, and at (6,3) closing it is
--     exactly what is open, so every counterexample sits IN the locus at distance zero,
--     where the tube inequality degenerates to 0 <= margin.  The named wall of gap 3 is
--     therefore the CHOICE OF REFERENCE SET, not any analytic modulus.
--
--   AND THE MEASURED EROSION WAS NEVER ON THE LOGICAL PATH.  A counterexample supplies its
--     own floor -- its smallest weight -- so a consumer needs the law once PER FLOOR and
--     never with a floor-uniform constant.  That is visible in the proof of
--     gtzWeightedHeavy_of_forall_hasCollarTubeLaw, which instantiates at
--     Finset.univ.inf' _ D.weight and nowhere needs uniformity.
--
--   THE LEVERAGE CAP RUNS ONE WAY ONLY.  Gtz.leverageOf_le_inv_weightFloor_of_mem_collaredSet
--     is the composite the tree proves inline but never states: collared implies capped.
--     Gtz.weight_mul_leverageCap_sub_le is the converse's obituary -- from the trace
--     identity a cap l_c <= cap yields t_c (cap - l_c) <= cap - k, an UPPER bound on the
--     weight and a lower bound nowhere.  So the crux funnel does NOT cap the leverage, and
--     the collar's l parameter is 1/weightFloor by construction rather than the design's
--     largest leverage.
--
--   THE REPAIR IS A MARGIN-INDEPENDENT REFERENCE VARIETY.  Gtz.stressLocus is the collared
--     configurations carrying a nonzero stress, cut out without mentioning the margin, and
--     Gtz.designMargin_nonneg_of_mem_stressLocus is its boundary condition -- a THEOREM, off
--     the shipped Gtz.exists_dominating_sixThree_of_stress, where the tie locus offered only
--     the conjecture.  Gtz.neg_lipschitz_mul_infDist_le_margin is the missing companion of
--     the shipped Gtz.consumedModulus_le_lipschitzConstant: that one caps the modulus from
--     ABOVE at a set where the margin VANISHES, this one floors the margin from BELOW and
--     needs only NONNEGATIVITY, which is the whole point.  Together:
--     Gtz.designMargin_ge_neg_reach_of_stressLocus, an a-priori value floor from a Lipschitz
--     constant and a REACH, neither of them a Lojasiewicz exponent.
--
--   THE VALUE LANE'S SLOGAN IS A THEOREM.  All cruxes are global minimisers of one objective
--     over one domain, so they share one value (Gtz.SixThreeCrux.chartObjective_eq) and
--     Gtz.SixThreeCrux.exists_pos_forall_le_neg_chartObjective discharges "there is a
--     positive lower bound on |chartObjective| at a crux" outright.  What the chain consumes
--     is an EXPLICIT value, because the crux supplies its own floor at the unknown height
--     -chartObjective (Gtz.SixThreeCrux.hasWeightFloor_neg_chartObjective).
--
--   AND THE ALL-FLOORS COVERING IS THE CELL, AT BOTH PREDICATES.
--     Gtz.forall_weightFlooredCovering_iff_gtzWeighted_six_three and
--     Gtz.forall_flooredSpreadCovering_iff_gtzWeighted_six_three: quantified over all
--     positive floors, both the new covering and the tree's OWN shipped
--     Gtz.FlooredSpreadCovering at zero spread are equivalent to GtzWeighted 6 3.  The
--     collapse is a property of the quantifier, not of the covering notion, so no floored
--     covering "for all eps > 0" can be easier than the cell.
--
--   WHAT REMAINS IS ONE EXPLICIT NUMBER, WITH A KNOWN RANGE.
--     Gtz.isEmpty_sixThreeCrux_of_bandExclusion_of_flooredSpreadCovering closes the cell from
--     a band exclusion plus the SHIPPED covering at the same band -- the weakest available
--     ingredient, reached through Gtz.hasSpreadAtLeast_zero (zero spread is Cauchy-Schwarz,
--     no restriction) and Gtz.flooredSpreadCovering_of_weightFlooredCovering.  And
--     Gtz.isEmpty_sixThreeCrux_of_bandExclusion_of_four_div_twentySeven_lt shows a band above
--     4/27 contradicts the shipped value window by itself, so the useful range is exactly
--     (0, 4/27] -- above it the band exclusion is not a sub-goal but the whole cell.
--
--   NO C*eps^2 MARGIN LAW IS STATED, DELIBERATELY.  That law is measured FALSE: the floored
--     chart minimum is zero on the whole feasible floor range, and on the useful band range
--     the covering carries no margin at all.  The tree already says as much in its own words
--     at Gtz/Quantitative/FlooredSpreadRegion.lean:411-414, where
--     Gtz.splitTetraDesign_balanced_hasWeightFloor puts an exact tie inside the 1/8-floored
--     family and the header records that "the floor alone does NOT remove it".
--
--   AND ONE HYPOTHESIS HAD TO BE REPAIRED BEFORE IT COULD BE LANDED.  The natural form of
--     that assembly asks for a GLOBAL Lipschitz constant for the design margin, and
--     Gtz.not_lipschitzWith_designMargin_sixThree proves no such constant exists: atomMatrix
--     g is g gᵀ, so the margin is quadratic in the atoms on an unbounded configuration
--     space, and Gtz.spikeGrowthConfig reaches margin about scale^2 at distance scale.  An
--     assembly resting on a global constant would have been VACUOUSLY TRUE -- a quantitative
--     theorem in appearance, asserting nothing.  The landed statements use LipschitzOnWith
--     on the collared class, where the class is compact, the margin is continuous, and the
--     open content is the constant's SIZE.
--
--   NOTHING HERE APPROACHES Gtz.GtzWeighted 6 3.  Neither lane supplies an ingredient; the
--     collar lane's two open inputs are a Lipschitz constant and a reach, and even a correct
--     constant on the class is not obviously enough, since 6*sqrt 3/sqrt weightFloor is about
--     29.4 at floor 1/8 and the product beats even the trivial floor -1 only below reach
--     0.034.  That arithmetic is quoted, not mechanized.
import Gtz.Quantitative.CollarReferenceVariety
import Gtz.Quantitative.ValueLaneBandExclusion

-- ============================================================================
-- GAP 13 -- THE MINIMALITY LAYER OF THE (6,3) BOX, AND A PROPERNESS WITNESS
-- Gtz/Quantitative/SixThreeMinimalityLayer.lean
-- Gtz/Quantitative/SixThreeMinimalityWitness.lean
-- ============================================================================
--
--   THE SHIPPED BOX DID NOT FAIL TO PROVE ITS FIRST TWO MINIMALITY CONJUNCTS -- IT THREW
--     THEM AWAY.  Gtz.SixThreeCrux.frontier proves, as its first two components,
--     -4/27 <= chartObjective and 3 <= card chartArgmaxFamily.  The projection to the
--     design level, Gtz.isSixThreeRefutationCandidate_of_sixThreeCrux, destructures that
--     conjunction with an obtain pattern whose first two slots are `_`.  Both are
--     functions of the design; they were dropped only because they read in chart
--     vocabulary.  Gtz.HasChartValueAboveSharpFloor and Gtz.HasThreeArgmaxBlocks recover
--     them as box conjuncts, at one line each.
--
--   AND TWO MORE COME FROM THE SAME PLACE.  Gtz.HasCoveringArgmaxFamily -- every atom
--     lies in some argmax triple -- is the shipped Gtz.SixThreeCrux.exists_mem_chartArgmaxFamily
--     read as a conjunct, and Gtz.HasSupportedCoveringArgmaxFamily strengthens it by
--     keeping the tight direction that does not vanish at the atom.  The general law
--     behind the second is new at every size and rank: the shipped
--     Gtz.exists_mem_activeSubset_of_isChartStationaryData uses only that the constant
--     assembly diagonal is NONZERO, and
--     Gtz.exists_mem_activeSubset_pos_activeWeight_tightDir_ne_zero_of_isChartStationaryData
--     keeps the positive summand instead of discarding it.
--
--   ALL FOUR SPEND MINIMALITY, NOT NON-DOMINATION.  That is the whole point of the layer.
--     Gtz.isSixThreeRefutationCandidateSharp_iff proved the previous enlargement EQUAL to
--     the shipped box because each of its conjuncts was derived from the box's own
--     no-domination clause; these four are derived from Gtz.SixThreeCrux.isChartMinimiser.
--     The terminus survives on the smaller box:
--     Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateMinimal has the
--     same one-antecedent shape as its sharp predecessor.
--
--   NOTHING ASSERTS THAT THE BOX GOT SMALLER, AND THAT IS A THEOREM RATHER THAN A CAVEAT.
--     Every member of the shipped box refutes the cell
--     (Gtz.not_gtzWeighted_six_three_of_isSixThreeRefutationCandidate), so a design
--     witnessing a strict shrink IS a refutation of Gtz.GtzWeighted 6 3 --
--     Gtz.not_gtzWeighted_six_three_of_exists_strictShrink, and
--     Gtz.not_gtzWeighted_six_three_of_exists_candidate_not_satisfying at an ARBITRARY
--     extra predicate, so that no future run re-attempts the impossible.  STRICT
--     PROPERNESS IS UNEXHIBITABLE WHILE THE CELL STANDS, which is a different situation
--     from the previous run's iff-trap, where the added conjuncts were PROVABLY IMPLIED.
--
--   SO PROPERNESS HAS TO BE RELATIVE, AND IT SPLITS INTO A MEASURED HALF AND A PROVED ONE.
--     Gtz.IsSixThreeShapeCandidate is the shipped box minus its one global conjunct, a set
--     that is not conjecturally empty.  Over all TEN of its conjuncts, properness is
--     Gtz.MinimalityLayerIsProperOverShape -- a Prop, NOT a theorem, carrying its exact
--     six-integer-direction witness in its docstring, with
--     Gtz.exists_shapeCandidate_not_isSixThreeRefutationCandidateMinimal_of_properOverShape
--     as the consumer that keeps it a hypothesis rather than an inert assertion.  Over the
--     FIRST of those ten alone it is a KERNEL THEOREM:
--     Gtz.minimalityLayerIsProperOverAllHeavy exhibits an ALL-HEAVY design whose argmax
--     family is a single block, so neither Gtz.HasThreeArgmaxBlocks nor
--     Gtz.HasCoveringArgmaxFamily follows from all-heaviness.  That conjunct is the one
--     worth isolating: Gtz.rank_three_of_heavy_six_three carries the whole of rank three
--     off the all-heavy box alone.
--
--   THE WITNESS IS EXPLICIT AND ITS CHART IS RATIONAL.  Gtz.heavySpikeDesign has atoms
--     2s e_0, 2s e_1, 2s e_2, s e_0, s e_1, s e_2 with s = sqrt (6/5) at the uniform
--     weight 1/6; Parseval is 4 s^2 + s^2 = 6 and both leverages 24/5 and 6/5 exceed one.
--     Uniform weight makes P = (1/6) Gram, so Gtz.heavySpikeGap_apply pins the whole gap
--     rationally: 19/30 on the heavy diagonal, 1/30 on the light one, 2/5 across.  The
--     three heavy atoms are orthogonal, so the block {0,1,2} is exactly (19/30) . 1, while
--     every block meeting a light atom has a diagonal entry 1/30 and hence a smaller least
--     eigenvalue.  IT IS NOT A SHAPE CANDIDATE -- 2s e_0 and s e_0 are parallel and the
--     heavy triple is orthogonal -- so the ten-conjunct properness is untouched by it.
--
--   MOMENTUM, general in size and rank:
--     Gtz.activeWeight_le_rank_div_size_of_isChartStationaryData caps every active
--     multiplier at rank/size -- one half at (6,3) -- because a unit tight direction
--     supported on its own rank-element block splits its multiplier into rank summands of
--     the assembly diagonal.  No shipped sibling bounds an individual multiplier above.
--     Gtz.chartBlockValue_le_chartGapRaw_diagonal bounds a block value by the chart gap's
--     diagonal at any atom of the block, without ever evaluating Finset.orderEmbOfFin,
--     which does not reduce in the kernel.
--
--   NOTHING HERE APPROACHES Gtz.GtzWeighted 6 3.  The layer restates minimality at the
--     design level; its conjuncts are conjecturally vacuous exactly when the cell holds,
--     and the argument that a closed empty-interior condition cannot follow from an open
--     one is prose in the module header, not a theorem of this tree.
import Gtz.Quantitative.SixThreeMinimalityLayer
import Gtz.Quantitative.SixThreeMinimalityWitness

-- ## THE gtz-g3 HARVEST (land-sweep): eight prototypes, 180 declarations
--
--   The `gtz-g3` run left eight compiling prototypes that no writer's slot owned.  They
--   are landed here, each in its own module, with the R6 repairs the harvest turned up.
--   NONE of them approaches Gtz.GtzWeighted 6 3; each module says so in its own header.
--
--   WHAT THE HARVEST'S OWN DUPLICATE SCAN CAUGHT.  A kernel env.contains scan over every
--   name the eight prototypes declare found SEVEN already present, and only four of those
--   had been flagged by anyone:
--
--     * Gtz.gtzWeightedHeavy_of_gtzWeighted was claimed as new by the (7,3) prototype,
--       which reported zero collisions.  It has been in the TRACKED, pre-existing
--       Gtz/Reduction/HeavyTraceFrame.lean since before this campaign, with a
--       character-identical statement AND a character-identical proof.  Dropped; that
--       module is imported instead, so the uses resolve to the shipped theorem.
--     * Gtz.trace_assembly_mul_chartStationaryGap and Gtz.trace_mul_grassmannAcceleration
--       are in Gtz/Quantitative/ChartSecondOrderStep.lean.  Dropped, along with the
--       prototype's third trace lemma, which is the trace-commuted twin of the shipped
--       Gtz.trace_projection_mul_multiplier_of_isChartStationaryData.
--     * the four relabelling transports are in Gtz/Quantitative/EdgeOrbitSectors.lean.
--
--   AND WHAT ONLY A CONCEPT SCAN CAUGHT -- three semantic duplicates carrying no name in
--   common with their shipped originals:
--
--     * the covering prototype's chart symmetry reader IS Gtz.projection_apply_comm
--       (ChartHadamard.lean:187), character-for-character including the proof, and its
--       row-square identity IS Gtz.sum_sq_projectionRow_eq_diagonal (:197) read in the
--       other direction.  Both dropped; the one genuinely absent lemma there, the RAW
--       diagonal bound asking only symmetry and idempotence, is stated on top of them.
--     * the aggregate prototype's first power trace re-proves
--       Gtz.trace_projectionOfDesign_sub_weightDiagonal (ChartHadamard.lean:179).  Now
--       consumed, and Gtz.chartGapMatrix_eq_chartPointGap checks by rfl that the
--       prototype's gap alias IS the shipped Gtz.chartPointGap at the design's chart, so
--       every power trace is a statement about the tree's object rather than a copy.
--
--   THE EIGHT MODULES.
--
--   Gtz/Quantitative/RungThreeAggregate.lean (16) -- THE AVERAGING LADDER DOES NOT DIE AT
--     j = rank.  Gtz/Quantitative/PairRungAggregate.lean:40 says "the ladder climbs to
--     j = rank - 1 and dies at j = rank" and ChartHadamard.lean:775 says the aggregate is
--     not design-independent at non-uniform weights; both are true of the FLAT triple sum
--     and stop one step short.  With the prod-of-weights factor the rung-three aggregate
--     closes: Gtz.rungThreeAggregate_eq_sum_det_chartGapMinor identifies it with e_3 of
--     the chart gap, and the three power traces give the closed form.  Consequence:
--     Gtz.exists_nonneg_det_subsetSum_sub_one_sixThree, a pigeonhole exclusion.  The
--     identity is FIELD-BLIND, so it is not a realness consumer.
--
--   Gtz/Reduction/CoveringForm.lean (15) -- the conjecture as a COVERING statement.
--     Gtz.gtzWeighted_six_three_iff_forall_coversSimplex exchanges the quantifiers in the
--     shipped Gtz.chartGtz_iff_gtzWeighted: the cell says the twenty domination sets cover
--     the weight simplex at every rank-three projection.  The down-set and face laws are
--     landed, and Gtz.card_dead_add_rank_le is the first place idempotence does work.  The
--     module's own header records that the picture's whole content is BOUNDARY content
--     while the open cell is its interior.
--
--   Gtz/Quantitative/SevenThreeCollapse.lean (12) -- the (7,3) lane collapses onto (6,3),
--     and FIVE shipped (7,3) results carry contradictory hypotheses as a result.  The
--     three Gtz.false_of_* certificates state that in the kernel; the honest unconditional
--     (7,3) normal form is Gtz.nonempty_sixThreeCrux_iff_not_gtzWeighted_seven_three.
--     Gtz.SevenThreeCrux is left with no production theorem, which is a real open item.
--
--   Gtz/Quantitative/DeformationAndCurvature.lean (15) -- route C's FIRST leaf is the cell:
--     Gtz.hasChartValueZeroLimitAtEveryCrux_iff_gtzWeighted_six_three, because
--     Gtz.IsChartValueZeroLimit's dominating-triple clause is the verbatim negation of a
--     crux field.  Also: three crux fields follow from a negative chart value alone, and
--     every common quadric of a design is TRACELESS.
--
--   Gtz/Quantitative/PairRungRow.lean (5) -- the pair conservation law at a FIXED VERTEX,
--     which the shipped ladder states only as an aggregate over all pairs.
--
--   Gtz/Quantitative/ChartValueTwoRegime.lean (14) -- the a-priori two-regime predicate,
--     with Gtz.chartValueBandExclusion_of_chartValueTwoRegime bridging it to the shipped
--     crux-quantified Gtz.ChartValueBandExclusion.  The two were produced by agents who
--     could not see each other and are DIFFERENT objects; the bridge runs one way.  Both
--     the 4/27 ceiling and its strict form are landed, so the lane's target range is
--     pinned to (0, 4/27).
--
--   Gtz/Quantitative/SectorClassWitnesses.lean (96) -- gap 23: an explicit rational,
--     all-heavy, parallel-free, pairing-nonvanishing design for EACH of the eight
--     surviving sign classes, with its link word proved equal to the representative the
--     kernel already names, plus a relabelling invariant proving the eight PAIRWISE
--     NON-ISOMORPHIC.  This makes the sign layer's sharpness a theorem and thereby closes
--     that lane rather than advancing it.
--
--   Gtz/Quantitative/HypothesisWitnesses.lean (7) -- two hypothesis separations that
--     shipped as docstring prose.  Gtz.exists_posDef_not_frameOperatorIsPinched keeps
--     Gtz.exists_design_of_frame from being a restatement of its pinched neighbour, and
--     Gtz.blockDiagonal_velocitySquare_of_exists_acceleration makes block-diagonality
--     EQUIVALENT to solvability of the curve constraint, which is more than the shipped
--     existence lemma alone says.
import Gtz.Quantitative.RungThreeAggregate
import Gtz.Reduction.CoveringForm
import Gtz.Quantitative.SevenThreeCollapse
import Gtz.Quantitative.DeformationAndCurvature
import Gtz.Quantitative.PairRungRow
import Gtz.Quantitative.ChartValueTwoRegime
import Gtz.Quantitative.SectorClassWitnesses
import Gtz.Quantitative.HypothesisWitnesses

-- ---------------------------------------------------------------------------
-- land-smallfix [gtz-g3, Sweep]: the Veronese dichotomy between the two fields,
-- and a stress-free complex (7,3).
--
--   Gtz/Quantitative/ComplexVeroneseDichotomy.lean (22).
--
-- The stress walk runs on ONE count: seven rank-one symmetric 3x3 matrices cannot be
-- independent, because dim_R Sym_3(R) = 6.  Gtz/Reduction/StressWalk.lean (lines
-- 113-122) and Gtz/Reduction/StressConditionalWalk.lean (lines 30-34) both record, as
-- ORIENTATION PROSE, that the count has no complex analogue -- and both hedge honestly
-- ("not mechanized in this file", "not a theorem of this file").  This module supplies
-- the theorems the hedges point at.
--
--   THE REAL HALF.  Gtz.span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent:
--     six independent Veronese images at rank three SPAN the symmetrics, so
--     independence upgrades to a basis.  Read at a crux by
--     Gtz.SixThreeCrux.span_veronese_eq_symmetricSubmodule off the shipped
--     Gtz.SixThreeCrux.linearIndependent_veronese.
--
--   THE COMPLEX HALF.  Gtz.span_complexAtom_hermitianSpanAtom: NINE explicit Veronese
--     images span the Hermitians, so the rank-one Hermitians really do attain all nine
--     real dimensions.  Hence Gtz.exists_mem_hermitianSubmodule_notMem_span_of_six and
--     its Veronese form Gtz.exists_complexAtom_notMem_span_complexAtom_of_six: SIX
--     matrices never span -- the exact converse of the real half.
--
--   THE WITNESS (gap 18, the N3 item).  Gtz.stressFreeSevenDesign is a complex (7,3)
--     design with rational weights and Gaussian-rational atoms whose seven Veronese
--     images are ℝ-linearly independent:
--     Gtz.exists_complexWeightedDesign_sevenThree_stress_eq_zero.  The two halves are
--     then stated side by side in the hypothesis shape the walk consumes --
--     Gtz.exists_nonzero_stress_atomMatrix_sevenThree (over ℝ EVERY seven-family carries
--     a nonzero stress, the shipped Gtz.exists_parsevalNullDirection at 6 < 7) against
--     Gtz.not_exists_nonzero_stress_stressFreeSevenDesign (over ℂ this design carries
--     none).  So the mechanism is not merely unproved over ℂ; it is absent.
--
-- PROVENANCE.  dim_R Herm_3(C) = 9 is NOT proved here: it is the shipped, TRACKED
-- Gtz.finrank_hermitianSubmodule (Gtz/Quantitative/RankTwoRealnessCount.lean), with
-- Gtz.two_mul_finrank_symmetricSubmodule for the real side.  Both prose sites above
-- were written on top of that tracked file, so their hedges understate the tree: the
-- dimension count itself was already a theorem one directory away.  What was genuinely
-- missing is the VERONESE layer -- that the rank-one images attain those dimensions,
-- and that a complex (7,3) DESIGN can be stress-free.
--
-- WHAT THIS DOES NOT DO.  It does not touch Gtz.GtzWeighted 6 3 and cannot: every
-- statement is about ℂ, where weighted GTZ at rank three is already FALSE.  Its content
-- is negative -- which real mechanism does NOT transport.  The witness is ONE design;
-- nothing here says a GENERIC complex (7,3) design is stress-free, and nothing here
-- bounds how many do carry a stress.
import Gtz.Quantitative.ComplexVeroneseDichotomy

-- ## SYNTHESIS: THE CRUX VALUE CONTROLS THE COLLAR GEOMETRY
--
-- Two lanes of this campaign each concluded, separately, that a leverage cap at a crux
-- was unavailable.  The collar lane (gap 3) proved that a cap gives no weight floor and
-- read that as the funnel failing to cap the leverage.  The value lane (gap 4) proved
-- that a crux HAS a weight floor, namely `-chartObjective`, which is strictly positive.
-- Both landed in one slot and were never joined.  Joining them supplies the converse
-- direction, which nothing had consumed:
--
--   Gtz.SixThreeCrux.leverageOf_le_inv_neg_chartObjective -- at a crux every leverage is
--     at most the reciprocal of the crux's own chart value.
--
-- Three consequences, each of which the collar lane had listed as missing:
--
--   Gtz.SixThreeCrux.mem_collaredSet_neg_chartObjective -- every crux lies in the
--     compact collared class at an explicit floor.  The lane had no theorem placing a
--     crux in its own class.
--
--   Gtz.SixThreeCrux.mem_collaredSet_neg_chartObjective_of_other -- ONE floor serves
--     EVERY crux, because all cruxes share one chart value.  The measured erosion of the
--     collar constant, thought to be the lane's obstruction, is therefore not on the
--     path: a consumer needs the law once per floor and there is only one floor.
--
--   Gtz.SixThreeCrux.leverageOf_le_inv_of_chartValueBandExclusion -- an a-priori value
--     band of width `band` IS a leverage cap of `1 / band`.  Gap 2's missing epsilon and
--     gap 3's missing cap are reciprocals of one unknown; neither closes without the
--     other.
--
-- A sharpening from the third lane.  The sharp box's quadratic floor
-- `Gtz.SixThreeCrux.pairingMassFloor`, fed through the weighted diagonal law
-- `Gtz.sum_weight_mul_atomPairing_mul_atomPairing`, gives
-- `Gtz.SixThreeCrux.atomShare_lt_one_sub_neg_chartObjective` -- every share is strictly
-- below `1 - (-chartObjective)`, sharpening the shipped `share < 1` -- and dividing by
-- the weight floor improves the cap by a unit
-- (`Gtz.SixThreeCrux.leverageOf_lt_inv_neg_chartObjective_sub_one`).
--
-- WHAT THIS DOES NOT DO.  It moves nothing and names no number: the crux value is at
-- most 4/27, so the cap is at least 27/4 and has no upper bound without gap 2.  Every
-- statement is conditional on a crux, so none is exhibitable.  What changes is the map --
-- two lanes being costed separately are one lane.
import Gtz.Quantitative.CruxCollarFloor

-- ## SYNTHESIS: EVERY MECHANIZED FORM OF THE OPEN CELL, AGAINST THE 1997 CONJECTURE
--
-- `Gtz.gtzWeightedAll_iff_forall_gtzOriginal` made the frame an equivalence and
-- connected three rank-three termini to the literal 1997 statement.  Six further forms,
-- each proved equivalent to `Gtz.GtzWeighted 6 3` in its own module by a different lane,
-- were left unconnected: the size-seven cell, the two all-heavy boxes, the value-zero
-- deformation obligation, the covering of the weight simplex, and the two floored
-- covering families.  This file closes all of them.
--
-- EVERY THEOREM IN IT IS ONE `Iff.trans` OF TWO SHIPPED EQUIVALENCES AND CARRIES NO NEW
-- MATHEMATICS.  It is a census, and it exists for three reasons.  The composition fell
-- between two authors, each of whom identified it and recorded it as belonging to the
-- other.  A form whose equivalence is untracked goes silently inert -- five shipped
-- theorems in this tree acquired contradictory hypotheses the moment
-- `Gtz.gtzWeighted_six_three_iff_seven_three` landed, and stayed inert across two
-- campaigns because nothing recorded that the two sides had become one.  And the
-- campaign's target is the 1997 conjecture rather than a weighted proxy, so a reader
-- should not have to chain two theorems by hand to see what is open.
--
-- An equivalence is not progress.  Several of the forms named here were originally
-- advertised as reductions of the cell before being shown to be the cell itself, and the
-- file is written so that cannot happen again.
import Gtz.Reduction.RankThreeEquivalenceHub
import Gtz.Quantitative.MixtureAggregates
import Gtz.Quantitative.HarmonicCircuit
import Gtz.Reduction.SevenThreeStressCollapse
import Gtz.Quantitative.CompoundGram
import Gtz.Quantitative.BalancedCollections
import Gtz.Design.LinePatternSixCasesTwo
import Gtz.Quantitative.UniformWeightTie
import Gtz.Quantitative.VertexExclusion
import Gtz.Quantitative.PrivateAtomQuantization
import Gtz.Quantitative.CocycleRigidity
import Gtz.Quantitative.ChartArgmaxIndexFloorTwo
import Gtz.Quantitative.VertexInstances
import Gtz.Quantitative.TwoGraphRepresentability
import Gtz.Quantitative.CollarLipschitzConstant
import Gtz.Quantitative.EdgeStarMass
import Gtz.Quantitative.PlueckerRealness
import Gtz.Quantitative.GeneralRankCertificate
import Gtz.Reduction.RankFourLedger
import Gtz.Quantitative.ResidueReduction
import Gtz.Reduction.ShareBudgetLifting
import Gtz.LinAlg.CayleyAtlas
import Gtz.LinAlg.PolynomialOpenVanishing
import Gtz.Reduction.ChartPullback
import Gtz.Reduction.GenericityReduction
import Gtz.Reduction.SignClashReduction
import Gtz.Design.EraseSystem
import Gtz.Reduction.ForcedSignForcing
import Gtz.Reduction.SignClashCoverage

-- The parity narrowing: at an exceptional design the strict forced-minus
-- clause is free, thus the sign-clash route narrows to three positive
-- conjuncts whose middle one is the landed positive parity triple.
import Gtz.Reduction.SignClashParityNarrowing

-- The faithfulness verdict: the five open propositions of the sign-clash
-- route are each equivalent to the weighted cell, so the lattice is a
-- restatement and not a reduction.
import Gtz.Reduction.SignClashFaithfulness
import Gtz.Design.ExceptionalWitnessDesign

-- Residual threading (phase 4): the census bridges and the bordered-slack converse
import Gtz.Reduction.ResidualThreading

-- Phase 5 (cheap-farkas): the multi-edge capacity lemma and its certificate region
import Gtz.Reduction.FarkasCapacity

-- Phase 5 (front-connected): the connectedness route from the hinge to the frontier,
-- and the small-cell calibration showing neither of its two premises is slack
import Gtz.Reduction.ConnectednessRoute
import Gtz.Reduction.ConnectednessRouteCalibration

-- Phase 5 (front-hinge-decide): the hinge's evidence base at (6,3) -- the parallel
-- census of every shipped tie, the repeated-atom equivalence, and the complex
-- witness that says where the hinge spends its realness
import Gtz.Design.ShippedTieParallelCensus
import Gtz.Quantitative.HingeRepeatedAtom
import Gtz.Complex.TrinePrimitive

-- Phase 5 (front-signclash): the star tripartition certificate, the free-sub-star
-- budget, and the threshold decomposition that makes the star alphabet exhaustive
import Gtz.Design.StarTripartitionCapacity

-- Phase 5 (front-integrality): the degree/triangle bridge -- the torsion is
-- invisible to every linear functional, and sign conditions are where it is spendable
import Gtz.Quantitative.HypersimplexTorsion

-- Phase 5 (mv-spinor): the harmonic lift transports to every rank, and the one
-- invariant it discards is the symmetric cubic that carries the triple product's sign
import Gtz.Quantitative.SpinorTransport

-- Phase 5 (mv-selfdual): the chart dual carries the Loewner flip on the uniform slice,
-- and the complementation involution is fixed-point free
import Gtz.Quantitative.SelfDualInvolution

-- Phase 5 (mv-tightframe): the right-endpoint spread obligation IS GtzOriginal 6 3,
-- the 1997 conjecture at its first open shape
import Gtz.Reduction.UniformSliceIdentification
-- Phase 6: the reach hypothesis PROVEN -- Cholesky whitening (T2), the
-- parallel-free reach with its hinge-only capstones (T1+T3), and the
-- general-rank stress sign-split for the (7,3) syzygy lane
import Gtz.Reduction.CholeskyWhitening
import Gtz.Reduction.ParallelFreeReach
import Gtz.Reduction.StressSignSplit
-- Phase 7: the wave-1 landings -- the canonical (7,3) stress with its
-- (3,4) split, the K4 diagonal bricks and pencil law, the Nesterenko
-- series-parallel certificate kit with the diamond instance, and the
-- design-form variational principle
import Gtz.Reduction.StressExistence
import Gtz.Reduction.K4Diagonal
import Gtz.Reduction.SpCertificates
import Gtz.Reduction.ChartRealization
import Gtz.Reduction.HingeFunnel
import Gtz.Reduction.StressMassGap
import Gtz.Reduction.StressSupportTaxonomy
-- the three branches of `sixThree_stress_trichotomy` and the certificate
-- payloads they consume.  Several import upward out of their own directory,
-- so they sit here rather than in the layer blocks above.  Branches (ii) and
-- (iii) land a NAMED RESIDUAL, not the target -- read each file's header
import Gtz.Reduction.NoStressRigidity
import Gtz.Reduction.CoplanarStress
import Gtz.Reduction.PairEngineCore
import Gtz.Certificates.K4LeafPrototype
import Gtz.Certificates.KillInequalityAnchors
import Gtz.Certificates.KillCellCertificate
import Gtz.Design.DiamondStressSupport
import Gtz.Design.TwoPoleStratum
-- the rank-two hinge chain: circuit engine, conic Caratheodory + equality
-- stratum, the nu-band closure, the tie criterion, the hinge bridge, and the
-- companion construction closing branch (iii) unconditionally
import Gtz.Ties.RankTwoMassCircuit
import Gtz.Ties.ConicCaratheodory
import Gtz.Ties.RankTwoBand
import Gtz.Design.RankTwoTieCriterion
import Gtz.Ties.RankTwoHingeBridge
import Gtz.Design.CompanionConstruction
-- the balanced stratum, the trichotomy ledger (three-Prop reduction), and the
-- rank-three composite: GtzOriginal n 3 at every size from two remaining Props
import Gtz.Design.BalancedStratum
import Gtz.Reduction.TrichotomyLedger
import Gtz.Reduction.RankThreeComposite

-- Branch (i) of the stress trichotomy: the stratum's geometry, the normalizer
-- quadric kit, and the closure counterexample that pins weight positivity.
import Gtz.Design.StressFreeStratum
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.StressFreeClosureFailure

-- the free-mass budget hypothesis discharged, and the certificate arm shown
-- empty on the whole tie locus: the stress-free arm of the (6,3) hinge carries
-- ONE open Prop, `NoStressResidual 6`, not two
import Gtz.Design.FreeMassBudgetDischarge

-- and that Prop carried all the way up: rank-three GTZ at every size from
-- `NoStressResidual 6` alone -- a REPACKAGING, since the same file proves the
-- single Prop is strictly stronger than the five class obligations it stands in for
import Gtz.Reduction.RankThreeFromStressFreeResidual

-- The kill-inequality kernel certificate and the window/layer/dual kit
-- supporting the hinge and balanced-stratum frontiers.
import Gtz.Certificates.KillInequalityD7
import Gtz.Quantitative.CauchyBinetLayerSum
import Gtz.Quantitative.WindowCofactorBridge
import Gtz.Quantitative.WindowGramSignature
import Gtz.Quantitative.GeneralPositionWindow
import Gtz.Quantitative.WindowPolarity
import Gtz.Ties.TieBasisWindow
import Gtz.Ties.TieFreeNoGo
import Gtz.Ties.AllTied
import Gtz.Design.TetrahedralRigidity
import Gtz.Design.GaleDualWindow
import Gtz.Design.BalancedNormalForm
import Gtz.Design.LinePatternCompleteness

-- Branch (ii) machinery: the balanced-tie reduction (the selection Prop is a
-- tie exclusion on the zero-sum slice) and the endpoint-gauge descent with its
-- vanished-count residuals.
import Gtz.Reduction.BalancedTieReduction
import Gtz.Reduction.EndpointGaugeDescent

-- Kernel refutation certificates: no pure-triple selection closes the zero-sum
-- slice, neither pointwise nor along the whole walk orbit.
import Gtz.Certificates.PureTripleSelectionRefuted
import Gtz.Certificates.OrbitPureTripleSelectionRefuted

-- Branch (i) instruments: planar compression and the pair budget along tight
-- axes, the four-on-plane stress lever, the axis-mass budget transport with
-- its weakened drop residual, and the kernel witness that pair-budget
-- equality does not force coplanar outside atoms.
import Gtz.Design.TightAxisPairBudget
import Gtz.Design.FourOnPlaneStress
import Gtz.Design.AxisMassBudgetTransport
import Gtz.Certificates.PairBudgetEqualityWitness

-- The spike matroid obstruction: five atoms covered by two planes carry no
-- full-support spike, reducing the endpoint (5,3) tie exclusion to the
-- shared-line-pair matroid statement.
import Gtz.Ties.SpikeMatroidObstruction

-- The two-vanished (4,3) boundary residual holds unconditionally: the
-- conservation dichotomy, the total-tie frame, Bhatia-Davis selection, and
-- the two-rank-one exchange close the second vanished-count stratum.
import Gtz.Reduction.TwoVanishedBoundary

-- Branch (i)'s two tie constraint families in kernel form: the on-plane drop
-- is impossible at any tie (both drop residuals are exactly the stress-free
-- hinge), and the insert-plane pair-completion gate prices the second family.
import Gtz.Design.OnPlaneDropObstruction
import Gtz.Design.InsertPlaneCompletion

-- The balanced stratum is closed: branches (ii) and (iii) of the stress
-- trichotomy are theorems, and rank-3 GTZ at every size rests on the
-- stress-free hinge alone.
import Gtz.Reduction.BalancedStratumClosure

-- The threshold cell hinge at general rank: the deciding cell arithmetic, the
-- symmetric basis a stress-free design carries there, the rank-uniform stress
-- trichotomy, and the three named arms that reduce the two registry hinge
-- obligations.
import Gtz.Reduction.ThresholdCellHingeMap

-- The degenerate hinge arm at general rank: the Householder frame of a
-- hyperplane at every rank, the pole mass law that makes the Schur surplus
-- free, the repair of the producer residual that a parallel-pair tie refutes,
-- the mass gap priced over the labels a stress misses, and the two registry
-- hinge obligations on a smaller residual list.
import Gtz.Reduction.DegenerateHingeArm

-- The one-frame gate system at a tie: the master gate extraction, the
-- coupling floor, the equality law on the dominating stratum, the dual-conic
-- polarity of the stress-free stratum, the gate trichotomy, and the
-- light-weight collar criteria.
import Gtz.Design.TwoFamilyTightFrame

-- The uniform-in-rank corank-2 descent: the explicit rank-two Naimark dual
-- with its pair and triple bracket dictionaries, the tie-locking of that
-- dual, and the shared-circuit-pair law at every primitive corank-2 tie.
import Gtz.Uniform.NaimarkCorankTwo
import Gtz.Uniform.CorankTwoTransfer
import Gtz.Uniform.SharedCircuitPair

-- The uniform induction step: the corank floor at every rank, the
-- window-closure step skeleton with its descent-ladder mechanism twin, the
-- grand conditional resting the whole conjecture on per-rank window closures,
-- and the named open gap Props of routes (a) and (b).
import Gtz.Uniform.InductionStep

-- The rank-two uniform-position bridge (named gap 4 closed) with the uniform
-- dependence dictionary, the route-(a) composition on its two remaining
-- Props, the rank-3 hinge corank-2 slice, and route (b) wired uniformly;
-- then the relativized window hinge, the corank wall, and the free anchor
-- half of the reach obligation.
import Gtz.Uniform.UniformPositionBridge
import Gtz.Uniform.RouteBProps

-- The core-tail anchor for route (b)'s reach obligation: the Parseval
-- bookkeeping is feasible at every rank, and the diagonal tail assembles in a
-- single coordinate 2-plane with telescoping weights.
import Gtz.Uniform.AnchorBookkeeping
import Gtz.Uniform.AnchorAssembly

-- The assembly itself: the core and tail families reindexed along the block
-- split of the label set, Parseval balanced, and the anchor produced at every
-- cell of corank two or more.  What is left of route (b)'s reach obligation is
-- one connectivity statement about the parallel-free locus.
import Gtz.Uniform.AnchorReachAssembly

-- The reach statement at general rank: the tuple walk and the whitening
-- interface, and the composition that turns the two of them into the reach
-- hypothesis at every size and rank.  Also the general-rank moment curve, the
-- normal to a pair of rows, and the single move inside the good tuples.
import Gtz.Uniform.GeneralRankReachSkeleton

-- The moment-hub schedule at general rank: a spanning family contains a
-- spanning base of at most rank rows, and the window floor 2 * rank <= size
-- lets the labels outside that base walk onto the moment curve first.  The
-- tuple walk is a theorem at every window cell of every rank of three or more.
import Gtz.Uniform.MomentHubSchedule

-- The whitening at general rank, through the positive-definite square root of
-- the continuous functional calculus, and the anchor-reach obligation as a
-- theorem: the sharp-window statement at rank four and above needs no
-- hypothesis, and route (b) keeps one topological input.
import Gtz.Uniform.SpectralWhitening

-- The window induction step with the topological side discharged: the parallel
-- branch is free from the previous cell, thus a window cell needs only its
-- hinge, and the deciding cell of a rank follows from the three hinge arms.
import Gtz.Uniform.WindowInductionStep

-- The mass-gap descent and the tie-carrying recut of the deepest hinge arm: a
-- strictly dominating set drops a label when that label's pivot value is less
-- than one, the pivot values add up to the rank plus the inverse-gap trace, the
-- mass gap prices both, three explicit atoms show the bare shrink route is
-- false, and the deepest arm is restated with the tie and the primitive design
-- it always had.
import Gtz.Reduction.MassGapDescent

-- The polar cover descent: the Householder frame of a hyperplane is an
-- orthonormal BASIS at every rank, every design carries an atom longer than the
-- unit sphere, that atom is light, thus the design read against its own
-- orthogonal hyperplane leaves a mass deficit and the conjecture one RANK down
-- answers with a STRICT cover; the Schur core then turns the cover plus a tilt
-- bound into a strictly dominating subset, and one selection residual closes
-- the hinge, all three arms, the partial-support sub-arm, the repaired
-- degenerate cover and both registry hinge obligations.
import Gtz.Reduction.PolarCoverDescent

-- The polar tilt ledger: Parseval read along the pole prices the whole tilt
-- budget, thus that budget is at most HALF the pole's leverage and never the
-- leverage itself; a pole that saturates the leverage cap is orthogonal to every
-- other atom, thus the whole saturated stratum closes with no residual; a tie
-- obeys a new weight law against the saturation deficit at every overshooting
-- atom; and the residual narrowed by those two free facts still closes the
-- hinge, the three arms, the sub-arm, the repaired cover, the three threshold
-- arms and both registry hinge obligations.
import Gtz.Reduction.PolarTiltLedger

-- The plane whitener and the deletion law: the whitener of a one-atom deletion
-- is a RANK-ONE shear, thus it is elementary and no matrix square root is
-- spent; a design with a dead atom admits the deletion of any unsaturated live
-- atom; the pole of the polar construction IS the dead atom of the plane
-- restriction, thus the covering set of the hyperplane can be chosen to avoid
-- one named label; a tie carries no deletable label whose removal leaves every
-- other label below the tilt budget; and the tilt residual narrowed by that
-- free fact still closes the hinge, the three arms, the two sub-arms, the
-- repaired cover, the three threshold arms and both registry hinge obligations.
import Gtz.Reduction.PolarDeletionWhitening

-- The iterated deletion: the composed shear of a deleted SET removes exactly
-- the deleted atoms, with the ORIGINAL weights, thus the covering set of the
-- pole's orthogonal hyperplane can be steered away from a whole named set.  The
-- set is deletable exactly when its SURVIVORS carry debt above `rank - 2`.
import Gtz.Reduction.PolarIteratedDeletion
-- The pair spread and the survivor Schur kill: the division-free pair
-- eigenvalue certificate, the spread cover under trace admissibility alone,
-- the residual narrowed a fourth time, and the survivor Schur kill of the
-- deciding cell.  The Schur kill reads the pole components of the survivors,
-- needs no predecessor rank, and reaches the pentagon phantom.
import Gtz.Reduction.PolarPairSpread
-- The witnessed Schur kill: the exact plane witness removes the coupling
-- Cauchy-Schwarz loss, the sharp tie law of the deciding cell follows, and
-- the residual narrows a fifth time.  The complex ties of the deciding cell
-- saturate the witness law, thus the discharge of the residual must consume
-- a real-only ingredient.  The bracket sign platform is that ingredient's
-- vocabulary: the wedge square is the shadow Gram complement, and shared-slot
-- wedge products are polynomial in the pairings.
import Gtz.Reduction.PolarWitnessSchur
-- The plane Cramer calculus and the closed cross witness: the Cramer
-- dependency laws couple brackets to pairings, the sine addition law
-- transports shadow brackets, and the witnessed Schur kill of the deciding
-- cell closes with an explicit witness.  The plane Cayley-Hamilton law solves
-- the survivor plane equation at the scale `leverage * polarPlaneDet`, thus
-- the sharp tie law becomes a polynomial law of the pairing data.
import Gtz.Reduction.PolarCrossWitness
-- The quarter turn of the pole plane and the arithmetic tie law: the cross
-- product of the pole with an atom pairs through the Lagrange identity, the
-- turned frame gives the five contraction laws of the pole plane, and the
-- plane Cayley-Hamilton law turns the trace and the plane Gram determinant
-- into a direct cover with no weight cap.  The coupling vector reads the
-- closed cross witness as a polynomial in the shadow data, thus the sharp tie
-- law of the deciding cell becomes arithmetic.
import Gtz.Reduction.PolarPlaneTurn

-- The circular order of the pole plane: the signed shadow of a label is its
-- pole reading times its plane component, and the anchor identity makes every
-- row of signed wedges a positively weighted sum that vanishes.  Thus every
-- pole of a primitive tie carries an antiparallel pair or a wrapping triple,
-- the origin is a positive combination of at most three signed shadows, and
-- the seventh bundle of the polar chain carries content that the complex field
-- cannot supply.
import Gtz.Reduction.PolarCircularOrder
import Gtz.Reduction.PolarShadowFloor
import Gtz.Reduction.PolarGapDeterminant

-- The frame-priced descent: the design identity contracts against the inverse
-- gap of every region, thus the pivot pigeonhole becomes an exact stage law and
-- the first drop is free at every design of size above the rank plus one; the
-- block drop and the price of a stage; the exact rank-one pivot update and two
-- free drops at the deciding cell of rank four and up; the same laws for a bare
-- frame with scales of total less than one; and the two hinge obligations on
-- the current arm list.
import Gtz.Reduction.FrameDropDescent

-- The matroid stratification of the stress-free hinge: the plane-pair escape
-- law empties four of the nine six-point classes, the hinge follows from
-- tie-freeness of the five named survivors, and the seam splits those five by
-- the diamond restriction; plus the gating wall on the general-position
-- stratum, named and priced.
import Gtz.Design.StressFreeMatroidStratification
import Gtz.Design.StressFreeClassSplit
import Gtz.Design.TieCensusCompletion
import Gtz.Design.KFourChartSample

-- the census ladder for the two chartless classes, the relabel bridge from
-- identity-labelled tie-freeness, the fully rational one-line sample with two
-- strict dominators, and the direction-generic open-atom lift identity
import Gtz.Design.LineClassObstructions
import Gtz.Design.TightSwapObstructions
import Gtz.Design.InPlaneRestriction
import Gtz.Design.SelectorEquivalences
import Gtz.Design.LineMarginCap
import Gtz.Design.PairDifferenceCover
import Gtz.Design.PairingMinorPlueckerBridge
import Gtz.Design.TightAntecedentMining
import Gtz.Design.AllHeavyNegativeAggregate
import Gtz.Design.BarycentricOpenCellWitness

-- the gap determinant in projection-DPP basis coordinates: the Cauchy-Binet
-- expansion at EVERY subset and cardinality, the dictionary that makes the
-- centered inclusion moments the campaign's own refusal scalars, and the
-- transported-frame congruence that removes the whitening from the question
import Gtz.Quantitative.BasisCoordinateGapExpansion

-- the polarized cross-axis Parseval, off-conicity as a single Gram determinant,
-- and the fifteen octahedral binomials that put off-conicity back inside the
-- weight-free bracket-square layer
import Gtz.Design.ConicBinomialShadow

-- the six dual conics of the stress-free stratum, read JOINTLY: every linear
-- functional of the frame is an additive set function, and at the tree's landed
-- stress-free inhabitant no additive score separates the strict triples
import Gtz.Design.DualConicLinearBarrier

-- U(3,6): the off-conic formulation of stress-freeness, the exact rational
-- icosa approximant sample, and the mass-reading clearance functionals
-- positive exactly on the open line-free stratum
import Gtz.Design.LineFreeConicBridge

-- the K4 contraction-descent bricks: the rank-two Foster engine, Sylvester
-- lifts by completed squares, the deletion-contraction det normal forms, the
-- rank-two slack lemma, the contraction winner at edge 5, the endgame
-- vocabulary -- AND the kernel refutation of the max-conductance-edge
-- selection at an exact witness where the chart obligation stays intact
import Gtz.Design.KFourChartClosure

-- the K4 leverage refuter and the K4 tight locus: the max-leverage-edge
-- selection dies at an exact chart point, and the tie-freeness of the K4
-- direction chart is reduced to emptiness of one tight-but-not-strict locus
import Gtz.Design.KFourLeverageRefuter
-- The knife-band liveness layer: the canonical band inhabitant carries a
-- strict tree in kernel, the det-positive-not-definite witness is exact,
-- and the pencil-gate collapse shows a gated determinant argmax is the
-- bare existence statement and can never produce it.
import Gtz.Design.KFourBandLiveness
import Gtz.Design.KFourTightLocus

-- the K4 forced-edge law and the descent ladder it sits at the top of: the
-- chart gap in electrical coordinates, the necessary condition every strictly
-- dominating subset satisfies at each label it omits, the erase rung as an
-- equivalence at every level, and the rung-two pruning that is exact at the
-- residual band's canonical inhabitant
import Gtz.Design.KFourDescentLadder

-- and what the forced set can be: always a forest, hence always inside a spanning
-- tree, hence the forcing condition can never exclude every candidate -- forcing
-- prunes, it cannot decide and it cannot refute
import Gtz.Design.KFourForcedForest

-- the strong-stationarity index floor: feeding the block least-eigenvector
-- selection into strong chart stationarity DISSOLVES the compatibility
-- hypothesis instead of proving it, and multiplicity inside a block stops
-- mattering.  UNCONDITIONAL: at least FOUR active blocks at a crux, raising the
-- shipped floor of three; and an active block whose tight support has at least
-- two labels with its coordinate singles inside the finite row span.  At
-- exactly four active blocks some active block carries a coordinate vanishing
-- on its WHOLE tight eigenspace.  The five-floors and the flat-pair refutation
-- are CONDITIONAL on supplied tight-eigenvector data whose satisfiability this
-- module does not settle
import Gtz.Quantitative.StrongStationarityIndexFloor

-- the complement-kernel weld: whitening the full excess turns EVERY complement
-- test, at any omitted size and any rank, into the principal minors of one
-- inverse-metric Gram matrix, whose first rung is the already-landed full-base
-- pivot and is therefore free at a crux -- the residual selector is three edge
-- conditions plus one determinant.  ITS CLOSING EQUIVALENCE IS A RESTATEMENT
-- OF THE TARGET AND DISCHARGES NOTHING; what it buys is the change of
-- coordinates, not a reduction in the open content
import Gtz.Reduction.ComplementKernelWeld

-- the collar atlas kernel replay: the verified interval/graded/guarded box
-- checker for the rung-15 barycentric order-chart certificates, and the 120
-- replayed charts -- one decide per chart turns the adaptive coarsest cover
-- into the pointwise window sign package on the whole chart cube
import Gtz.Certificates.CollarChartReplay

-- the descent ladder, its supply, its blind spot, and the kernel that repairs
-- it: the three rung equivalences identify each rung of the pivot descent with
-- a nested principal minor of ONE inverse-full-excess Gram, with no rank-one
-- update anywhere (which matters, because at the tetrahedron the erased base is
-- singular and the update form does not exist); the cardinality-slack law
-- generalises the landed excess balance off the rank+1 base and measures the
-- descent supply; and the blind-spot theorem proves that a dominating subset
-- whose gap carries two independent probes has NO positive definite one-label
-- superset, so the descent cannot reach it while the kernel decides it anyway.
-- THE LADDER AND THE KERNEL ARE THE SAME COORDINATES ONLY ON THE CORANK <= 1
-- STRATUM; off it the kernel is complete and the descent is not.  Nothing here
-- discharges an obligation: the lattice is the same lattice.
import Gtz.Reduction.ComplementKernelRepairsDescent


-- the joint chart index floor: the two first-order fields of a chart
-- stationarity datum are the two coordinate blocks of ONE gradient, so both
-- stationarity laws are the single relation `sum_C mu_C . jointGradient_C = 0`
-- and the joint floor `|A| >= 1 + rank(J)` DOMINATES both one-block floors,
-- a coordinate projection being unable to raise a rank.  The Grassmannian
-- gradient is identified as a rank-one outer product, and the tangent identity
-- shows the first-order motion of a block value reads only the off-diagonal
-- corner.  MEASURED CAVEAT CARRIED IN THE AUDIT BLOCK: the floor is an
-- identity, not a bound, in the whole crux regime.
import Gtz.Quantitative.JointChartIndexFloor


-- the floor-atom span: the master identity
--   sum_l mu_l ((P u_l)_c)^2 = (value + t_c) / size
-- at every atom of every chart stationarity datum, off the landed sandwich and
-- the landed forced diagonal.  Its consequences: the leak identity as a
-- corollary rather than a measurement; the row law, which kills every projected
-- tight direction at an atom sitting on the landed weight floor; and the
-- closing theorem, that the projected tight directions of a datum in the OPEN
-- value window are never all collinear -- proved by an integrality argument,
-- with no geometry at all.
import Gtz.Quantitative.ChartFloorAtomSpan


-- the rank-three collinearity rigidity: in a PARALLEL-FREE rank-three design any
-- two distinct atoms determine ONE unit chart-fixed direction, and every
-- chart-fixed vector vanishing at both is a multiple of it.  Unconditional,
-- about designs alone, and NOT vacuous under the conjecture.  It is the socket
-- the floor-atom closing theorem needs, supplied from the design side where the
-- landed cross-product kit makes it elementary and no dimension count is used.
import Gtz.Quantitative.ZeroLeakCollinearClosure


-- the design-free value window: the design hypothesis carried by every shipped
-- value floor is REDUNDANT -- a stationarity datum is a chart point, and
-- `Gtz.chartPointHasDesign` realises every such point unconditionally -- so the
-- sharp floors -4/27 at (6,3) and -10/77 at (7,3) hold off the bare bundle plus
-- argmax.  With them the pointwise weight cap and its window, the cap's
-- equality case inhabited at a landed datum, and an exact witness showing the
-- STRICT dual bound is FALSE without a further hypothesis.
import Gtz.Quantitative.ChartStationaryDesignFreeWindow


-- the weight-aware clearance functional the stage-5 note of the U(3,6)
-- obligation asks for, built and TESTED: the minimum of the landed wall
-- clearance and a scaled minimum raw weight, positive on the open stratum and
-- relabelling-invariant, instantiated into the landed two-family split without
-- touching one lemma of it.  It removes the landed clearance refutations -- the
-- design behind all three falls below 3/8 at every weight scale at most 47 --
-- and the repaired region is inhabited by a landed design and STILL FALSE at
-- margin floor 1/4.  With it the sharp division-free collar in the weight
-- chart.  Buys back the rectangle's ground and nothing more.
import Gtz.Design.WeightAwareClearance
-- The universal needle of a weighted design.  A cap on the weights is a
-- floor on the FULL gap form at EVERY probe, division-free, with the
-- constant 1 - cap beating the per-triple 1 - 2*cap of the A1 residual.
-- The heavy-label audit lands here: every (6,3) design carries a weight
-- of at least 1/6, so the tenth-heavy narrowing of A1 is free.
import Gtz.Design.UniversalNeedle


-- THE (6,3) INDEX-LADDER SPINE: the chart argmax family is a filter of the
-- rank-subsets, so its cardinality is at most `size.choose rank` -- TWENTY at
-- (6,3), a ceiling nothing in the tree had ever recorded.  With the landed
-- unconditional floor of four the active count of a counterexample lies in a
-- window of SEVENTEEN VALUES, and excluding all seventeen IS the cell: the
-- ladder is a finite case analysis, not an open-ended climb.  Every open rung
-- is a NAMED HYPOTHESIS of a compiling theorem, never a `sorry`, and BOTH
-- routes through the file are proved EQUIVALENT to the cell, so the split is a
-- lossless reformulation that buys a countable residual and no mathematics.
import Gtz.Quantitative.SixThreeIndexLadderSpine


-- the zero-leak dependency: the global eigen-equation, which is zero leak,
-- forces a linear combination of the atoms to vanish -- one theorem, no case
-- analysis, at every support size and every rank, and consuming no part of the
-- first-order system.  With it the EQUIVALENCE that a design has a parallel
-- pair exactly when its projection form has a two-supported kernel vector,
-- which is what turns the support-two branch into a contradiction at a
-- counterexample.
import Gtz.Quantitative.ZeroLeakDependency


-- a dominating triple that no ladder rung can certify: a fully RATIONAL (6,3)
-- design on the three coordinate axes whose base triple dominates with a gap of
-- corank two, so the blind-spot theorem applies and every rung of the pivot
-- descent is vacuous there while the complement kernel decides it with no base
-- at all.  Rationality is not automatic -- at uniform weights none exists, six
-- not being a sum of two rational squares -- and it is what makes the
-- separation exhibitable rather than merely measured.
import Gtz.Reduction.LadderRungHasNoBase


-- THE SIGN OF AN ADMISSIBLE CHART STATIONARITY VALUE IS THE CELL.  Every
-- quantitative floor in the layer is trivially true at a nonnegative value, so
-- all of its content sits on the negative side -- and this proves that side is,
-- at (6,3), EQUIVALENT to the failure of the cell, and provably EMPTY at rank
-- two and at every size at most five.  A floor cannot be improved into a proof
-- of the cell without becoming a proof of the cell.  The sign law needs neither
-- first-order law, so the trap that the diagonal and commutation laws constrain
-- jointly does not touch it.
import Gtz.Quantitative.ChartStationaryValueSign


-- the four-active support-two block: at a (6,3) counterexample with exactly
-- four active blocks, EVERY unit least-eigenvector family has an ACTIVE block
-- of support exactly two.  Two landed theorems 274 lines apart in one file,
-- composed for the first time, and the composition is multiplicity-robust
-- because it quantifies over the family rather than choosing an eigenvector.
import Gtz.Quantitative.FourActiveSupportTwoBlock


-- the chart weight box: what the pointwise weight cap buys.  The box and its
-- diameter, the equality case characterising when the cap is attained, the
-- quantitative deformation of the landed floor rigidity -- every weight within
-- (size-1)(value + 1/size) of uniform, with the shipped endpoint theorem as its
-- zero-radius case -- and the crux corollaries.  The cap and the floor are the
-- two faces of one statement under the simplex, so the SUMMED consequence is
-- exactly the shipped bound; what is new is that the bound is POINTWISE.
import Gtz.Quantitative.ChartWeightBox


-- the design-free floor at its widest scope, and its non-vacuity: the
-- Cauchy-Binet floor design-free at EVERY cell without a rank hypothesis --
-- weaker than the combined floor wherever both apply, but the comparison
-- carries `0 < rank` and `rank <= size` and this does not, so its only content
-- is scope -- together with the two witnesses that make the whole design-free
-- layer's antecedent inhabited rather than merely unrefuted.
import Gtz.Quantitative.DesignFreeFloorScope


-- the zero-leak branch, closed at rank three: a zero-leak tight direction is
-- supported at two distinct atoms, its support sits on the weight floor, the
-- row law then kills every projected tight direction there, the rank-three
-- rigidity makes them all multiples of one normal, and the collinearity theorem
-- forbids that.  No case split on the support size anywhere.  ** BUT ITS
-- HYPOTHESIS BUNDLE HAS NO EXHIBITED INHABITANT AT ANY CELL: the one landed
-- negative-value (6,3) datum sits on the excluded endpoint by an exact
-- equality, so the crux corollary is vacuous if the conjecture holds. **
import Gtz.Quantitative.ZeroLeakClosure


-- the captured rank floor: at negative value NEITHER captured corner of a
-- stationary assembly has range dimension at most one.  The complement corner
-- dies by a Rayleigh estimate -- constant diagonal caps each coordinate mass,
-- per-block Cauchy-Schwarz caps each scaled overlap by rank/size, and the
-- multiplier average contradicts the corner's trace whenever
-- rank * size <= (size - 1)^2 -- needing NO multiplier positivity and no
-- window strictness, so it reaches every multiplier support.  The primal
-- corner transports rank one into collinearity of the positively weighted
-- projected tight directions and fires the landed closing theorem.  Together
-- the corners put every (6,3) crux assembly at rank at least four.
import Gtz.Quantitative.CapturedRankFloor


-- the assembly rank floor: the two captured corners live inside the assembly's
-- range and meet trivially, so with both corners past rank one every (6,3)
-- crux assembly has range dimension at least four -- at every active count,
-- with no positivity hypothesis.  At exactly four active blocks the floor
-- saturates: all four multipliers are positive, the four tight directions are
-- independent, and the corner ranks pinch to exactly (2,2) -- the four-active
-- coefficient projection has trace two, with positivity DERIVED.
import Gtz.Quantitative.AssemblyRankFloor


-- the four-active coefficient projection: the multiplier-weighted tight
-- columns of an exactly-four argmax family have Gram equal to the assembly
-- and admit a left inverse, and the chart descends to a coefficient matrix
-- with P B = B M, symmetric, idempotent, of trace two -- the complete
-- algebraic interface under the four-active leaf census, with multiplier
-- positivity and the (2,2) captured ranks drawn from the landed rank floor.
import Gtz.Quantitative.FourActiveCoefficientProjection


-- the assembly rank split: the reusable additivity rank Xi = rank(P Xi) +
-- rank((1-P) Xi), the two corner caps at three, the survivor list (4,2,2),
-- (5,2,3), (5,3,2), (6,3,3), the captured trace window [1/54, 1/6), the
-- shifted-weight window [0, 1), and the three-rung rank spine that is
-- equivalent to the cell.
import Gtz.Quantitative.AssemblyRankSplit


-- reindexing invariance of the least Rayleigh value: a permutation of the
-- index set is a bijection of nonzero probes preserving quadratic form and
-- norm, so lambdaMinMat is invariant under permutation submatrices, and the
-- least eigenvalue of a principal block depends only on the SET of selected
-- indices, never on the enumeration cutting the block.  The two analytic
-- bricks under the relabelling equivariance of the chart objective.
import Gtz.LinAlg.LambdaMinReindex


-- relabelling equivariance of the chart objective at the configuration
-- level: permuting the atoms conjugates the gap, moves every block value
-- along C |-> C.map sigma, and fixes the objective -- the candidate family
-- is permutation-stable and the sup does not move.  The chart-point and
-- crux transports that reduce any active family to its orbit representative
-- consume exactly these three theorems.
import Gtz.Reduction.ChartRelabel


-- the crux relabelling action: every field of a (6,3) crux transports along
-- an atom permutation -- the projection conjugates, the chart objective does
-- not move, the minimiser field survives verbatim, the design-side fields
-- ride the landed domination equivariance -- and the argmax family of the
-- relabelled crux is the inverse-image family with the SAME CARDINALITY.
-- Every statement proved at an orbit representative of an active family now
-- transports to the whole orbit; the four-active census fires at fifteen
-- representatives instead of every covering family.
import Gtz.Quantitative.CruxRelabel


-- the four-block cover budget: four card-three blocks carry twelve incidence
-- slots over six atoms, so under covering exactly six units of multiplicity
-- are forced above the floor of one, and some atom is doubly covered.  The
-- enumeration pre-filters of the four-active orbit classifier.
import Gtz.Quantitative.FourFamilyCoverBudget


-- the seven multiplicity profiles: a covering four-family's cover counts
-- take values in [1,4], partition the six atoms into four count classes, and
-- weigh the twelve incidence slots -- so the profile (#4s, #3s, #2s, #1s) is
-- one of exactly seven tuples.  The outer case split of the four-active
-- orbit census.
import Gtz.Quantitative.FourFamilyCoverProfiles


-- the quadruple-atom door: a cover count of four puts the atom in all four
-- blocks, and a card-three block through two named atoms is those two plus a
-- third -- the edge-pencil normal form behind the three profile doors that
-- carry a quadruply-covered atom.
import Gtz.Quantitative.QuadrupleAtomDoor


-- the pencil-door reduction, COMPLETE: two quadruply-covered atoms force the
-- family into the edge pencil (four pairwise-distinct thirds exhaust the four
-- atoms off the edge), and the explicit pair permutation carries any such
-- family onto the canonical pencil at the edge {0,1}.  The first census door
-- closed end to end: normal form, witness permutation, canonical transport.
import Gtz.Quantitative.PencilDoorReduction


-- the hub normal form: a single quadruply-covered hub sits in every block, so
-- erasing it turns the family into four pairwise-distinct edges on the five
-- off-hub atoms — the family is the image of that edge set under insertion of
-- the hub, off-hub cover counts become edge degrees, covering makes the edges
-- span the off-hub atoms, and a singleton quadruple class caps every off-hub
-- degree at three.  The single-hub profile doors are now 4-edge graphs on
-- five vertices, the object the graph classification consumes.
import Gtz.Quantitative.HubFamilyNormalForm


-- the chair-door reduction, COMPLETE: at profile (1,1,1,3) the erased edge
-- graph is forced into the chair — the triple atom (apex) and double atom
-- (wrist) share an edge or two blocks collide, the apex carries two leaf
-- edges, the wrist one tail edge — and the six pinned atoms assemble an
-- explicit permutation carrying the family onto the canonical chair
-- {{0,1,2},{0,1,3},{0,1,4},{0,2,5}}.  Second census door closed end to end;
-- the count inversions and pair-extraction bricks are shared by the
-- remaining doors.
import Gtz.Quantitative.ChairDoorReduction


-- the path-and-triangle door, COMPLETE: at profile (1,0,3,2) the two single
-- atoms either share their sole edge (the remaining three edges are then
-- card-two subsets of the three double atoms: the TRIANGLE plus pendant
-- edge) or hang off two distinct double atoms whose remaining slots thread
-- through the third (the FIVE-PATH).  The 16-branch leaf dispatcher
-- renormalizes the family around the leaves with counts carried verbatim,
-- and explicit permutations land both shapes on their canonical
-- representatives.  The quadruple-atom half of the census is complete:
-- doors (2,0,0,4), (1,1,1,3), (1,0,3,2) all closed.
import Gtz.Quantitative.PathTriangleDoorReduction


-- the quadruple-door dispatch: a card-four crux family names four distinct
-- covering triples, the profile census fires, and the three closed
-- quadruple doors compose with the crux relabelling transport — every
-- card-four crux either relabels to a crux whose argmax family IS one of
-- the four canonical quadruple representatives (pencil, chair, five-path,
-- triangle-plus-edge) or realizes one of the four quadruple-free profiles,
-- the exact interface the remaining census doors consume.
import Gtz.Quantitative.QuadDoorDispatch


-- the three-triple door, COMPLETE: at profile (0,3,0,3) each triply-covered
-- atom misses exactly one block — coinciding misses collide two all-triple
-- blocks — so the misses biject with the three mixed blocks: one block holds
-- all three triple atoms and each mixed block is a triple pair completed by
-- its own single atom.  An explicit permutation lands the family on
-- {{0,1,2},{1,2,5},{0,2,4},{0,1,3}}.  First quadruple-free door closed.
import Gtz.Quantitative.ThreeTripleDoorReduction


-- the all-double door, COMPLETE: at profile (0,0,6,0) the dual multigraph on
-- the four blocks is three-regular with six edges, so the family is the
-- simple K4 — atoms biject with block pairs, the TETRAHEDRON M(K4) — or a
-- doubled edge with its forced complementary double, the DOUBLE-DOUBLE.
-- The first block's three atoms each name one companion block: injective
-- assignment gives the tetrahedron, a repeated target the double-double, a
-- triple target collides two blocks.  Explicit permutations land the shapes
-- on {{0,1,2},{0,3,4},{1,3,5},{2,4,5}} and {{0,1,2},{0,1,3},{2,4,5},{3,4,5}}.
import Gtz.Quantitative.AllDoubleDoorReduction


-- the two-two-two door, COMPLETE: at profile (0,2,2,2) the two triple atoms
-- miss one block each.  A shared miss gives the TRIDENT (three blocks
-- through the triple pair, the miss block pairing the doubles with the
-- leftover).  Split misses sort by where the two pair-completing atoms
-- land: the ZIGZAG, the TWIN-PAIRS, the HOOK, and the NESTED shape.  All
-- five relabel onto explicit canonicals; twelve of the fifteen census
-- representatives are pinned.
import Gtz.Quantitative.TwoTwoTwoDoorReduction


-- the pendant door, COMPLETE — and with it THE WHOLE CENSUS: at profile
-- (0,1,4,1) the single atom either sits in the triple atom's miss block
-- (the DOUBLE-PATH: the four doubles chain end-to-end through the thread
-- blocks) or completes a thread block beside a partner double, which
-- either avoids the miss block (the PENDANT-SPLIT) or sits in it (the
-- PENDANT-FORK).  All fifteen representatives of covering four-families
-- of triples on six atoms are now pinned by explicit permutations.
import Gtz.Quantitative.PendantDoorReduction


-- the fifteen-family dispatch: the census wired end to end.  Every crux
-- whose argmax family has four blocks relabels to a crux whose argmax
-- family IS one of the fifteen canonical covering four-families — the
-- quadruple doors via the quad dispatch, the quadruple-free profiles via
-- their door capstones and the relabelling transport.  The rung-4
-- classifier is complete; the leaf-exit wave has fifteen concrete targets.
import Gtz.Quantitative.FifteenFamilyDispatch

-- ============================================================
-- THE WAVE: the rung-4 leaf-exit stack, ported from the verified
-- Codex scratch campaign (backup 2026-08-11) onto today's tree.
-- Fifty modules: the support-layer row-span aggregator, the
-- stationarity dichotomy driver (full support or pair support with a
-- three-row cancellation), the shared-edge and orbit-aligned spectral
-- exits, and the conditional family kills the fifteen-family
-- classifier feeds.  Superseded scratch layers were dropped for their
-- landed tree twins (FourActiveCoefficientProjection, CapturedRankFloor,
-- StrongStationarityIndexFloor); three files are slimmed to their
-- non-superseded remainder.
-- ============================================================
import Gtz.Wave.TypeNineAlignedOperatorExit
import Gtz.Wave.Index46CFreeExit
import Gtz.Wave.FourRowCoefficientProjection
import Gtz.Wave.RankOneCapturedRangeFloor
import Gtz.Wave.RankOneCaptureBridge
import Gtz.Wave.CapturedRankTraceGap
import Gtz.Wave.CapturedAmbientTraceGap
import Gtz.Wave.ThreeRowCapturedDichotomy
import Gtz.Wave.StationaryPositiveSupport
import Gtz.Wave.CanonicalSharedEdgeClosure
import Gtz.Wave.PrivateMultiplierFloor
import Gtz.Wave.StationaryFinThreeReindex
import Gtz.Wave.PositiveSupportTwoBlockExit
import Gtz.Wave.ThreeBlockStationaryClosure
import Gtz.Wave.GtzEFourRowSpan
import Gtz.Wave.SharedEdgeSpectralSeparation
import Gtz.Wave.ZeroLeakPair
import Gtz.Wave.GlobalZeroLeakFloor
import Gtz.Wave.SharedEdgeAmbientWrapper
import Gtz.Wave.ComplementCrossCruxExit
import Gtz.Wave.SupportThreeNonzero
import Gtz.Wave.PosDefFourActiveExit
import Gtz.Wave.ThreeRowAmbientWrapper
import Gtz.Wave.SupportThreePositiveCollapse
import Gtz.Wave.SharedEdgePathSpectrum
import Gtz.Wave.SharedEdgeSpectralTraceGap
import Gtz.Wave.ZeroFullTwoPositiveTraceGap
import Gtz.Wave.FourActiveSpine
import Gtz.Wave.FourActivePositiveMultipliers
import Gtz.Wave.ComplementRankOneCapture
import Gtz.Wave.FourActiveRankSplit
import Gtz.Wave.PositiveRowSpanRankFloor
import Gtz.Wave.ActiveBlockKernelPromotion
import Gtz.Wave.OrbitFourCoefficientBridge
import Gtz.Wave.SupportTypeEightTraceFloor
import Gtz.Wave.TypeEightProjectionTraceFloor
import Gtz.Wave.TypeNineAlignedOrthogonalExit
import Gtz.Wave.OrbitFourAlignedSimilarity
import Gtz.Wave.OrbitFourAlignedFrame
import Gtz.Wave.OrbitFourAlignedSelfAdjoint
import Gtz.Wave.OrbitFourAlignedFullRankExit
import Gtz.Wave.ActiveKernelExchange
import Gtz.Wave.OrbitFourAlignedExchange
import Gtz.Wave.OrbitFourAlignedZeroDetExit
import Gtz.Wave.OrbitFourTypeNineSupportExit
import Gtz.Wave.FourFamilyTypeEightExit
import Gtz.Wave.Index46CruxExit
import Gtz.Wave.Index46EndpointTrace
import Gtz.Wave.CriticalBridge
import Gtz.Wave.Index46SupportExit
import Gtz.Wave.SupportProfileCombinatorics
import Gtz.Wave.CrossSupportedTightExit
import Gtz.Wave.PencilFamilyClosure
import Gtz.Wave.ChairFamilyClosure
import Gtz.Wave.TridentFamilyClosure
import Gtz.Wave.FivePathFamilyClosure
import Gtz.Wave.ThreeTripleFamilyClosure
import Gtz.Wave.DoubleDoubleFamilyClosure
import Gtz.Wave.ZigzagFamilyClosure
import Gtz.Wave.TwinPairsFamilyClosure
import Gtz.Wave.HookFamilyClosure
import Gtz.Wave.DoublePathFamilyClosure
import Gtz.Wave.IsolatedRowProjectionKill
import Gtz.Wave.KernelDependencyParallelPair
import Gtz.Wave.ResidualRowSpanHarvest
import Gtz.Wave.FullRowCrossVanishing
import Gtz.Wave.FullRowTriangleKill
import Gtz.Wave.TetrahedronFamilyClosure
import Gtz.Wave.WeightedColumnSupportBridge
import Gtz.Wave.TriangleEdgeFamilyClosure
import Gtz.Wave.PendantForkFamilyClosure
import Gtz.Wave.PendantSplitFamilyClosure
import Gtz.Wave.StationaryRelabelTransport
import Gtz.Wave.NestedFamilyClosure
import Gtz.Wave.RungFourCapstone
import Gtz.Wave.RungFourIndexFloor

-- the support-minimal stationary multiplier: sliding along a relation among
-- the positive-support constraint columns q_C q_C^T keeps the assembly
-- literally unchanged, and the trace budget forces both signs, so every
-- datum reduces to one with linearly independent positive constraint columns.
import Gtz.Wave.AssemblyMinimalSupport

-- the support cap: positive tight directions span exactly the assembly's
-- range, the constraint columns live in the symmetrised pair span of a
-- basis of that range, and independence caps the positive support at
-- r(r+1)/2 -- ten, fifteen or twenty-one blocks along the rank survivors.
import Gtz.Wave.AssemblySupportCap

-- the residual-row cancellation, freed from the four-count: the engine of
-- the fifteen kills consumed its active count in one cardinality clause
-- only, and the count-free restatement is the working interface of the
-- rank-four generalization.
import Gtz.Wave.ResidualRowCancellation

-- the tight-direction basis: the exact span law hands every stationary
-- datum a labelled basis of range Xi drawn from the positive support, the
-- carrier of the campaign's coefficient coordinates.
import Gtz.Wave.AssemblyBasisSelection

-- the basis columns: the labelled basis as a size x r matrix with column
-- space equal to range Xi, full column rank, a matrix left inverse, and
-- the absorption identity B (L X) = X on column spaces inside col B --
-- the engine of the coefficient H-form.
import Gtz.Wave.AssemblyBasisColumns

-- the coefficient H-form: with B the labelled basis columns and L a left
-- inverse, M = L P B and H = L Xi L^T satisfy P B = B M, M^2 = M,
-- B H B^T = Xi and H^T = H at every active count -- the repair of the
-- four-active identification B B^T = Xi.
import Gtz.Wave.AssemblyCoefficientForm

-- the coefficient laws: the coordinate Gram is positive semidefinite by
-- congruence and has trivial kernel by the rank chain, and the exchange
-- law M H = H M^T is the chart commutation in coefficient coordinates.
import Gtz.Wave.AssemblyCoefficientLaws

-- the coefficient trace: tr (L P B) = rank (P Xi), because M represents
-- the chart restricted to range Xi and an idempotent's trace is its rank.
import Gtz.Wave.AssemblyCoefficientTrace

-- the enumerated basis: the finset basis becomes an injective Fin r family
-- of positive labels, with r literally the assembly rank, so the
-- coefficient layer applies with no cast at the call site.
import Gtz.Wave.AssemblyBasisEnumeration

-- the rank-four normal form: a support-minimal multiplier, four positive
-- basis labels, and the coefficient coordinates L, M, H with every landed
-- law and tr M = 2 -- the single interface of the first rank rung.
import Gtz.Wave.RankFourNormalForm

-- the coordinate dictionary: every positive tight direction reconstructs
-- through the basis, q = B (L q), so an extra positive label is a circuit
-- over the basis rather than free data.
import Gtz.Wave.AssemblyCoordinates

-- the circuit equations: at every atom outside a positive label's block
-- the coefficient combination of the basis directions vanishes -- the
-- linear system the rank-four census solves against the basis supports.
import Gtz.Wave.AssemblyCircuitEquations

-- the datum support dichotomy: the ambient support of every active datum
-- direction has exactly two or three atoms -- the sign engine on the block
-- submatrix, reconstituted from the coordinatewise tight equation.
import Gtz.Wave.DatumSupportDichotomy

-- the basis coverage law: the constant diagonal forces every atom into the
-- datum tight support of a positive label, and the reconstruction pushes
-- the coverage onto the basis supports.
import Gtz.Wave.AssemblyBasisCoverage

-- the rank relabelling transport: a permutation conjugation keeps the
-- assembly rank, the datum supports and the positive support transport as
-- images -- the bridge the census dispatch composes with the normal form.
import Gtz.Wave.RankFourRelabelTransport

-- the support-quadruple census: the mass count forces the trichotomy --
-- a card-two support, or a private atom, or exact double coverage -- and
-- the dispatch hands each rank-four datum to its kill group.
import Gtz.Wave.SupportQuadrupleCensus

-- the private-atom coefficient geometry: the circuit kill at the private
-- slot, the diagonal pin M_ss = value + weight, and the leak dictionary --
-- all at the abstract positive-support datum, no argmax quantification.
import Gtz.Wave.PrivateAtomGeometry

-- the coefficient projection window and the Gram sum: M H and H - M H are
-- positive semidefinite, and H is the multiplier sum of coefficient atoms.
import Gtz.Wave.CoefficientProjectionWindow

-- the Gram localization at a private atom: the private slot's Gram row
-- reads only the labels that carry the private atom.
import Gtz.Wave.PrivateAtomGramLocalization

-- the capture form B (M H) B^T = P Xi, and the private diagonal reading
-- of every conjugated form through the single surviving coordinate.
import Gtz.Wave.CoefficientCaptureForm

-- the all-private kill: four private atoms exhaust the trace budget --
-- the four diagonal pins force value >= 1/4 against the negative value.
import Gtz.Wave.AllPrivateSlotsKill

-- the private slot extraction: a multiplicity-one atom yields its private
-- slot with the block membership and the vanishing of the other columns.
import Gtz.Wave.PrivateSlotExtraction

-- the pinned dispatch: branch two of the census carries its diagonal pin,
-- the Gram diagonal is positive, and the private square law reads 1/size.
import Gtz.Wave.PinnedSupportDispatch

-- the capture tightness: (M H)_ss = (value + weight) H_ss at each private
-- atom, and a zero diagonal entry of a PSD matrix kills its column.
import Gtz.Wave.PrivateAtomCaptureTightness

-- the two-carrier dictionary: the conjugated diagonal at a shared atom
-- collapses to the four core entries on the two carrier slots.
import Gtz.Wave.TwoCarrierDictionary

-- the off-block column identity: with a fully private slot, the projected
-- off-block column splits into the shifted-weight part and the private
-- part, and the left inverse reads the diagonal coefficient.
import Gtz.Wave.OffBlockColumnIdentity

-- the conjugation trace transfer: a kernel-free intertwiner Q A = D Q
-- forces trace A = trace D.
import Gtz.Wave.ConjugationTraceTransfer

-- the fully-private-block kill: a private block exhausts the trace budget
-- through the off-corner intertwiner and the diagonal pin.
import Gtz.Wave.FullyPrivateBlockKill

-- the all-private-support kill: the census clause with one fully private
-- support assembles the enumerations and dies against the trace budget.
import Gtz.Wave.AllPrivateSupportKill

-- the private-support split: full privacy or a shared atom.
import Gtz.Wave.PrivateSupportSplit

-- the capture symmetry: the exchange law makes M H symmetric.
import Gtz.Wave.CaptureSymmetry

-- the carried row reading: the pointwise coefficient law at a block atom,
-- and its two-carrier collapse.
import Gtz.Wave.CarriedRowReading

-- the dense eigenpair trace: two independent eigenvectors read the trace
-- of a two-by-two matrix, and a shared support supplies them.
import Gtz.Wave.DenseEigenpairTrace

-- the shared-support pair trace: two slots on one shared support read
-- their diagonal sum as two shifted weights.
import Gtz.Wave.SharedSupportPairTrace

-- the two-shared-pair kill: two shared supports exhaust the trace budget.
import Gtz.Wave.TwoSharedPairKill

-- the coefficient corner window: corner minors under a diagonal Gram.
import Gtz.Wave.CoefficientCornerWindow

-- the corner characteristic: an eigen atom prices the corner determinant,
-- and the complement minor caps it at the shifted weight.
import Gtz.Wave.CornerCharacteristic

-- the complete-pair kill: six pair atoms exhaust the corner budget.
import Gtz.Wave.CompletePairKill

-- the corner trace bounds: one eigen atom caps the corner trace, and two
-- independent eigen atoms read it exactly.
import Gtz.Wave.CornerTraceBounds

-- the cycle kill: one independent double on a four-cycle exhausts the
-- trace budget under a diagonal Gram.
import Gtz.Wave.CycleQuadKill

-- the diagonal Gram supply: a basis-only positive set makes the Gram
-- core the diagonal of the basis weights.
import Gtz.Wave.DiagonalGramSupply

-- the triple-pair sector kill: three atoms on one pair force two shared
-- supports on the six-atom shape, and the sector dies.
import Gtz.Wave.TriplePairSectorKill

-- the carrier-pair extraction: a multiplicity-two atom yields its dense
-- carrier pair.
import Gtz.Wave.CarrierPairExtraction

-- the chart block ceiling: every block value sits below the objective,
-- with no minimality input.
import Gtz.Wave.ChartBlockCeiling

-- the ceiling margin kill: a block that dominates a margin above the
-- objective kills the chart point.
import Gtz.Wave.CeilingMarginKill

-- the ambient ceiling toolbox: the sparse lift calculus, the ambient
-- margin kill, the domination kills, the explicit-triple interface, and
-- the parallel combination layer.
import Gtz.Wave.AmbientCeilingToolbox

-- the parallel concentration layer: the both-parallel dichotomy at the
-- C4 shape — the dependent concentrations die on the left inverse, and
-- the independent concentrations export the scaled coordinate singles.
import Gtz.Wave.ParallelConcentrationLayer

-- the gap row dictionary: eigen rows in entry form, the range
-- invariance, the span bridge, the collapse calculus with the evaluated
-- reads, the row squares, and the pair-plane column reads.
import Gtz.Wave.GapRowDictionary

-- the dense share dichotomy: the multigraph dispatch of the dense branch
-- — the K4 profile or two disjoint doubled pairs, with the degree law,
-- the full-share kill, and the routed dense-branch closure.
import Gtz.Wave.DenseShareDichotomy

-- the doubled-pair closure: the full-share omega, the exact split, the
-- cycle normalization, the atom labeling, the support enumeration, and
-- the oriented routed closure of the dense branch.
import Gtz.Wave.DoubledPairClosure

-- the rank-four rung assembly: the frame, the five named closures, the
-- branch discharges, the K4 labeling, and the rung modulo the closures.
import Gtz.Wave.RankFourRungAssembly

-- the support-two closure supply: the pair extraction, the pair row laws,
-- the multiplied identities, and the label energy calculus with the
-- energy floor -value <= sum w q^2.
import Gtz.Wave.SupportTwoClosure

-- the coefficient engine core: the idempotency products, the
-- division-free pricing, the doubled-pair dichotomy, e2 = 1, the master
-- identities, the vertex equations, the exchange entries, and the
-- datum-level bridges.
import Gtz.Wave.CoefficientEngineCore

-- the pencil null-form layer: the scalar null-form law, the pair pencil
-- identity, the pencil corner inequality, the doubled-pair eigenpair
-- laws, and the frame lifts.
import Gtz.Wave.PencilNullFormLayer

-- the cycle independent closure layers: the share vocabulary, the
-- double-trace kill, the pair kernel vector, the equal-squares law, the
-- kernel invariance, and the projected-kernel kill.
import Gtz.Wave.CycleIndependentClosure

-- the support-two Rayleigh kill: the pair reading calculus, the
-- trace-Rayleigh bound, the capture caps, the arithmetic squeeze, the
-- private-pair kill, and the closure bridge.
import Gtz.Wave.SupportTwoRayleighKill

-- the Gram exchange layer: the direction Gram, the second exchange law
-- Gamma M = M^T Gamma M, the two positivity laws, the diagonal and
-- support reads, the energy window, the minors, and the trace window.
import Gtz.Wave.GramExchangeLayer

-- the K4 edge coordinates: the third-slot exclusion, the off-carrier
-- vanish, the edge distinctness, the corner reads, the Gram edge
-- entries, the unit norm in edge coordinates, and the four-term
-- expansions of the exchange symmetry.
import Gtz.Wave.KFourEdgeCoordinates

-- the both-parallel kernel rigidity: the pair kernel annihilation, the
-- left-inverse pullback, the division-free collapse, the projected
-- kernel reads, the twin weights, and the equal pair diagonal.
import Gtz.Wave.BothParallelKernelRigidity

-- the both-parallel trichotomy: the span decomposition, the pair
-- dichotomy, the counting kill, the pair refusal, the parallel
-- promotion, the circuit laws, and the all-heavy gap floor.
import Gtz.Wave.BothParallelTrichotomy

-- the both-parallel diagonal core: the unit atom collapse, the class
-- separation, the effective multipliers, the diagonal-core identity,
-- the entry reads, the zero cross entry, and the commutation pricing.
import Gtz.Wave.BothParallelDiagonalCore
-- The collapse supply: the row-square masses of the diagonal core.
import Gtz.Wave.BothParallelCollapseSupply
-- The finale supply: the decomposition readers, the circuit class, the
-- five-class core, the six-atom sums, the per-triple Schur test, and
-- the four-triple finale.
import Gtz.Wave.BothParallelEffectiveEntries
import Gtz.Wave.BothParallelSchurFinale
-- The branch-one kill and the discharge: closure five modulo the cross
-- pin and the circuit closure.
import Gtz.Wave.BothParallelDiagonalKill
import Gtz.Wave.BothParallelDischarge
-- The circuit kill: the scalar certificate chain and the datum module
-- that discharge the circuit obligation of closure five.
import Gtz.Wave.BothParallelCircuitCore
import Gtz.Wave.BothParallelCircuitKill

-- The cross pin: the staged scalar certificate that pins the gap entry
-- of the two single atoms to zero at the all-parallel C4 datum.
import Gtz.Wave.BothParallelCrossPinCore

-- The cross-pin datum bridge: the folds, the entry readers, the branch
-- dichotomy, and closure five without hypotheses.
import Gtz.Wave.BothParallelCrossPin

-- the shared-pair outer reduction: the row reads, the entry
-- Cauchy-Schwarz, the gap floor, the singleton kill, the same-pair
-- kill, the narrowing window, and the refined closure-one bridge.
import Gtz.Wave.SharedPairOuterReduction

-- the rank-five normal form: the support-minimal reduction, the
-- five-label basis, the coefficient coordinates, the H-form, the
-- exchange law, and the captured-trace disjunction tr M = 2 or 3.
import Gtz.Wave.RankFiveNormalForm

-- the support-quintuple census: the independence cap, the fully
-- private kill, the quintuple trichotomy with the heavy atom, and
-- the pinned dispatch of the rank-five rung.
import Gtz.Wave.SupportQuintupleCensus

-- the rank-five rung assembly: the frame, the three named closures,
-- the inline fully-private discharge, and the rung modulo the
-- closures.
import Gtz.Wave.RankFiveRungAssembly

-- the rank-five closure supply: the shared-block cap at the two
-- rungs, the private-pair kill, the same-pair kill, and the
-- outer-sharer bridge of closure one.
import Gtz.Wave.RankFiveClosureSupply

-- the rank-five dense structure: the support-block identity, the
-- heavy-atom carrier triple, and the doubled-cover law.
import Gtz.Wave.RankFiveDenseStructure

-- the shared-pair capture narrowing: the positive entry Cauchy-Schwarz,
-- the complement conjugation, the sign law, the squeeze supply, the
-- zero propagation, and the positive closure-one bridge.
import Gtz.Wave.SharedPairCaptureNarrowing

-- the pair wedge calculus: the kernel row laws, the sharer wedge laws,
-- the wedge energy window, the aligned-wedge kill, and the wedge
-- closure-one bridge.
import Gtz.Wave.PairWedgeCalculus

-- the pair coupling calculus: the split diagonals, the separated
-- sharer laws, the aligned annihilation, the third-diagonal pricing,
-- the protrusion law, the kernel read, and the wedge energy demand.
import Gtz.Wave.PairCouplingCalculus

-- the cycle seam reduction: the share calculus, the corner trace law,
-- the parallel weight pin, the pattern transport, the seam
-- certificate, and the closure-four discharge.
import Gtz.Wave.CycleSeamReduction

-- the K4 certificate reduction: the edge extraction from the unit
-- pair shares, the support identification, and the closure-three
-- discharge at the identity slot pattern.
import Gtz.Wave.KFourCertificateReduction

-- the certificate corner backbone: the corner product law, the pair
-- trace and det laws, the corner det sum, the two excess balances,
-- the uncarried solves, and the Gamma factorization with the two
-- positive semidefinite laws.
import Gtz.Wave.CertificateCornerBackbone

-- the shared-private certificate reduction: the generic kill target
-- over the basis count, the captured-diagonal boundary laws, the
-- strict weight floor, and the three bridges that discharge the
-- shared-private closures of ranks four, five, and six.
import Gtz.Wave.SharedPrivateCertificateReduction

-- the complement-trace calculus: the leak calculus of a corner read,
-- the masked trace floor, the carrier cap, the pin-set budget, the
-- interior kills at trace two and trace three, the boundary upgrade
-- at a zero captured diagonal, and the diagonal-Gram interior
-- discharge of the shared-private kill target.
import Gtz.Wave.SharedPrivateComplementTrace

-- the shared-private strata dispatch: the two-carrier corner cap, the
-- refined three-class budget, the trace-split kill that makes every
-- trace-three datum interior, the refined diagonal-Gram discharge,
-- the three named residues, and the strata dispatch with the three
-- rung compositions.
import Gtz.Wave.SharedPrivateStrataDispatch

-- the kernel-residue decomposition: the column Gram exchange law, the
-- projection split into the frame part plus a kernel residue with the
-- six laws, and the datum residue with the boundary heavy floor.
import Gtz.Wave.SharedPrivateKernelResidue

-- the shared-private kernel Gram: the split energies of a read against
-- the coefficient idempotent, the cross laws, the kernel-free Gram
-- bound, the trace floor of a fixed family, the read frame package
-- with the boundary kernel law, and the disjoint-family kill.
import Gtz.Wave.SharedPrivateKernelGram

-- the shared-private boundary dispatch: the boundary carrier cap, the
-- four-class budget, the pin-boundary count law, the multiplicity
-- arithmetic that puts the basis count above three, the rank-four
-- rigidity, the private-slot independence kill, the pin-complement
-- law, and the two narrowed boundary residues.
import Gtz.Wave.SharedPrivateBoundaryDispatch

-- the kernel-minor budget: the minor calculus of a symmetric idempotent,
-- the singular corner at kernel trace two, the corner minor identity at
-- carriers of one, two and three slots, the kernel-minor kill, the
-- deficit profile at basis count five, and the two deficit residues with
-- the extras fold.
import Gtz.Wave.SharedPrivateKernelMinor

-- the kernel factorization: the trace-zero law, the rank-two split of a
-- trace-two symmetric idempotent, the width-free corner minor identity,
-- the width-free kernel-minor kill, the datum kill on the whole
-- kernel-trace-two stratum, the complementary support law, and the
-- sharper deficit dispatch.
import Gtz.Wave.SharedPrivateKernelFactor

-- the spectral split: the rank-one action, the orthonormal rank-one sum
-- of a symmetric idempotent at every natural trace, the carrier energy
-- matrix with its trace and its eigenvalue law, and the split at the
-- shared-private datum at every kernel gap.
import Gtz.Wave.SharedPrivateSpectralSplit

-- the read intertwiner: the read matrix of a diagonal-Gram datum, the
-- intertwiner law between the slot projection and the chart, the read
-- weight matrix with its unit trace and its commutation, the faithful
-- assembly at basis count six with the interior window, and the two
-- interior deficit residues.
import Gtz.Wave.SharedPrivateReadIntertwiner

-- the circuit geometry: the coefficient frame of a positive label, the
-- parallel criterion, the pin privacy law, the outside proportion law,
-- the pair kill at the pin block, and the split of the circuit residue
-- into the pair circuits and the wide circuits.
import Gtz.Wave.SharedPrivateCircuitGeometry

-- the capture leak: the commuting sandwich read atom by atom, the leak
-- law of every chart stationary datum with its off-block witness, the
-- cross leak law of one atom pair, the per-label capture energy, the
-- slot form at a diagonal Gram core with the missing-slot law and the
-- slot mass lattice, the pair circuit geometry, and the two narrowed
-- residues with the dispatch.
import Gtz.Wave.SharedPrivateCaptureLeak

-- the shared-private boundary complement: the carrier cap of the
-- rank-four rigidity, the rank-four minor kill at shared slot pairs,
-- the partition law of a disjoint support pair, the complement slot,
-- and the narrowed rank-four residue with the four dispatches.
import Gtz.Wave.SharedPrivateBoundaryComplement

-- the shared-private Gram commutation: the kernel invariance of the
-- read Gram, the all-boundary kill through the span law, and the
-- boundary propagation at a unique co-carrier atom.
import Gtz.Wave.SharedPrivateGramCommutation

-- the shared-private slot energy: the slot energy identity and its
-- Cauchy-Schwarz cap, the multiplicity-one boundary law, the pin-slot
-- propagation, the dead-slot law with the interior floor, the
-- triangular triple kill, the closed rank-four complement residue, and
-- the boundary residue narrowed to basis count five.
import Gtz.Wave.SharedPrivateSlotEnergy

-- the kernel chain: the back substitution at every family size, the
-- general trace floor of a triangular kernel-fixed family, the three
-- kernel witnesses with the dead-slot column law, the chain kill with
-- its quadruple and private-slot corollaries, the double-cover budget
-- with the single-cover slot, the private-slot structure at trace two,
-- and the narrowed basis-count-five residue with the five dispatches.
import Gtz.Wave.SharedPrivateKernelChain
import Gtz.Wave.SharedPrivateConfinement

-- the leak energy of an interior read: the column calculus of a
-- symmetric idempotent, the leak energy identity off the carrier, the
-- co-carrier floor and the carrier floor, the solitary co-slot law, the
-- kernel leak relation, the commutation term calculus with the unique
-- separator leak law, the zero-leak line of two columns, the disjoint
-- co-carrier kill of an interior triple, and the narrowed residue with
-- its five dispatches.
import Gtz.Wave.SharedPrivateLeakEnergy

-- the dual read of a fixed vector: the read combination calculus, the
-- commutant law that keeps a fixed combination fixed, the solitary dual
-- read kill and the dual pair, the plane of a trace-two idempotent with
-- its dual vector, the plane trace of two eigenvectors, the
-- double-carrier trace identity, the full read frame, the interior
-- triple, the shared carrier kill, and the narrowed residue with its six
-- dispatches.
import Gtz.Wave.SharedPrivateDualRead

-- the co-parallel columns and the nonzero leak: the column resolution of
-- a symmetric idempotent, the dichotomy that either joins the special
-- column to the parallel family or prices its diagonal entry at one, the
-- read combination of a two-seer probe, the nonzero leak of the second
-- seer, the interior dual seers, and the unique separator kill.
import Gtz.Wave.SharedPrivateCoparallelColumn

-- the residual line: the residuals of the three interior reads are
-- multiples of one kernel line, the line is alive at every live slot,
-- the fixed parts carry a plane dependency that each slot reads as one
-- linear equation, the carrier mass law puts a slot with the whole
-- triple, a second such slot degenerates the line, three singleton
-- slots refuse the dependency, and the carrier residue, the leak
-- residue, the confined residue, the core residue, the basis-count-five
-- stratum and the whole trace-two boundary stratum become theorems.
import Gtz.Wave.SharedPrivateResidualLine

-- the diagonal kill: the trace-two boundary residue and the trace-three
-- deficit residue are both theorems, thus a shared-private datum never
-- has a diagonal Gram core; every datum carries a nonzero off-diagonal
-- Gram entry, the extras residue and the generic kill are the same
-- statement, and the circuit residue, the width pair, the fine circuit
-- lattice, the saturated lattice and the ledger lattice each close the
-- kill and the three rung closures with no boundary hypothesis.
import Gtz.Wave.SharedPrivateDiagonalKill

-- the circuit rank-one link: the corner rows of a tight direction on a
-- triple, the wedge law, the rank-one shifted gap block of a shared
-- triple, the triple kill that refuses three basis columns on one
-- support, the basis independence reads, the split dichotomy with its
-- label collapse and pair minor, and closure two on five residues.
import Gtz.Wave.SharedPrivateCircuitRankOne

-- the circuit saturation law: the sparse probe readings, the gap
-- dictionary of a symmetric idempotent chart, the division-free budget
-- cores, the pair and triple budgets of a singular shifted gap block,
-- the row energy law with its cross energy ceiling, the dead-wedge
-- support-two collapse with its parallel shared rows, and closure two
-- on the two paid residues.
import Gtz.Wave.SharedPrivateCircuitSaturation

-- the complement ledger: the cover budget at every family size, the
-- dominated corner budget, the off-block leak law of a rank-one block,
-- the tight leak identity, and closure two on the re-cut lattice.
import Gtz.Wave.SharedPrivateComplementLedger

-- the slot case split: the defect Cauchy-Schwarz of a symmetric
-- idempotent chart, the singular budget of every set that carries a
-- kernel vector, the combination budget of two tight directions, the
-- straddle rank-one extension, the refusal of a second identical pair on
-- the complement triple, and closure two on the slot-split lattice.
import Gtz.Wave.SharedPrivateSlotSplit
-- The coefficient row law: the pair corner and the trace cover kills.
import Gtz.Wave.SharedPrivateCoefficientRow
-- The corner defect kill: the pure pair closes the identical branch at
-- basis count four.
import Gtz.Wave.SharedPrivateCornerDefect
-- The leak budget: the stationary leak law on the shared-private lattice.
import Gtz.Wave.SharedPrivateLeakBudget
-- The wedge corner: the shared pure pair closes the live wedge at basis
-- count four.
import Gtz.Wave.SharedPrivateWedgeCorner
-- The complement eigenvalue law: two shared pure atoms close the
-- identical branch and the live wedge at every basis count.
import Gtz.Wave.SharedPrivateComplementEigen

-- The pair fold: two basis slots with one support span a tight plane,
-- the fold kills the corner of the Gram core, and the identical
-- residue leaves the shared-private lattice.
import Gtz.Wave.SharedPrivatePairFold

-- the K4 certificate proof: the three opposite-pair dichotomy laws,
-- the certificate proof through the corner excess balance, and
-- closure three.
import Gtz.Wave.KFourCertificateProof

-- the cycle seam certificate proof: the pair trace law and two corner
-- products feed the dichotomy, the two branches die on the weight
-- cone, and closure four holds.
import Gtz.Wave.CycleSeamCertificateProof

-- the outer-sharer dual scaffold: the diagonal and leak certificate
-- consumers, the priced coupling of a both-pair sharer, the block
-- quadratic reads, and the one-pair outside forms.
import Gtz.Wave.OuterSharerDualScaffold

-- the outer cofactor reduction: the adjugate certificate calculus,
-- the det collapse, and the rank-four and rank-five outer-sharer
-- kills modulo the extras cap and the det-zero stratum kill.
import Gtz.Wave.OuterCofactorReduction

-- the outer cofactor span form: the span membership of every positive
-- label, the energy expansion, and the extras cap as a zero-diagonal
-- quadratic in the cross pairings.
import Gtz.Wave.OuterCofactorSpanForm

-- the outer residue collapse: the extras residue is equivalent to the
-- det-vanishing law, the residue pair is equivalent to the direct
-- kill, and the rank-six outer datum joins the kill interface.
import Gtz.Wave.OuterResidueCollapse

-- the outer block-pin budget: under a diagonal Gram core the
-- conjugated coefficient matrix is a projection, the block carriers
-- price the budget, and pinned atoms kill the three ranks.
import Gtz.Wave.OuterBlockPinBudget

-- the outer block-degree dispatch: the carrier census, the conjugated
-- frame package, the refined generic kill, and the rank-four
-- narrowing to the fully two-carrier dense branch.
import Gtz.Wave.OuterBlockDegreeDispatch

-- the outer parallel fold: parallel labels give the diagonal Gram,
-- the circuit residues name the other arm, and the compositions
-- narrow the outer data at the three ranks.
import Gtz.Wave.OuterParallelFold

-- the outer trace-three interior: a vanished shifted weight breaks
-- the gap floor at captured rank three, thus the rank-six profile
-- kill drops its interiority hypothesis.
import Gtz.Wave.OuterTraceThreeInterior

-- the outer column-Gram fold: the commuting read Gram of the basis
-- directions, the capture trace of a rank-six frame, and the rank-six
-- profile lattice that reduces closure one to two named residues.
import Gtz.Wave.OuterColumnGramFold

-- the outer zero and the profile lattice: the full-carrier kill, the
-- degree dichotomy at every rank, the outer zero of the pair column,
-- the tight census, the pin rigidity, and the boundary kernel line.
import Gtz.Wave.OuterZeroProfileLattice
-- the outer dense corner kill: the two-carrier branch of the outer datum
-- dies with no Gram hypothesis, and the circuit residue narrows
import Gtz.Wave.OuterDenseCornerKill

-- the outer circuit residue: the coefficient row calculus of a general
-- positive label, the pin dichotomy, the rank-one shifted gap block, and
-- the two narrowed circuit residues at each of the three rungs
import Gtz.Wave.OuterCircuitPinResidue

-- the atom energy and the ceiling: the atom vector and the blend, the
-- frame law, the blend identity, the escape law with its sharp ratio,
-- the confinement at a read block, the outside escape, the ceiling in
-- atom form at every triple, and the rank-six discharge from one
-- design-side residue
import Gtz.Wave.AtomEnergyCeiling

-- the atom Gram and the dominating pair: the row energy law, the trace
-- law, the idempotence law, the two nested minor certificates, the
-- dominating pair theorem at a region and off one slot, the positive
-- read space, the carrier discharge, and the polynomial residue of the
-- third rung
import Gtz.Wave.AtomGramSelection

-- the complement null kill: the basis coverage law from the constant
-- assembly diagonal, the null constructor on the complement of a
-- circuit block, the one-atom kill, the clone lattice with its
-- boundary law, and the narrowed rank-four residues.
import Gtz.Wave.OuterComplementNullKill

-- the boundary residue line: the capture frame and the capture
-- residue, the trace-one parallel law of a low-trace idempotent, the
-- boundary dichotomy at the atom axes, the boundary pair kill (at most
-- one boundary atom), the proportional-row interior law, and the clone
-- closure with no interiority.
import Gtz.Wave.OuterBoundaryResidueLine

-- the capture kernel line: the rank-one minor law of a low-trace
-- idempotent, the capture frame as a chart-fixed symmetric idempotent,
-- the chart pair minor identity of a clone pair with its three
-- positivities, the residue line and the clone split, the coplanarity
-- reading of a chart fixed direction, the three live atoms of a chart
-- null direction, the zero residue kill at a full capture trace, and
-- the two narrowed thin clone residues
import Gtz.Wave.OuterCaptureKernelLine

-- the argmax block floor: the value is the bottom of every argmax
-- block, thus the block gap dominates the value form on each supported
-- probe; the floored block calculus with the dual domination, the atom
-- independence and the chart entry law; the co-singleton kill of every
-- chart-fixed singleton and the two live atoms of the capture line;
-- the liveness of a chart-fixed direction on every floored block; the
-- confinement kill of a chart-null direction inside one floored block
-- at the three upper rungs; and the floored rank spine: the cell from
-- one floored rank-four residue plus the six upper closures.
import Gtz.Wave.ArgmaxBlockFloor

-- the capture line trichotomy: the support of the capture line has
-- one, two, or three-plus atoms; the singleton dies at the
-- co-singleton field; the pair is a clone pair with both atoms
-- interior and four coplanar atoms, handed to the pair residue; the
-- wide branch is the second residue; and the cell follows from the two
-- residues plus the six upper closures.
import Gtz.Wave.CaptureLineTrichotomy

-- the pair kill: the commutation row at the first clone atom, read
-- against the chart entries into the four coplanar atoms, evaluates
-- to the shifted weight against the pair trace excess on one side and
-- against the plane row energy on the other; equality forces the
-- shifted weight to zero or one, and interiority refuses the pair.
-- The pair residue is a theorem, and the cell rests on the wide
-- residue plus the six upper closures.
import Gtz.Wave.CaptureLinePairKill

-- the wide spectral kill: the split diagonal law prices the sandwich
-- of the assembly at the shifted weight over the size; the capture
-- line of a rank-four frame sits in the assembly kernel, thus the
-- price matrix is a rank-two form with one free direction; the
-- crux-free selection residue supplies a triple that dominates the
-- shifted diagonal strictly, and the argmax field refuses it.  Every
-- rank-four frame dies modulo the one residue, and the cell follows
-- from the residue plus the six upper closures.
import Gtz.Wave.CaptureLineWideKill
import Gtz.Wave.WideSpectralAtomForm
import Gtz.Wave.WideParityStrata

-- the rank-six normal form: the support-minimal reduction, the
-- six-label basis, the two-sided inverse, the H-form, the exchange
-- law, and the exact captured trace.
import Gtz.Wave.RankSixNormalForm

-- the support-sextuple census: the fully private kill through the
-- independence cap, the sextuple trichotomy with the heavy atom, and
-- the pinned dispatch of the rank-six rung.
import Gtz.Wave.SupportSextupleCensus

-- the rank-six rung assembly: the frame with the two-sided inverse,
-- the three named closures, the inline fully-private discharge, and
-- the rung modulo the closures.
import Gtz.Wave.RankSixRungAssembly

-- the rank-six closure supply: the block cap at the third rung, the
-- private-pair kill, the same-pair kill, the outer-sharer bridge, and
-- the doubled-pairs law of the dense branch.
import Gtz.Wave.RankSixClosureSupply

-- the dense full-carrier quantization: the heavy-atom eigenrow laws,
-- the rank-six full-carrier kill, and the rank-five trace pin.
import Gtz.Wave.DenseFullCarrierQuantization

-- the dense profile dispatch: the multiplicity census reduces each
-- dense closure to three named profile closures.
import Gtz.Wave.DenseProfileDispatch

-- the dense kernel-line dichotomy: the kernel line, the scaled
-- extension calculus, the leak square, and the heavy kernel column.
import Gtz.Wave.DenseKernelLineDichotomy

-- the dense block geometry: the block eigen system, the cofactor
-- calculus, the shared-block kills, and the carrier corner equations.
import Gtz.Wave.DenseBlockGeometry

-- the dense heavy-five structure: the block shape of the heavy-five
-- profile and the exact corner pins at a shared support.
import Gtz.Wave.DenseHeavyFiveStructure

-- the dense shared-block rank: the rank-one gap block of a shared
-- support, the sign law, and the row square budget.
import Gtz.Wave.DenseSharedBlockRank

-- the heavy-atom reduction: the deflated chart of a full-carrier atom, the
-- collapsed block system, the triangle trace cap, and the death of the
-- doubled cell of the rank-five heavy-five profile.
import Gtz.Wave.DenseHeavyAtomReduction

-- the assembly-rank capstone: the cell and the rank-three payoff
-- modulo the eleven named closures of the three rungs.
import Gtz.Wave.AssemblyRankCapstone

-- the dense ceiling collapse: the increment that removes the interiority
-- from the atom triple ceiling, the shifted weight floor that every crux
-- carries, the `(6,3)` cell from one design-side residue, the six dense
-- profile closures, the frame energy floor, and the plane pair residue
-- with its deflation at a boundary atom.
import Gtz.Wave.DenseCeilingCollapse
-- The pivot deflation and the pair extension total: the Dodgson identity of
-- the shifted Gram block, the closed form of the three-slot determinants of
-- one pair, the trace certificate, the maximal volume triple at every scale
-- mass below one quarter, and the refutation of the frame-constrained drop.
import Gtz.Wave.AtomPivotDeflation
-- The plane witness ledger: the trace law of a plane frame, the master
-- identity of a witness, the kill at general rank, the four unconditional
-- strata of the plane residue, and the plane residue in dual form with
-- seven real unknowns and no combinatorial search.
import Gtz.Wave.PlaneWitnessLedger
-- The cap reading of the plane residue: the orthonormal frame of a plane, the
-- doubled reading that makes the pair law linear, the caps of the plane and
-- their convexity, the Helly collapse of the residue to THREE atoms, the cap
-- kill, and the two-atom cap law.
import Gtz.Wave.PlaneCapHelly
-- The pivot witness ledger: the deflated Gram calculus of one pivot with its
-- exact rank-one defect, the deflated master identity and kill, four deflated
-- strata of the third rung, the share defect of every crux, the regular
-- tetrahedron as the tightness datum, and the third rung in dual form.
import Gtz.Wave.PivotWitnessLedger
-- The three-atom cap residue is a theorem: the half calculus of the doubled
-- reading, the Farkas wedge bound with its two vertex evaluations, the vertex
-- and line dispatch, the second Helly call over the disc and the three half
-- planes, and the campaign chain with no hypothesis — the pair Gram residue,
-- the pair ceiling, profile A at rank five in both forms, campaign
-- interiority, and the boundary crux kill.
import Gtz.Wave.PlaneCapTripleClosure
-- The plane pair selection theorem at rank two: a plane frame of at least
-- three atoms, with positive scales of total less than one, carries a pair
-- that dominates the identity of the plane, with the margin one plus half
-- the scale slack.  The pair test is an equivalence, and the trine shows
-- that no positive margin survives at scale total one.
import Gtz.Wave.PlanePairSelection
-- The shadow transfer: the deflated pair matrix at a pivot is the plain
-- shadow pair matrix at inflated scales plus one rank-one square, thus the
-- landed plane closure supplies the deflated pair at every budget pivot.
-- The heavy stratum closes, the ceiling holds below scale mass `13/20`,
-- and the residue narrows to the blocked stratum.
import Gtz.Wave.AtomShadowTransfer
-- The blocked residue in deflated pair form: the carrier conclusion and the
-- deflated pair conclusion are one obligation, through the converse Sylvester
-- extraction.  The single-budget window puts the doubly blocked stratum above
-- scale mass `39/50`, and the reading moment is the orthogonality law of the
-- pivot defect.  The scaled complex trine sits inside the blocked package,
-- thus the residue needs a real-only proof.
import Gtz.Wave.AtomBlockedDefect
-- The band split of the blocked residue at scale mass `39/50`: the split is
-- lossless, the band part follows from one kill at a single-budget pivot, and
-- the defect wedge calculus with the single-budget engine and the slack
-- pigeonhole arm the kill.  The deep part keeps the pivot selection open.
import Gtz.Wave.AtomDefectBandSplit
-- The product inflation engine: the transfer consumes only a product law on
-- the extra inflation of a pair, thus the uniform double budget is one
-- instance and the discounted inflation opens a strictly larger stratum.
import Gtz.Wave.AtomProductInflation
import Gtz.Wave.AtomTrineCutBand
import Gtz.Wave.AtomCutRigidity
import Gtz.Wave.AtomDeepCutRigidity
import Gtz.Wave.AtomCoherentTriangle
import Gtz.Wave.AtomIcosahedralWitness
import Gtz.Wave.AtomTriangleEnergy
import Gtz.Wave.AtomBoundaryWitness
import Gtz.Wave.InterlacingSelection
import Gtz.Wave.AtomMassOneLadder
import Gtz.Wave.AtomVertexSelection
import Gtz.Wave.AtomMarginalFoil
import Gtz.Wave.AtomIntegralityGap
import Gtz.Wave.SignatureSelection
import Gtz.Wave.SignatureMoments
-- The pivot lift of rank two to rank three: the shadow frame law, the shadow
-- mass law and the charge law of one pivot, the survivor inflation engine
-- whose product law only reads the pairs that the plane closure can return,
-- the drop set consumer that buys the death of a slot for one pair minor,
-- and the pair completion law, whose four triple determinants add to an
-- explicit polynomial in six readings of one pair.
import Gtz.Wave.PivotSchurLift
import Gtz.Wave.OrientedTriangleSign
import Gtz.Wave.SpectralSupplyCell

import Gtz.Certificates.CollarAtlas.ChartGroup01
import Gtz.Certificates.CollarAtlas.ChartGroup02
import Gtz.Certificates.CollarAtlas.ChartGroup03
import Gtz.Certificates.CollarAtlas.ChartGroup04
import Gtz.Certificates.CollarAtlas.ChartGroup05
import Gtz.Certificates.CollarAtlas.ChartGroup06
import Gtz.Certificates.CollarAtlas.ChartGroup07
import Gtz.Certificates.CollarAtlas.ChartGroup08
import Gtz.Certificates.CollarAtlas.ChartGroup09
import Gtz.Certificates.CollarAtlas.ChartGroup10
import Gtz.Certificates.CollarAtlas.ChartGroup11
import Gtz.Certificates.CollarAtlas.ChartGroup12
import Gtz.Certificates.CollarAtlas.ChartGroup13
import Gtz.Certificates.CollarAtlas.ChartGroup14
import Gtz.Certificates.CollarAtlas.ChartGroup15
import Gtz.Certificates.CollarAtlas.ChartGroup16
import Gtz.Certificates.CollarAtlas.ChartGroup17
import Gtz.Certificates.CollarAtlas.ChartGroup18
import Gtz.Certificates.CollarAtlas.ChartGroup19
import Gtz.Certificates.CollarAtlas.ChartGroup20

-- The Plücker certificate: the spread law of the determinantal weights, and
-- the dual face of the residue, which moves every scale to one side.
import Gtz.Wave.PluckerCertificate

-- The four slot rung: the dual Gram of the gap form, the count that proves
-- the rung, and the scalar criterion of the drop.
import Gtz.Wave.QuadCoverSelection
import Gtz.Wave.QuadDropSign

-- The determinantal energy of the twenty triples: the two slot marginal, the
-- moment law of the determinantal average, the flatness identity and the
-- spectral floor at one twelfth.
import Gtz.Wave.PluckerEnergySupply

-- The heavy pivot is the false ingredient of the plane route: the foil in
-- fifths, the refutation, and the gap between the plane test and the cover
-- test at a pivot.
import Gtz.Wave.HeavyPivotFoil

-- The plane test cannot be part of the selection: a second exact foil over
-- the square root of thirteen kills the plane half and the heavy half at one
-- datum.
import Gtz.Wave.PlaneRouteFoil

-- The plane test that the margin theorem actually delivers, at the factor
-- one plus half the pivot scale. Neither foil touches it, and it still
-- carries the cell.
import Gtz.Wave.PlaneMarginTarget

-- The Schur floor of the determinantal energy: Schur's inequality of the first
-- degree, summed over the ten triples of five slots, gives the tenth for every
-- frame whose six leverages are one half, and it names what is left.
import Gtz.Wave.PluckerSchurFloor

-- The shifted wedge: the per-triple floor of the campaign, applied a second
-- time to the shifted block. It reads all three symmetric functions, and one
-- step carries the per-triple half of the route past the Hermitian value.
import Gtz.Wave.ShiftedWedgeFloor

-- The determinantal weight is the wrong measure. The flat average of the
-- twenty shifted triple determinants caps at (5 - sqrt 15)/10, below the
-- Hermitian value; no nonnegative weight that reads the block determinant
-- alone survives the cuboctahedron; and the Bargmann-signed repair does not
-- survive the trine foil.
import Gtz.Wave.DeterminantalWeightKill

-- The tenth is six copies of one rank-two statement. The gap of the tenth is
-- the exact total of six local pentagon readings, one for each atom the family
-- drops, and each reading has no frame law and no leverage in it. The residue
-- is a polynomial inequality in fifteen free numbers, sharp at the pentagon.
import Gtz.Wave.PentagonFloorReduction

-- The determinantal average of the reduced second rung, and the cap on every
-- certificate that reads only the moments of the twenty triples. The icosahedron
-- reads 1637/12015, which is ABOVE the cuboctahedron, so the extremal moves along
-- the ladder. Two exact witnesses cap the moment programme below the
-- field-agnostic ceiling, with and without the level-three energy floor, and that
-- floor 3/50 is proved here and is sharp at the icosahedron.
import Gtz.Wave.DeterminantalAverageCap

-- The pentagon floor is a theorem. Five vectors of rank three carry a plane of
-- dependencies, and the ten minors of that plane carry the margin, so the
-- residue is rank two. The tenth and the spectral supply at one tenth are now
-- unconditional.
import Gtz.Wave.PentagonFloorProof

-- The spread law is NOT the missing ingredient. The moment class, tightened by
-- the pair-minor law, the six doubled slot marginals and the doubled spread law
-- of the twenty determinants, still caps every per-triple floor at
-- 2107/17000 = 0.1239412, below the field-agnostic ceiling (3 - sqrt 5)/6. The
-- witness is the three-cut weight table, and it fails only the level-three
-- energy floor and the tenth.
import Gtz.Wave.SpreadWeightCap

-- The tenth carries the determinantal average PAST the field-agnostic ceiling.
-- Under the moment class augmented by E2 <= 10 E3 the determinantal average of
-- the smallest eigenvalue is at least 141/1000 = 0.141, against the ceiling
-- (3 - sqrt 5)/6 = 0.1273220. One polynomial inequality in the three eigenvalues
-- of one block carries the whole proof. The sharp cap of the route is the exact
-- (2 - sqrt 2)/4, read at a member of the class, so 1/6 is out of reach here.
import Gtz.Wave.TenthAverageFloor
-- The involution block form: the Jacobi block law at every leverage profile,
-- the balanced cut dictionary, the triangle criterion, the path and polygon
-- laws, and the quartet pigeonhole.
import Gtz.Wave.InvolutionBlockForm
-- The full spectral-parameter Jacobi law and its first selection payoff. A cut
-- of square mass at most 4/9 has a winning side, so the landed heavy-edge
-- escape closes every balanced frame with an edge of square at least 2/3.
-- The only balanced determinant residue is the strict subcritical edge region,
-- and the module connects its determinant target to the actual 1/6 carrier.
import Gtz.Wave.BalancedCutSelection
-- The older abstract U6 theorem closes the Wave target outright.  For a
-- balanced frame, `H = 2G - I` is a hollow symmetric involution and its
-- unconditional `2/3` PSD block is exactly twice the Wave `1/6` shifted Gram
-- block.  This yields the determinant win, the sharp blend floor, and the
-- final carrier for every balanced scale at most `1/6`; the former strict
-- subcritical residue is empty.
import Gtz.Wave.BalancedInvolutionClosure
-- In weighted-design coordinates the same result selects a principal block of
-- `projectionOfDesign` above the flat `1/6` diagonal.  This is valid for every
-- uniform-share design; comparing the selected flat diagonal with the true
-- weights recovers an actual dominating triple.
import Gtz.Wave.BalancedDesignClosure
-- The complement jaw window and the needle law of the two terminal tie
-- charts. The quadratic-cap jaw closes a subset from the budget
-- tin * kappa + tout < 1, the rank-one instantiation is the C3 foil law,
-- and the engine contrapositive turns every light-weight tie into a
-- needle: the gap form reads at least (1 - 2 tau) / tau along some
-- direction, which is 8 at tau = 1/10 — the lower window edge of the
-- needle chart as a theorem. The rank-two jaw prices the needle at the
-- sharp cap 1 + s1 through Bessel, the weld rivet turns every carrier
-- floor into a strictness certificate on its light region, and the
-- light-atom pigeonhole makes a needle eat its own carrier's weight.
import Gtz.Ties.ComplementJawWindow
-- The exact pair criterion, the strictness engine, and the isotropy spread.
-- The strict plane pair test is an equivalence in gap and in budget
-- coordinates, the active budget returns a strict pair at scale total one, and
-- every plane frame carries a sixty-degree pair — sharp at the trine, real
-- only by the Bloch tetrahedron.
import Gtz.Wave.PlanePairCriterion
-- The complete three-atom plane tie classification.  The open tie simplex is
-- inhabited exactly when every atom mass exceeds one half, then its weight is
-- uniquely `2 * mass - 1`; every pair is weakly tied with an explicit kernel
-- probe.  The same module supplies the arbitrary-cardinality active-set W
-- engine used by the terminal descent charts.
import Gtz.Wave.PlaneTieClassification
-- The design-level adapter for the exact plane boundary.  On scaled atom rows,
-- plane strictness is core `PosDef`, weak plane domination is core
-- `PosSemidef`, and the closed-form weight equation is exactly `IsTie` for a
-- weighted `(3,2)` design.  Each tied pair is exported with its PSD singular
-- gap, determinant zero, nonparallel bracket, and an actual nonzero kernel.
import Gtz.Wave.PlaneTieDesignBridge
-- The descent weld spends all three preceding layers. Every balanced frame at
-- scale at most `1/6` now produces the actual carrier unconditionally; light ties
-- carry an eight-needle on every triple and die against one strict gap cap;
-- the nonuniform three-atom plane endpoint is now completely decided by the
-- weights.  Off `2 * mass - 1` a strict pair exists; at that one weight vector
-- every pair is weakly tied, nonparallel, and carries an explicit kernel probe.
import Gtz.Wave.DescentWeld
-- The projection dictionary and its first payoffs. Domination of a picked
-- triple is the synthesis floor of the atom blends and the weighted Gram
-- reading, the block determinant is the Gram block determinant, the uniform
-- (4,2) cell holds, weights below one tenth force a strict triple at (6,3),
-- and four pairwise-nonparallel active plane slots push the no-strict budget
-- strictly below the active mass minus one.
import Gtz.Wave.ProjectionDictionary
-- The unconditional tenth spectral supply now reaches the A1 registry
-- consumer.  A square-transpose floor closes every design with all weights
-- below `1/10`; composed with the separated weak-direction and twenty-triple
-- balance reductions, A1 is equivalently narrowed to a tenth-heavy residual
-- carrying every previously landed pin.  The same closure is exported once
-- for every no-strict configuration and every tie.
import Gtz.Wave.TenthLightA1Wiring
-- Spend the general complement-jaw theorem in that A1 residual as well.  The
-- two pinned triple maxima give an attained positive global cap; under the
-- hypothetical no-strict ledger the base weak triple is an actual tie, so
-- every triple now carries the corresponding nonzero gap needle.  The new
-- counterexample formula is exactly equivalent to A1.
import Gtz.Wave.A1NeedleWiring
-- Leverage heaviness does not imply a large raw weight.  The same light
-- theorem therefore removes an additional region from both chartless pattern
-- obligations: their surviving residuals retain leverage heaviness and gain
-- an explicit label of weight at least `1/10`, with a generic IFF back to the
-- former pattern statement.
import Gtz.Wave.TenthLightPatternWiring
-- The chartless line obligations now spend their landed lift engines as well:
-- one line survives only in the tenth-heavy joint cap/normal blind spot, while
-- two meeting lines survive only there and at four explicit transversals.
import Gtz.Wave.TenthHeavyLineResidualWiring
-- In the one-line blind spot, every strict winner contains at most one line
-- atom.  The remaining ten triples are exactly the existing
-- `PlaneBranchTenCandidate` selector from the line-free U(3,6) plane branch,
-- so both residuals now consume one shared finite endpoint.
import Gtz.Wave.OneLineSurvivorWiring
-- The same tenth-light theorem now crosses the square-root-free chart
-- whitening dictionary.  It removes the all-light region from both remaining
-- chart obligations: A2 survives only at a tenth-heavy point in the
-- three-lines fundamental domain, and A3 only at a tenth-heavy point in the
-- doubly uncovered K4 knife band.  Both sharpenings are kernel-equivalent to
-- their former public statements.
import Gtz.Wave.TenthLightChartWiring
-- The budget cover criterion. An allocated Cauchy-Schwarz step converts each
-- outside label's mass demand into loads on the selected triple, and strict
-- load-below-budget bounds give positive definiteness outright. The two
-- canonical three-lines cells land with exact rational kernel witnesses, and
-- the consumer joint reduces the committed A2 obligation to a per-point
-- strict triple on the tenth-heavy fundamental domain.
import Gtz.Design.BudgetCoverCriterion
-- The unsigned cycle cells: the allocation-free upgrade of the budget
-- certificate.  For any probe the chart gap dominates the unsigned cycle form
-- at the absolute selected readings, so a cell is three leading-minor
-- inequalities in the moduli alone.  The module carries the K4 transport (the
-- gauge tree and the band tree with the fundamental-cycle expansions), the
-- exact band witness at integer minors, the two three-lines cells in the same
-- format, the heavy-label law, and the K4 registry joint.
import Gtz.Design.UnsignedCycleCells
-- Spend both allocation-free K4 cycle cells in A3.  The exact residual is now
-- outside Layer A, the exchange star, and the unsigned star/band cells; its
-- chart-heavy antecedent is removed because it is automatic.
import Gtz.Wave.KFourUnsignedCycleWiring
-- Spend both allocated three-lines cells in the A2 registry chain.  The live
-- residual is now tenth-heavy and simultaneously outside the vertex and free
-- budget certificates; IFF theorems recover both the prior tenth-heavy form
-- and the original public chart statement.
import Gtz.Wave.ThreeLinesBudgetWiring
-- The max-reading cover cell is spent after the two allocated cells, again
-- with an exact IFF back to the public three-lines obligation.
import Gtz.Wave.ThreeLinesReadingCoverWiring
-- The three dependent chart lines cannot even supply the weak antecedent; the
-- final A2 residual therefore ranges over the seventeen off-line triples.
import Gtz.Wave.ThreeLinesOffLinesWiring
-- Spend the allocation-free vertex/free cycle cells in A2 and remove the
-- redundant chart-heavy antecedent from the final off-lines residual.
import Gtz.Wave.ThreeLinesUnsignedCycleWiring
-- The unsigned trace cell: one cleared inequality per tree, the three
-- missing star cells, and the gauge-star trace corollary.
import Gtz.Design.UnsignedTraceCell
-- The coverage refuters and the pendant-family cells.  Two exact chart points
-- kill the two candidate selection dichotomies: at the first, no star
-- row-dominates and every cleared trace sits at or past its floor, but the
-- gauge-star cell fires; at the second, no star selection is positive
-- definite at all, but the pendant cell at the matching `{2, 3}` fires.  The
-- knife-band residual is the full minor atlas, and the four pendant cells of
-- that matching are landed in the master format.
import Gtz.Design.CoverageRefuters
-- The row certificate atlas.  Every unsigned cell matrix is a symmetric
-- Z-matrix, so one positive vector with three strict LINEAR row inequalities
-- gives all three minors through the matrix-tree forest identity.  The module
-- lands the scalar bridge, the row master, the seven missing path cells (all
-- sixteen spanning trees now carry moduli-only cells), the pendant row
-- corollary with the second coverage refuter as its witness at the vector
-- (8, 5, 1), and the subset pigeonhole for chart weights.
import Gtz.Design.RowCertificateAtlas
-- The Z-matrix alternative at the atlas cell shape. Three positive minors
-- give the explicit adjugate row certificate, each minor failure gives an
-- explicit dual witness, and a dual witness forces a diagonally non-dominant
-- row. The forward and reverse directions of the row bridge are now one
-- equivalence.
import Gtz.Design.ZMatrixAlternative
-- The chart-design whitening: the K4 chart is the complete-quadrilateral
-- stratum of the design problem. The moment matrix whitens through the landed
-- congruence, domination transfers as an equivalence, the four triangles are
-- never strict, and a design-level strict selection at mass one discharges
-- the committed A3 axiom verbatim.
import Gtz.Design.ChartDesignWhitening
-- The stratum squeeze. The corrected weld quantifies the strict selection
-- over the whitened family only, because the global form is false at the
-- sharp extremal. The complement dichotomy makes the star obstruction a
-- theorem: a star's complement is its opposite triangle and is never strict.
-- The squeeze producers read no tie hypothesis: a no-strict design pays the
-- jaw budget at every three-slot complement, and a weighted energy floor on
-- a non-strict subset forces a heavy weight inside the subset.
import Gtz.Design.StratumSqueeze
-- Spend the gauge trace criterion and the three newly available vertex-star
-- cells in the exact K4 residual.  The live formula is now outside all six
-- unsigned certificate cells and remains equivalent to the public knife band.
import Gtz.Wave.KFourUnsignedTraceWiring
-- Spend all four pendant cells around the `{2, 3}` matching.  Together with
-- the six previous unsigned cells this is the full ten-cell minor atlas; the
-- second coverage refuter inhabits the newly removed region exactly.
import Gtz.Wave.KFourPendantAtlasWiring
-- Spend the seven remaining path-tree cells.  The resulting seventeen-cell
-- union attaches a moduli-only certificate to every one of the sixteen K4
-- spanning trees and remains exactly equivalent to the public knife band.
import Gtz.Wave.KFourRowCertificateWiring
-- Convert failure of the seven path cells into explicit nonnegative adjugate
-- witnesses and Gershgorin bad-row alternatives, and expose that finite ledger
-- in the exact K4 residual.
import Gtz.Wave.KFourZMatrixWiring
-- Reverse the bad-budget ledger into seven existential-free polynomial cells.
-- Any one of these three-inequality cells recovers its path minor certificate
-- and therefore dispatches a strict K4 spanning tree directly.
import Gtz.Wave.KFourPolynomialBudgetCells
-- Complete the Z-matrix ledger for the nine earlier minor cells and join it
-- to the seven missing paths.  The exact A3 residual now carries a full
-- nonnegative dual witness, bad row, and cleared budget for every spanning
-- tree, rather than only for the seven paths added by the row atlas.
import Gtz.Wave.KFourAllTreeZMatrixWiring
-- Identify the design-side whitening-family selector with both strict chart
-- coverage and the exact all-tree Z-obstructed A3 residual.
import Gtz.Wave.KFourFamilySelectionWiring
-- The Gershgorin washout: one rational chart point satisfies the bad-row
-- condition of all sixteen spanning trees while nine trees are strictly
-- dominating.  The sixteen-row necessary system cannot decide coverage, so
-- a covering proof must consume more of each dual witness than its row.
import Gtz.Design.GershgorinWashout
-- Recover the information discarded by the Gershgorin projection on all seven
-- paths in the row atlas.  Alternating path signs identify each unsigned
-- Z-form exactly with a pullback of the chart gap, so a full dual witness at a
-- weak path supplies a nonzero kernel direction of the actual gap.  The exact
-- A3 registry formula consumes the resulting conditional saturation ledger.
import Gtz.Wave.KFourDualSaturation
-- Saturate the five earlier K4 paths as well: the band tree and four pendants.
-- Joined to the seven-path ledger above, all twelve path trees now carry exact
-- nonnegative Z-kernels pulled back to actual chart-gap kernel directions.  The
-- four vertex stars are the remaining sign-frustrated tree type.
import Gtz.Wave.KFourPriorPathDualSaturation
-- Classify the realized weak K4 tree after all twelve path saturations.  A
-- weak path now arrives with its actual pulled-back nonzero kernel direction;
-- the only alternative is one of the four sign-frustrated vertex stars.
import Gtz.Wave.KFourPathStarResidual
-- Compose every realized path kernel with the chart pointer theorem.  The path
-- branch now names an outside repair label whose every host selection reads
-- strictly positively on the original path's null direction.
import Gtz.Wave.KFourPathPointerResidual
-- Spend the pointer on its four-edge window.  Every saturated weak path now
-- yields a strict tree, the exact final-rung pivot wall, or two independent
-- window-kernel directions; successful deletions are removed before the
-- resulting residual formula reaches the registered A3 joint.
import Gtz.Wave.KFourPathWindowDichotomy
-- The chart gap is antitone in each selected weight, so strictness moves down
-- in weight and a covering of the chart slice covers the full cone of weight
-- sum at most one. The probe behind the module: the K4 covering fails on the
-- open orthant from weight sum 6/5 on the symmetric ray, but adversarial
-- descent over uncovered points stalls at weight sum 1.0805 — the chart slice
-- carries interior slack, and certificates below that loss are admissible.
import Gtz.Design.ChartWeightMonotone
-- The kernel pointer and the chart exchange identity. A selection that reads
-- nonpositively at a nonzero probe names an outside kappa-argmax pointer, and
-- every selection through the pointer reads strictly positively at the same
-- probe. The pointer is the repair step of the weak-to-strict obligations;
-- the directed probe refuted the hosting conjecture, so it is not a selector.
import Gtz.Design.KernelPointer
-- The star sign rigidity. In the balanced gauge every star gap pairs into a
-- matrix with strictly positive off-diagonals, so a weak-not-strict star has
-- a kernel probe whose tree readings carry both signs, and the star gap is
-- strictly positive on the nonnegative reading orthant. The four instances
-- carry explicit basis and dual vectors, and every kernel probe hands the
-- landed outside pointer.
import Gtz.Design.StarSignRigidity
-- The star kernel and generic pointer remove the path/star distinction from
-- A3. Every weak K4 tree is either already strict or reaches the same exact
-- pointer-window pivot wall or corank-two wall.
import Gtz.Wave.KFourTreeWindowResidual
-- Pull a singular pointer-window kernel back through its positive rank-one
-- update.  The A3 corank wall now exposes two independent kernels of the
-- original PSD tree gap, and the incoming pointer is orthogonal to the second.
import Gtz.Wave.KFourTreeWindowCorankReduction
-- Eliminate the corank-two wall on all twelve K4 path trees.  Their exact
-- injective pullbacks are irreducible PSD Z-matrices, whose kernels cannot
-- contain two noncollinear vectors.  The singular A3 branch is now star-only.
import Gtz.Wave.KFourPathCorankCollapse
-- Spend the generic unsigned trace theorem at the two landed three-lines
-- expansions.  The exact A2 residual is now outside both minor cells and both
-- one-inequality trace cells.
import Gtz.Wave.ThreeLinesUnsignedTraceWiring
-- The five moved `Z/3` orbits now carry the same one-inequality trace engine.
-- Certificates are checked on transformed chart masses and transported back;
-- the exact A2 residual is outside all seven orbit cells.
import Gtz.Wave.ThreeLinesMovedOrbitTraceWiring
-- The three-lines family weld: the dischargeable A2 joint.  Strict selection
-- over the whitened fundamental-domain family alone discharges the committed
-- A2 axiom, and every dominator of a realizing design is off the three
-- dependent lines.
import Gtz.Design.ThreeLinesFamilyWeld
-- The star amplified exchange: a weak-not-strict star hands a kernel probe
-- whose amplifying triangle label strictly beats two star labels in squared
-- reading, and the amplified exchange reads positively at the probe when the
-- incoming boost quotient is at least the outgoing one.
import Gtz.Design.StarAmplifiedExchange
-- The wall collapse. At the corank-two wall the window kernel collapses into
-- the tree kernel orthogonal to the pointer, so the tree gap kills a plane and
-- a distinct second outside pointer arrives. At the pivot wall the pointer's
-- own deletion pivot joins the three wall pivots at one. The mixed-only plane
-- classification identifies the strictly one-signed normals.
import Gtz.Design.WallCollapse
-- The star-only law of the corank-two wall. The two-kernel rank collapse
-- makes the tree gap a nonnegative rank-one atom, the six chart coefficients
-- take the closed form (-z0z1, -z0z2, -z1z2, z0s, z1s, z2s), and the chart
-- signs admit that form only at the four vertex stars. The corank-two wall
-- is empty over the twelve path trees, and the corank branch of the gap
-- residual always carries a star.
import Gtz.Design.StarOnlyLaw
-- The star-corank closure platform. The swap quantifier collapses to one
-- singleton inequality, the exchange bookkeeping reads any selection at a
-- kernel probe as incoming minus outgoing boosts, the gauge-star wall gets
-- its one-signed normal form, and the double-pointer package hands a second
-- star positive at both kernel directions. The vacuity target names the
-- closure route against the atlas silence of the antecedent stack.
import Gtz.Design.StarCorankClosure
-- The star-wall family coordinates and the balanced case of the vacuity
-- target.  The six wall equations pin the triangle masses and the tree boost
-- identities by a positive axis, and the balanced case fires the vertex-a
-- star cell of the minor atlas with a determinant slack factor near three.
import Gtz.Design.StarWallVacuity
-- The heavy weight cap of the gauge star wall.  The landed balanced case
-- asks every sensitive weight to be at most one sixth.  That bound is not
-- sharp: the same term-bound architecture reaches three sixteenths, and the
-- exact wall threshold is (3 - sqrt 3) / 6 at the symmetric axis.
import Gtz.Design.StarWallHeavyCap
-- The sharp weight cap of the gauge star wall.  The joint bound replaces the
-- term bound and reaches the exact threshold: the worst-demand determinant is
-- the sharp wall polynomial times the two triangle axes and the axis sum, and
-- every coefficient of that polynomial is positive exactly when the boost
-- quotient clears two plus the square root of three.  The named caps are one
-- fifth and four nineteenths.
import Gtz.Design.StarWallSharpCap
-- The two balanced mirrors: the vertex-b and vertex-c stars fire when their
-- axis coordinate is maximal and their four weights are at most one sixth.
import Gtz.Design.StarWallMirrors
-- The star-wall transport: the vertex four-cycle lifts to a unimodular chart
-- congruence, the corank-two wall data transports along it, and the four star
-- walls cycle onto the gauge wall. A strict-tree law at the gauge wall alone
-- covers every star wall; per-family case work at the other stars is not
-- necessary.
import Gtz.Design.StarWallTransport
-- Wire the two final K4 walls to their strongest landed interfaces.  The
-- positive-definite window now carries all four large pivots; the singular
-- vertex star carries a nonnegative rank-one gap and two distinct repair
-- pointers.  The resulting A3 formula is exactly equivalent to the star-only
-- residual.
import Gtz.Wave.KFourStarWallWiring
-- Spend the landed amplified exchange on every surviving vertex star.  The
-- singular wall now carries both exact exchange readings and the exhaustive
-- alternative: a positive exchange reading, or a strict two-sided boost-ratio
-- reversal.
import Gtz.Wave.KFourStarAmplifiedWallWiring
-- Retain the combinatorial content of the star amplification: both repaired
-- selections are among the sixteen K4 spanning trees.  This avoids treating a
-- positive reading on a possibly dependent card-three set as a tree witness.
import Gtz.Wave.KFourStarExchangeTreeWiring
-- Correct the last amplified-star interpretation at the corank-two wall.
-- Every one-slot repair remains non-positive-definite: the original kernel
-- plane always contains a nonzero vector orthogonal to the incoming direction.
-- The positive exchange reading is therefore a stratifier, not a selector.
import Gtz.Wave.KFourStarSingleExchangeRefusal
-- Spend the balanced gauge-star vacuity theorem under the atlas-silence
-- antecedent.  The surviving family now has a nonmaximal first axis coordinate
-- or a strictly heavy weight in one of the four vertex-a slots.
import Gtz.Wave.KFourStarBalancedVacuityWiring
-- Spend all three balanced star-wall mirrors.  Atlas silence now couples the
-- maximal positive axis coordinate to a heavy weight in its exact four-slot
-- vertex-star cover, while remaining equivalent to the registered A3 formula.
import Gtz.Wave.KFourStarMirrorVacuityWiring
-- Retain the three maximal-axis certificates simultaneously instead of
-- selecting one branch.  Tied maximal axes now force either two distinct
-- weights above one sixth or a heavy label on the exact opposite edge; the
-- fully symmetric axis always forces two distinct heavy labels.
import Gtz.Wave.KFourStarAllMaxHeavyWiring
-- The pivot-wall vacuity target and the two-wall reduction. The pivot
-- branch and the star branch of the registered residual each die against
-- atlas silence once their vacuity laws hold, so the two laws together
-- discharge the registered A3 proposition and the family selection.
import Gtz.Design.PivotWallVacuity
-- The pivot balance law: at a strict gap the coefficient-weighted inverse
-- readings sum to three.  The full selection is always strict, its pivots
-- average three fifths, and the descent to a strict tree stalls only at a
-- priced five-edge or four-edge wall — the descent trichotomy.
import Gtz.Design.PivotBalanceLaw
-- Split the final K4 residual into two callable components.  Exact four-cycle
-- transport identifies all four corank-two vertex-star walls with the one
-- gauge-star wall; solving that canonical wall together with the four-pivot
-- window wall discharges A3 and the design-side K4 family selector.
import Gtz.Wave.KFourGaugeStarTransportWiring
-- Spend the centered four-set balance and exact self-pivot update at the
-- independent pivot wall.  The former direct wall closure is now exactly the
-- conjunction of a recurrent exchanged-four-set closure and a strict
-- half-priced five-set endpoint closure, wired through A3 to family selection.
import Gtz.Wave.KFourPivotStallPropagationWiring
-- Collapse the priced five-set endpoint onto its exact zero-cross locus.  The
-- inserted edge is orthogonal to the original tree kernel and preserves that
-- kernel in the exchanged four-set; the narrowed endpoint closure remains
-- exactly equivalent to the former pivot propagation route.
import Gtz.Wave.KFourPivotEndpointOrthogonalityWiring
-- The three-lines wall architecture.  The chart is a triangle: three
-- coordinate labels and three join labels.  At a rank-one wall the six chart
-- coefficients are pinned by the axis, the three join coefficients are the
-- pairwise axis products, and their product against the slide is a square.
-- The parity of the selected join labels is therefore forced by the sign of
-- the slide, which excludes half of the twenty triples at every slide.
import Gtz.Design.ThreeLinesWallArchitecture

-- Stall confinement.  A stall is a positive definite selection every label of
-- which carries chart ladder pivot at least one, so no single deletion keeps
-- positive definiteness.  The pointer window of a K4 pivot wall is exactly a
-- four label stall, and the law confines every positive definite spanning tree
-- out of that window: the winner always meets the two label complement.
import Gtz.Design.StallConfinement
-- The unified stall law and the five-stall elimination.  A stalled selection
-- of k labels prices its complement by k - 4, so the full selection never
-- stalls, the five-edge price is the k = 5 instance, and the four-edge law is
-- the k = 4 instance.  The landed insertion law then deletes the five-edge
-- branch of the descent trichotomy: every chart point carries a strict
-- spanning tree or a stalled four-edge selection.
import Gtz.Design.PivotArmClosure
-- The card-four equivalence and the univ-descent law.  A strict spanning
-- tree exists exactly when a non-stalled positive definite four-edge
-- selection exists, so the stalled branch repackages the chart statement
-- rather than reducing it.  Every four labels hold one droppable from the
-- full selection, and a matching plus any edge is a spanning tree.
import Gtz.Design.CardFourStallEquivalence
-- The two-meeting-lines transversals price their complements.  Each of the four
-- transversal complements is the shared atom together with the two unused
-- private atoms, so a failing transversal hands the universal needle to a set
-- containing the shared atom.  The needle's complement law is weakened here
-- from a tight direction to a nonpositive one, which is what a failure of
-- positive definiteness supplies.
import Gtz.Design.TwoMeetingLinesNeedle
