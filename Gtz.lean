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
import Gtz.LinAlg.GordanAlternative
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ResolventPerturbation
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.TwoByTwo

-- Design: WeightedDesign facts: trace identity, leverage, margins, compactness
import Gtz.Design.BhatiaDavis
import Gtz.Design.CapSlack
import Gtz.Design.ClosureObtuse
import Gtz.Design.CollaredCompact
import Gtz.Design.DeflationCertificate
import Gtz.Design.DowndateInterlacing
import Gtz.Design.LeverageBound
import Gtz.Design.MarginTransfer
import Gtz.Design.StressCertificate
import Gtz.Design.SymmetryReduction
import Gtz.Design.TraceIdentity
import Gtz.Design.WhiteningDistortion

-- Reduction: the ladder: crystallization, Naimark duality, deflation, the lifting lemma
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.MaximalVolume
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
import Gtz.Quantitative.CollarFloor
import Gtz.Quantitative.CollarRate
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.FirstOrderLaw
import Gtz.Quantitative.GapStabilityFacts
import Gtz.Quantitative.Interface
import Gtz.Quantitative.MarginContinuity
import Gtz.Quantitative.OneObjectNarrowing
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Quantitative.RealnessEngine
import Gtz.Quantitative.StrictDomination
import Gtz.Quantitative.TwoMomentCertificate
import Gtz.Ties.StratumFirstOrder
import Gtz.Ties.StratumSharpMaximum
import Gtz.Reduction.MixedCharPolynomial

-- Complex: the complex refutations: weighted (4,2) and (6,3) are false over C
import Gtz.Complex.ComplexPadding
import Gtz.Complex.ComplexWitness

-- Ties: exact ties and the corank-one classification
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Ties.CorankOneTieExistence
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

-- the axiom ledger for everything above
import Gtz.Audit
import Gtz.Quantitative.PositivstellensatzRankThree
