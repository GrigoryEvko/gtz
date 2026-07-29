/-
# Audit: axiom hygiene for everything claimed proven (FX discipline)

Every non-private theorem in every `Gtz.*` module is listed here with
`#print axioms`, so each build displays exactly what it rests on. Expected axiom
set for Mathlib-backed proofs: `propext`, `Classical.choice`, `Quot.sound` — and
NOTHING else. In particular `sorryAx` appearing for any theorem listed here is a
broken promise; roadmap statements carrying `sorry` are deliberately NOT listed.

Coverage is a maintained invariant, not an aspiration, and it has drifted
twice. A first adversarial audit found 162 proved public theorems silently
absent; a second found 72 more, together with four modules this file reached
only transitively and so could not name. All were axiom-clean, so both defects
were documentary — but the docstring had promised total coverage it did not
deliver. Each gap was closed by enumerating every `theorem`/`lemma` in `Gtz/`
and appending what was absent. The one deliberate exclusion is
`Gtz/Ties/DiamondTie.lean`, which no module imports and which duplicates
`Gtz/Design/DiamondPrimitive.lean`.

If you add a theorem, add its line; the list is checked by re-running that
enumeration, and the honest long-term fix is a meta-level probe that enumerates
`Gtz.*` constants and asserts the axiom set, which cannot drift.

Definitions are listed selectively — the ones whose junk-value or `noncomputable`
behaviour is load-bearing — not exhaustively.

Update this file in the same commit that completes a proof.
-/
import Gtz.Design.BhatiaDavis
import Gtz.Core.Sanity
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.TraceIdentity
import Gtz.Certificates.TriangleClosure
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.CollaredCompact
import Gtz.Quantitative.MarginContinuity
import Gtz.Design.StressCertificate
import Gtz.Quantitative.StrictDomination
import Gtz.Ties.DominationWithoutCertificate
import Gtz.Ties.SplitClassTieFamily
import Gtz.Ties.SplitTetrahedronTie
import Gtz.Ties.SplitTetraLocalBalance
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Ties.RepeatedAtomExclusion
import Gtz.Ties.SelectionObstruction
import Gtz.Ties.NonTetrahedralTie
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Ties.CorankOneTieExistence
import Gtz.Quantitative.OneObjectNarrowing
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.GapStabilityFacts
import Gtz.Quantitative.RealnessEngine
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Quantitative.TwoMomentCertificate
import Gtz.Ties.StratumFirstOrder
import Gtz.Ties.StratumSharpMaximum
import Gtz.Reduction.MixedCharPolynomial
import Gtz.Certificates.FrameBridge
import Gtz.Quantitative.CollarRate
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.ChargeSelection
import Gtz.Quantitative.CapArgmax
import Gtz.Quantitative.CapBoundaryConstant
import Gtz.Corner.CornerFiber
import Gtz.Corner.CapCriterion
import Gtz.Reduction.Crystallization
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.Completion
import Gtz.Reduction.Naimark
import Gtz.Reduction.Reductions
import Gtz.Reduction.RatCertificate
import Gtz.Reduction.RatCertificateInstance
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.CertificateBall
import Gtz.Planar.PlanarPlatform
import Gtz.Planar.BlochDictionary
import Gtz.Planar.DustControl
import Gtz.Planar.LawCounterexample
import Gtz.Planar.Pushoff
import Gtz.Planar.TightGraph
import Gtz.Planar.CertificateFrame
import Gtz.Planar.MomentCovector
import Gtz.Reduction.Compression
import Gtz.Reduction.DescentLadder
import Gtz.Quantitative.FirstOrderLaw
import Gtz.Quantitative.CollarFloor
import Gtz.Design.CapSlack
import Gtz.Corner.QuantitativeCorner
import Gtz.Planar.StressFrame
import Gtz.Complex.ComplexWitness
import Gtz.Planar.Seam
import Gtz.Complex.ComplexPadding
import Gtz.Planar.PThreeStratum
import Gtz.Planar.CollinearStratum
import Gtz.Planar.MomentBound
import Gtz.Corner.CornerResolvent
import Gtz.Planar.SilenceDictionary
import Gtz.Planar.BallPerturbation
import Gtz.Planar.EulerPairing
import Gtz.Planar.SplittingRule
import Gtz.Planar.ChordTheorem
import Gtz.Planar.LocalLaw
import Gtz.Planar.Completeness
import Gtz.LinAlg.ResolventPerturbation
import Gtz.LinAlg.CongruenceRobustness
import Gtz.LinAlg.EigenvalueSubdifferential
import Gtz.Corner.IdempotentSplitting
import Gtz.Planar.LeafTangency
import Gtz.Corner.CapDictionary
import Gtz.Design.MarginTransfer
import Gtz.Corner.AggregatePushoff
import Gtz.Corner.CornerPerturbation
import Gtz.Certificates.FrameEncoding
import Gtz.Planar.WedgeChain
import Gtz.Certificates.CertificateAnchor
import Gtz.LinAlg.BernsteinPositivity
import Gtz.LinAlg.GordanAlternative
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.MaximalVolume
import Gtz.Reduction.ExchangeInvariant
import Gtz.Ties.TetrahedronTie
import Gtz.Ties.TieEigenvector
import Gtz.Corner.TiedQuadruple
import Gtz.Corner.CoveringMargin
import Gtz.Design.DowndateInterlacing
import Gtz.Certificates.CyclicStress
import Gtz.Certificates.LawEquivalence
import Gtz.Design.WhiteningDistortion
import Gtz.Design.ClosureObtuse
import Gtz.Design.SymmetryReduction
import Gtz.Design.DeflationCertificate
import Gtz.Design.LeverageBound
import Gtz.Certificates.PFourCertificate
import Gtz.Certificates.CFiveCertificate
import Gtz.Certificates.GeometricExclusion
import Gtz.Reduction.LiftingLemma
import Gtz.Quantitative.Interface
import Gtz.Reduction.BranchTwoRational
import Gtz.Reduction.BranchTwoMinimal
import Gtz.Reduction.BranchTwoCompleteness
import Gtz.Reduction.PsdCongruenceConsumer
import Gtz.Reduction.PrincipalMinorsThree
import Gtz.Design.GraphicInstance
import Gtz.Quantitative.CollarExponent
import Gtz.Reduction.RankInductionStep
import Gtz.Design.LeverageCapDecision
import Gtz.Quantitative.DecisionAtlasSevenThree
import Gtz.Certificates.PositivstellensatzObstruction
import Gtz.Ties.SevenThreeTieLocus
import Gtz.Complex.SharpConstantLedger
import Gtz.Reduction.ExchangeRepair
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Reduction.StrengthenedInductionHypothesis
import Gtz.Complex.PerRankConstantLedger
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.DiagonalRungs
import Gtz.Quantitative.PositivstellensatzRankThree
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
import Gtz.Field.WeightedDesign
import Gtz.Design.ProjectionChart
import Gtz.Field.CorankOne
import Gtz.Complex.SizeAxis
import Gtz.Quantitative.CriticalQuadric
import Gtz.Design.VolumeSamplingAverage
import Gtz.Quantitative.ExpectedCharPolynomial
import Gtz.Reduction.CompactnessReduction
import Gtz.Quantitative.InteriorExclusion
import Gtz.Design.DiamondPrimitive
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.ProjectionChartLegs
import Gtz.Reduction.BranchTransferConstants
import Gtz.Quantitative.ChartStationary
import Gtz.Quantitative.ChartMultiplierSplit
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.ChartTwoBlock
import Gtz.Quantitative.ChartInstances
import Gtz.Quantitative.ChartStrongStationary
import Gtz.Quantitative.ChartCovering
import Gtz.Quantitative.RankTwoRealnessCount
import Gtz.Quantitative.VolumeSelectionFailure
import Gtz.Quantitative.ChartEmptinessCertificate
import Gtz.Quantitative.ComplexRankThreeFloor
import Gtz.Quantitative.ExtremalBasisActivity
import Gtz.Quantitative.CauchyBinetValueFloor
import Gtz.Quantitative.VolumeAverageLaw
import Gtz.Quantitative.ProjectionOnePointMarginal
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Quantitative.SubsetDeterminantBound
import Gtz.Quantitative.OddRankDeterminantUpgrade
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Quantitative.ClassRouteCost
import Gtz.Reduction.ChartAttainment
import Gtz.Reduction.ChartPointFactorisation
import Gtz.Quantitative.ChartDescentFromMinimality
import Gtz.Quantitative.HeavyAtomDichotomy
import Gtz.Quantitative.SignReadingCell
import Gtz.LinAlg.SignForcing
import Gtz.LinAlg.ElliptopeInterval
import Gtz.Design.RhoNormalForm
import Gtz.Design.FrameConservation
import Gtz.Design.DominationGates
import Gtz.Design.SignSelectedAggregate
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.EqualShareSixThree
import Gtz.Quantitative.EqualShareSixThreeMargin
import Gtz.Quantitative.WeightedTripleCriterion
import Gtz.Quantitative.TauOrderStatistics
import Gtz.Quantitative.MinorSumIdentities
import Gtz.Quantitative.GTransformGate
import Gtz.Quantitative.PlanarTightFrameRigidity
import Gtz.Quantitative.CheapAtomGate
import Gtz.Quantitative.WeightedBandCovering
import Gtz.Quantitative.SevenThreeInvolution
import Gtz.Quantitative.SevenThreeConservation
import Gtz.Quantitative.SevenThreeRigidity
import Gtz.Quantitative.SevenThreeCapsGates
import Gtz.Quantitative.SevenThreeMaxVolume
import Gtz.Quantitative.SevenThreeNoGo
import Gtz.Quantitative.SevenThreeCBFloor
import Gtz.Quantitative.SevenThreeMiddleBand

#print axioms Gtz.bhatiaDavis_telescope
#print axioms Gtz.exists_pair_mul_le_neg_one
#print axioms Gtz.posSemidef_atomMatrix
#print axioms Gtz.Dominates.mono
#print axioms Gtz.unitDesign
#print axioms Gtz.gtzWeighted_one_one
#print axioms Gtz.exists_extremal_pair
#print axioms Gtz.tie_two_valued
#print axioms Gtz.vecMulVec_mulVec_eq
#print axioms Gtz.dot_mulVec_comm
#print axioms Gtz.PosDef.transpose_eq
#print axioms Gtz.posSemidef_sub_vecMulVec_iff
#print axioms Gtz.dotProduct_self_pos
#print axioms Gtz.pivot_eq_dot
#print axioms Gtz.trace_identity
#print axioms Gtz.excess_balance
#print axioms Gtz.erase_dominates_iff_pivot_le_one
#print axioms Gtz.pigeonhole
#print axioms Gtz.trace_atomMatrix
#print axioms Gtz.isHermitian_of_transpose_eq
#print axioms Gtz.transpose_eq_of_isHermitian
#print axioms Gtz.vecMulVec_sum_right
#print axioms Gtz.atomMatrix_mul_atomMatrix
#print axioms Gtz.posSemidef_of_sq_eq_smul
#print axioms Gtz.simplex_sum_eq_zero
#print axioms Gtz.simplex_frame_operator
#print axioms Gtz.corner_dot_diag
#print axioms Gtz.corner_dot_off
#print axioms Gtz.corner_heavies_sum_zero
#print axioms Gtz.corner_subsetSum_eq
#print axioms Gtz.corner_balance_forced
#print axioms Gtz.corner_fiber_dominates
#print axioms Gtz.gtz_rank_one
#print axioms Gtz.atomMatrix_smul
#print axioms Gtz.transpose_mul_self_eq_sum_rows
#print axioms Gtz.original_of_weighted
#print axioms Gtz.symmetric_eq_zero_of_coords_eq_zero
#print axioms Gtz.card_orderedPairs
#print axioms Gtz.exists_null_direction
#print axioms Gtz.sum_orderIsoOfFin
#print axioms Gtz.exists_reduced_design
#print axioms Gtz.crystallization
#print axioms Gtz.dotProduct_mulVec_transpose
#print axioms Gtz.posSemidef_one_sub_iff_contraction
#print axioms Gtz.contraction_flip
#print axioms Gtz.posSemidef_one_sub_transpose_comm
#print axioms Gtz.posSemidef_congr_right
#print axioms Gtz.posSemidef_transpose_mul_sub_one_comm
#print axioms Gtz.exists_congruence_to_one
#print axioms Gtz.inner_columnVec
#print axioms Gtz.exists_orthonormal_completion
#print axioms Gtz.vecMulVec_mul
#print axioms Gtz.transpose_mul_atomMatrix_mul
#print axioms Gtz.dot_weighted_atoms_mulVec
#print axioms Gtz.weight_lt_one
#print axioms Gtz.coParseval_posDef
#print axioms Gtz.eq_zero_of_forall_atom_dot_eq_zero
#print axioms Gtz.weighted_naimark_duality
#print axioms Gtz.rank_le_of_design
#print axioms Gtz.gtzWeighted_square
#print axioms Gtz.gtzWeighted_of_dual_rank
#print axioms Gtz.gtz_rank_two_of_four_two
#print axioms Gtz.rank_three_of_the_two_residuals
#print axioms Gtz.gtz_of_canonical_list
#print axioms Gtz.dot_mulVec_two
#print axioms Gtz.posSemidef_two_iff
#print axioms Gtz.posSemidef_two_iff_of_trace_pos
#print axioms Gtz.subsetSum_transpose
#print axioms Gtz.dominating_of_light_atom
#print axioms Gtz.exists_dominating_pair_of_heavy
#print axioms Gtz.gtz_rank_two
#print axioms Gtz.gtz_original_rank_one
#print axioms Gtz.gtz_original_rank_two
#print axioms Gtz.gtz_iff_canonical_list
#print axioms Gtz.rank_three_iff_the_two_residuals
#print axioms Gtz.gtz_original_of_canonical_list
#print axioms Gtz.psd_on_complement_transfer
#print axioms Gtz.cap_criterion
#print axioms Gtz.cap_criterion_trace
#print axioms Gtz.RatDesign.subsetSum_apply
#print axioms Gtz.RatDesign.leverage_cast
#print axioms Gtz.RatDesign.dominates_iff_cast
#print axioms Gtz.posDef_congr_right
#print axioms Gtz.certificate_dominates
#print axioms Gtz.certificate_dominates_of_excess
#print axioms Gtz.map_mul_cast
#print axioms Gtz.det_cast
#print axioms Gtz.RatDesign.gram_cast
#print axioms Gtz.ratInv_cast
#print axioms Gtz.RatDesign.pivot_cast
#print axioms Gtz.ratCertificate_dominates
#print axioms Gtz.ratGram_det_ne_zero
#print axioms Gtz.ratCertificate_dominates_of_excess

-- the certificate's reach: which half of an LDL certificate survives perturbation
#print axioms Gtz.dotProduct_congruence
#print axioms Gtz.diagonal_quadForm_floor
#print axioms Gtz.posDef_of_congruence_perturbed
#print axioms Gtz.abs_congruence_quadForm_le
#print axioms Gtz.posDef_of_congruence_entryBound
#print axioms Gtz.subsetSum_sub_one_transpose
#print axioms Gtz.gate_posDef_of_nearby_design
#print axioms Gtz.certificate_ball_dominates

-- an exact rational (6,3) certificate, end to end
#print axioms Gtz.WeightedDesign.ext
#print axioms Gtz.splitTetraRatDesign
#print axioms Gtz.splitTetraRatBase_card
#print axioms Gtz.splitTetraRatBase_compl
#print axioms Gtz.splitTetraRat_gram
#print axioms Gtz.splitTetraRat_gramInv
#print axioms Gtz.splitTetraRat_congruence
#print axioms Gtz.splitTetraRat_pivot_eq_one
#print axioms Gtz.splitTetraRat_excess_eq_zero
#print axioms Gtz.splitTetraRatDesign_certified_dominates
#print axioms Gtz.splitTetraRatDesign_certified_dominates_pointwise


-- the rank-4 canonical window: size monotonicity, spike padding,
-- and the chain that makes (M(s), s) the single object per rank
#print axioms Gtz.not_dominates_of_repeated_atom_general
#print axioms Gtz.sum_eq_add_diff_of_agree_off
#print axioms Gtz.replicatedAtoms
#print axioms Gtz.replicatedWeights
#print axioms Gtz.replicatedDesign
#print axioms Gtz.replicatedAtoms_castSucc
#print axioms Gtz.replicatedAtoms_last
#print axioms Gtz.replicatedDesign_atom_castSucc
#print axioms Gtz.replicatedDesign_atom_last
#print axioms Gtz.replicationMerge
#print axioms Gtz.replicationMerge_castSucc
#print axioms Gtz.replicationMerge_last
#print axioms Gtz.atom_replicationMerge
#print axioms Gtz.gtzWeighted_of_succ
#print axioms Gtz.gtzWeighted_of_add
#print axioms Gtz.gtzWeighted_of_le
#print axioms Gtz.gtzWeightedAll_of_top
#print axioms Gtz.gtz_iff_top_of_each_rank
#print axioms Gtz.gtzWeighted_window_of_top
#print axioms Gtz.rank_four_window_eq
#print axioms Gtz.gtzWeighted_window_four_of_eleven
#print axioms Gtz.gtzWeightedAll_four_of_eleven
#print axioms Gtz.gtzWeighted_six_three_of_seven_three
#print axioms Gtz.gtzWeightedAll_three_of_seven_three
#print axioms Gtz.exists_gap_witness
#print axioms Gtz.exists_uniform_gap
#print axioms Gtz.spikeAtoms
#print axioms Gtz.spikeWeights
#print axioms Gtz.spikeAtoms_old_cast
#print axioms Gtz.spikeAtoms_old_last
#print axioms Gtz.spikeAtoms_spike_cast
#print axioms Gtz.spikeAtoms_spike_last
#print axioms Gtz.spikeWeights_old
#print axioms Gtz.spikeWeights_spike
#print axioms Gtz.spikeDesign
#print axioms Gtz.dotProduct_snoc_zero
#print axioms Gtz.dotProduct_lastBasis
#print axioms Gtz.gtzWeighted_of_spike
#print axioms Gtz.gtzWeighted_ten_three_of_eleven_four
#print axioms Gtz.gtzWeightedAll_three_of_eleven_four
#print axioms Gtz.gtzWeighted_six_three_of_eight_four
#print axioms Gtz.gtzWeightedAll_three_of_eight_four
#print axioms Gtz.gtzWeighted_seven_four_of_seven_three
#print axioms Gtz.gtzWeighted_sub_window_four_of_rank_three

#print axioms Gtz.original_of_weighted_single
#print axioms Gtz.gtzWeighted_corank_one
#print axioms Gtz.gtzWeighted_corank_two
#print axioms Gtz.gtz_original_square
#print axioms Gtz.gtz_original_corank_one
#print axioms Gtz.gtz_original_corank_two
#print axioms Gtz.gtz_original_of_le_five
#print axioms Gtz.gtzWeighted_of_le_five
#print axioms Gtz.gtzWeighted_dual_iff
#print axioms Gtz.planarMaster_quadraticForm
#print axioms Gtz.planarMaster_trace
#print axioms Gtz.planarMaster_transpose
#print axioms Gtz.posSemidef_planarMaster_of_pairEntry_nonneg
#print axioms Gtz.sum_sub_normSq_expansion
#print axioms Gtz.sum_sub_normSq_levWeighted
#print axioms Gtz.pinch_quadratic
#print axioms Gtz.blochSquare_dotProduct
#print axioms Gtz.blochSquare_normSq
#print axioms Gtz.pairEntry_bloch
#print axioms Gtz.pairEntry_bloch_nonneg_of_silent
#print axioms Gtz.posSemidef_planarMaster_bloch_of_silent
#print axioms Gtz.pairEntry_bloch_nonneg_of_mixed
#print axioms Gtz.pairEntry_bloch_ge_of_dust
#print axioms Gtz.dust_deficit_bloch
#print axioms Gtz.pairSum_nonneg_of_silent
#print axioms Gtz.blochSquare_sub_normSq_ge
#print axioms Gtz.cross_rebate_bloch
#print axioms Gtz.cexDesign_valid
#print axioms Gtz.cexDesign_capped_essential
#print axioms Gtz.cexBudget_eq_trace
#print axioms Gtz.cexBudget_quadratic
#print axioms Gtz.cexMaxSlack_ge
#print axioms Gtz.cexMaxSlack_le
#print axioms Gtz.cexMaxSlack_pos
#print axioms Gtz.lawConstant_cap_ten
#print axioms Gtz.bForm_law_fails_at_cap_ten
#print axioms Gtz.dotProduct_le_planarNorm_mul
#print axioms Gtz.planarNorm_add_le
#print axioms Gtz.abs_planarNorm_sub_le
#print axioms Gtz.abs_planarDefect_sub_le
#print axioms Gtz.sum_weighted_defect_eq_zero
#print axioms Gtz.zeroAtom_pushoff
#print axioms Gtz.cornerDesign_valid
#print axioms Gtz.cornerNearest_defect_zero
#print axioms Gtz.cornerPushoff_saturates
#print axioms Gtz.pairEntry_eq_level_gap
#print axioms Gtz.dustOnly_completion_forces_saturation
#print axioms Gtz.det_sub_vecMulVec_two
#print axioms Gtz.depth_eq_one_sub_zmass
#print axioms Gtz.unitCircle_line_le_two
#print axioms Gtz.tight_iff_polar
#print axioms Gtz.polarNormal_ne_zero
#print axioms Gtz.tight_partners_le_two
#print axioms Gtz.star_three_impossible
#print axioms Gtz.oldInterfacePair_vacuous
#print axioms Gtz.ballTauCeiling
#print axioms Gtz.interfacePair_nonvacuous_iff
#print axioms Gtz.weighted_defect_leash
#print axioms Gtz.smul_eq_smul_of_independent
#print axioms Gtz.eq_of_two_independent_rays
#print axioms Gtz.parabola_conic_zero_iff
#print axioms Gtz.parabola_poles_are_clones
#print axioms Gtz.offWindow_margin_pos
#print axioms Gtz.acidTest_margin_pos
#print axioms Gtz.planarDet_eq_zero_of_common_orthogonal
#print axioms Gtz.fourCycle_normals_parallel
#print axioms Gtz.dust_never_tight
#print axioms Gtz.dust_pair_never_tight
#print axioms Gtz.budget_le_vertex_bound
#print axioms Gtz.weightSplit_design_invariant
#print axioms Gtz.weightSplit_defect_invariant
#print axioms Gtz.sum_weighted_leverage
#print axioms Gtz.exists_leverage_ge_rank
#print axioms Gtz.gtzWeightedAll_of_heavy
#print axioms Gtz.gtzWeightedAll_of_heavy_bounded
#print axioms Gtz.rank_three_of_heavy_residuals
#print axioms Gtz.gtz_original_of_heavy_window
#print axioms Gtz.gtz_original_rank_three_of_heavy
#print axioms Gtz.allHeavy_rank_gt_one
#print axioms Gtz.coSpreadRelation_eq_coLeverage
#print axioms Gtz.coSpreadRelation_mul_leverages
#print axioms Gtz.coSpreadRelation_pos_of_heavy
#print axioms Gtz.branchProduct_eq_zero
#print axioms Gtz.spreadRelation_eq_zero_of_tight
#print axioms Gtz.thirdConic_of_spread
#print axioms Gtz.atomMatrix_conj
#print axioms Gtz.subsetSum_compress
#print axioms Gtz.compressed_dominates_iff
#print axioms Gtz.posSemidef_compress
#print axioms Gtz.exists_subset_dominates_in_view
#print axioms Gtz.exists_pair_dominates_in_plane
#print axioms Gtz.exists_pair_nonneg_on_plane
#print axioms Gtz.fullExcess_eq_coParseval
#print axioms Gtz.posDef_fullExcess
#print axioms Gtz.descent_identity
#print axioms Gtz.sum_one_sub_weight
#print axioms Gtz.pivot_nonneg
#print axioms Gtz.exists_pivot_le_average
#print axioms Gtz.card_pivot_le_one_ge
#print axioms Gtz.budget_le_max_of_leash
#print axioms Gtz.channelFace_attained
#print axioms Gtz.clusterFace_attained
#print axioms Gtz.exists_value_nonpos_of_positive_covector
#print axioms Gtz.exists_fire_of_positive_covector
#print axioms Gtz.collarFloorRate_ge_third
#print axioms Gtz.collarFloorRate_zero
#print axioms Gtz.collarFloorRate_lt_of_lt
#print axioms Gtz.offWindowGate_identity
#print axioms Gtz.offWindow_cap_fires
#print axioms Gtz.offWindowGate_lt_fifty_at_working_radius
#print axioms Gtz.det_sub_atomMatrix
#print axioms Gtz.det_add_atomMatrix
#print axioms Gtz.det_erase_eq_det_mul_pivot_gap
#print axioms Gtz.erase_dominates_iff_det_nonneg
#print axioms Gtz.cap_fires_iff_det_nonneg
#print axioms Gtz.fquant_term_le
#print axioms Gtz.fquant_dist_mul_gap_le
#print axioms Gtz.posDef_excess_of_kappa
#print axioms Gtz.pivot_eq_leverage_div_of_kappa
#print axioms Gtz.complementary_commute
#print axioms Gtz.kappa_lt_of_insiders_silent
#print axioms Gtz.zmass_floor_of_wall_silent
#print axioms Gtz.conic_normalization
#print axioms Gtz.focal_conic_form
#print axioms Gtz.edge_pairing_eq_slack
#print axioms Gtz.uncovered_atom_forces_pole
#print axioms Gtz.det_pair_excess
#print axioms Gtz.pair_not_posSemidef
#print axioms Gtz.omegaRoot_cube
#print axioms Gtz.omegaRoot_sum
#print axioms Gtz.omega_overlap_product
#print axioms Gtz.sicNorm
#print axioms Gtz.sicOverlap
#print axioms Gtz.sicParseval
#print axioms Gtz.complexGtzWeighted_four_fails
#print axioms Gtz.pole_contradicts_conic
#print axioms Gtz.covered_of_conic
#print axioms Gtz.seam_trivial_scale
#print axioms Gtz.seam_subsumption
#print axioms Gtz.posSemidef_topLeftBlock
#print axioms Gtz.not_posSemidef_of_det_re_neg
#print axioms Gtz.scaledPair_not_posSemidef
#print axioms Gtz.paddedParseval
#print axioms Gtz.oneSpike_kill
#print axioms Gtz.allOld_kill
#print axioms Gtz.complexGtzWeighted_six_three_fails
#print axioms Gtz.det_fin_four_expand
#print axioms Gtz.p3_compatibility_factors
#print axioms Gtz.p3_thirdGap_factors
#print axioms Gtz.p3_stratum_is_family
#print axioms Gtz.collinear_stratum_empty
#print axioms Gtz.focal_conic_antipode
#print axioms Gtz.moment_short_of_conic_pos
#print axioms Gtz.vecMulVec_mul_vecMulVec
#print axioms Gtz.corner_cap_mul
#print axioms Gtz.corner_cap_inv
#print axioms Gtz.corner_normal_form
#print axioms Gtz.corner_covering
#print axioms Gtz.corner_extra_caught
#print axioms Gtz.corner_cap_negative_direction
#print axioms Gtz.corner_cap_mulVec_diff
#print axioms Gtz.corner_cap_psd_on_complement
#print axioms Gtz.corner_gate_cap_iff
#print axioms Gtz.det_pair_excess_planar
#print axioms Gtz.pair_dominates_iff_coherence_le
#print axioms Gtz.pair_silent_iff_coherence_gt
#print axioms Gtz.pair_dominates_iff_conic
#print axioms Gtz.bloch_halfAngle
#print axioms Gtz.pair_dominates_iff_halfAngle
#print axioms Gtz.abs_dotProduct_le
#print axioms Gtz.gram_perturbation
#print axioms Gtz.euler_pairing_global
#print axioms Gtz.stress_mass_pinned
#print axioms Gtz.chord_projection_tight
#print axioms Gtz.splitting_rule
#print axioms Gtz.harmonic_rule
#print axioms Gtz.dot_rotateQuarter_self
#print axioms Gtz.rotational_rule
#print axioms Gtz.zeroAtom_pushoff_clean
#print axioms Gtz.chordFn_vanishes
#print axioms Gtz.chordFn_at_vertex
#print axioms Gtz.inscribed_triangle_vertex
#print axioms Gtz.affine_vanishes_of_three
#print axioms Gtz.chord_silence_envelope
#print axioms Gtz.planarDefect_scaled
#print axioms Gtz.conic_curve_pos
#print axioms Gtz.equality_manifold_complete
#print axioms Gtz.coercive_isUnit_det
#print axioms Gtz.resolvent_difference
#print axioms Gtz.inverse_contraction_of_coercive
#print axioms Gtz.noise_mulVec_sq_le
#print axioms Gtz.perturbed_expansion
#print axioms Gtz.resolvent_perturbation_bound
#print axioms Gtz.sylvesterMap_eq_signed_blocks
#print axioms Gtz.blocks_decompose
#print axioms Gtz.sylvesterMap_range_block
#print axioms Gtz.sylvesterMap_corange_block
#print axioms Gtz.sylvesterMap_upper_mixed
#print axioms Gtz.sylvesterMap_lower_mixed
#print axioms Gtz.sylvesterMap_sq
#print axioms Gtz.sylvesterMap_tripotent
#print axioms Gtz.sylvesterMap_eq_zero_iff
#print axioms Gtz.sylvesterMap_mem_range_iff
#print axioms Gtz.sylvesterMap_sq_idempotent
#print axioms Gtz.designTransfer_mul_gram
#print axioms Gtz.designTransfer_idempotent
#print axioms Gtz.exists_leverage_le_rank
#print axioms Gtz.designTransfer_trace
#print axioms Gtz.basis_expansion
#print axioms Gtz.eq_of_unit_dot_eq_one
#print axioms Gtz.affine_double_zero_unique
#print axioms Gtz.leaf_tangency
#print axioms Gtz.det_pair_matrix_eq_neg_pairGram
#print axioms Gtz.cap_det_dictionary
#print axioms Gtz.cap_tie_iff_zmass
#print axioms Gtz.boundary_pivot_eq_one
#print axioms Gtz.atom_form_eq_sq
#print axioms Gtz.atom_form_le_leverage
#print axioms Gtz.parseval_erase
#print axioms Gtz.whitened_parseval
#print axioms Gtz.margin_transfer
#print axioms Gtz.margin_transfer_priced
#print axioms Gtz.aggregate_pushoff
#print axioms Gtz.aggregate_pushoff_pigeonhole
#print axioms Gtz.corner_cap_mulVec
#print axioms Gtz.corner_cap_transpose
#print axioms Gtz.corner_cap_form_sq
#print axioms Gtz.corner_cap_expansion
#print axioms Gtz.corner_cap_form_le
#print axioms Gtz.corner_resolvent_perturbation
#print axioms Gtz.correctedInterfacePair_nonempty
#print axioms Gtz.correctedPair_passes_gate
#print axioms Gtz.correctedFormula_rounds_down
#print axioms Gtz.corrected_c2_assembly
#print axioms Gtz.tight_cleared_eq
#print axioms Gtz.leaf_cleared_eq_criticality
#print axioms Gtz.leverage_cleared
#print axioms Gtz.beta_cleared
#print axioms Gtz.pair_normalizer_cleared
#print axioms Gtz.tight_half_angle_biquadratic
#print axioms Gtz.moment_row_annihilated
#print axioms Gtz.biquadratic_leading_constant
#print axioms Gtz.tight_partners_vieta_factor
#print axioms Gtz.qrt_step_deterministic
#print axioms Gtz.walk_continuation_unique
#print axioms Gtz.det_two_entrywise_stability
#print axioms Gtz.wedge_ceiling
#print axioms Gtz.classical_face_closed_form
#print axioms Gtz.quotient_constant_quadratic_at_two
#print axioms Gtz.anchor_is_design
#print axioms Gtz.anchor_conic
#print axioms Gtz.anchor_edges_tight
#print axioms Gtz.anchor_stress_mass
#print axioms Gtz.anchor_splitting
#print axioms Gtz.anchor_harmonic
#print axioms Gtz.bernstein_eval_nonneg
#print axioms Gtz.bernstein_sum_eval
#print axioms Gtz.bernstein_coeff_floor
#print axioms Gtz.bernstein_coeff_ceiling
#print axioms Gtz.bernstein_coeff_pos
#print axioms Gtz.bernstein_coeff_floor_two
#print axioms Gtz.bernstein_coeff_ceiling_two
#print axioms Gtz.gordan_alternative
#print axioms Gtz.gordan_alternative_dotProduct
#print axioms Gtz.det_atomMatrix_eq_zero
#print axioms Gtz.tied_erase_det_eq_zero
#print axioms Gtz.tied_subset_erase_boundary
#print axioms Gtz.covering_margin_pos
#print axioms Gtz.covering_margin_le
#print axioms Gtz.uncovered_multiplier_bound
#print axioms Gtz.downdate_form_floor
#print axioms Gtz.seam_floor
#print axioms Gtz.erased_form_reading
#print axioms Gtz.pivot_prices_overlap
#print axioms Gtz.erased_floor_of_pivot_gap
#print axioms Gtz.cyclic_stress_telescope
#print axioms Gtz.cyclic_stress_closure
#print axioms Gtz.cyclic_stress_vanishes_of_open
#print axioms Gtz.law_implies_floor
#print axioms Gtz.law_confines_zero_set
#print axioms Gtz.two_piece_law_assembly
#print axioms Gtz.tube_law_from_rate_curvature
#print axioms Gtz.linear_model_tube_expansion
#print axioms Gtz.whitening_form_lower
#print axioms Gtz.whitening_form_upper
#print axioms Gtz.whitening_gram_exact
#print axioms Gtz.closure_forces_obtuse_pair
#print axioms Gtz.nonneg_of_cell_cover
#print axioms Gtz.nonneg_of_symmetry_transfer
#print axioms Gtz.nonneg_of_fundamental_domain
#print axioms Gtz.nonneg_on_window_of_symmetric_cells
#print axioms Gtz.congruence_psd_transfer
#print axioms Gtz.deflated_singular_floor
#print axioms Gtz.deflated_floor_kills_kernel
#print axioms Gtz.leverageOf_eq_dotProduct
#print axioms Gtz.single_atom_dominated
#print axioms Gtz.weighted_leverage_le_one
#print axioms Gtz.leverage_le_of_weight_floor
#print axioms Gtz.p4_geometric_certificate_variety_empty
#print axioms Gtz.leaf_tangency_corner_certificate
#print axioms Gtz.c5_p5stress_geometric_certificate_variety_empty
#print axioms Gtz.planar_gap_pos_of_ne
#print axioms Gtz.clone_guard_of_ne
#print axioms Gtz.pole_guard_of_gate
#print axioms Gtz.no_tight_path_four_double_tangency
#print axioms Gtz.no_tight_path_three_leaf_tangency_off_pole
#print axioms Gtz.no_tight_cycle_five_with_path_stress
#print axioms Gtz.planar_eq_of_components
#print axioms Gtz.no_tight_path_four_double_tangency_of_directions
#print axioms Gtz.no_tight_path_three_leaf_tangency_off_pole_of_directions
#print axioms Gtz.no_tight_cycle_five_with_path_stress_of_directions
#print axioms Gtz.coisometryPushforward
#print axioms Gtz.coisometryPushforward_weight
#print axioms Gtz.coisometryPushforward_atom
#print axioms Gtz.exists_deflation_coisometry
#print axioms Gtz.exists_pivot_deflation
#print axioms Gtz.atomMatrix_mulVec_eq_dot_smul
#print axioms Gtz.decompose_along_deflation
#print axioms Gtz.dotProduct_split_along_deflation
#print axioms Gtz.quadratic_nonneg_of_discriminant
#print axioms Gtz.dominates_insert_of_projection_certificates
#print axioms Gtz.LiftingLemma
#print axioms Gtz.gtzWeighted_succ_of_liftingLemma
#print axioms Gtz.gtzWeighted_dim_zero
#print axioms Gtz.gtzWeightedAll_of_liftingLemma
#print axioms Gtz.gtz_original_all_of_liftingLemma
#print axioms Gtz.bordered_form_eq
#print axioms Gtz.subsetSum_form_eq_sum_sq
#print axioms Gtz.sum_sq_ge_of_dominates
#print axioms Gtz.discriminant_le_of_quadratic_nonneg
#print axioms Gtz.liftingLemma_of_gtzWeighted
#print axioms Gtz.liftingLemma_iff_gtzWeighted_succ
#print axioms Gtz.gtzWeighted_six_three_of_liftingLemma_two
#print axioms Gtz.liftingLemma_zero
#print axioms Gtz.liftingLemma_one
#print axioms Gtz.liftingLemma_two_iff_the_two_residuals
#print axioms Gtz.pivot_form_le_leverage_div_margin
#print axioms Gtz.pivot_form_le_leverage_of_dominated
#print axioms Gtz.liftingLemma_all_iff_gtzWeightedAll
#print axioms Gtz.liftingLemma_all_of_canonical_windows
#print axioms Gtz.subsetPairingMap
#print axioms Gtz.exists_common_annihilator
#print axioms Gtz.notMem_of_dominates_of_atom_eq_zero
#print axioms Gtz.exists_good_in_projection
#print axioms Gtz.exists_good_in_projection_rank_three
#print axioms Gtz.exists_all_certificates_but_discriminant
#print axioms Gtz.exists_all_certificates_but_discriminant_rank_three
#print axioms Gtz.triangle_closure_biquadratic
#print axioms Gtz.IsTie
#print axioms Gtz.ZeroSetConfinement
#print axioms Gtz.ClassificationLeEleven
#print axioms Gtz.TieDichotomy
#print axioms Gtz.ResidueConfinement
#print axioms Gtz.zeroSetConfinement_of_classification_and_residue
#print axioms Gtz.dichotomy_collapses_of_no_residue
#print axioms Gtz.deepCycle_forces_closure
#print axioms Gtz.no_deepCycle_off_torsionLocus
#print axioms Gtz.zeroSetConfinement_of_funnelingLaw
#print axioms Gtz.p3_closure_numerator_factors
#print axioms Gtz.focal_conic_p3_closes
#print axioms Gtz.no_chordless_tight_four_cycle
#print axioms Gtz.collaredSet
#print axioms Gtz.design_mem_collaredSet
#print axioms Gtz.weighted_leverage_le_one_of_parseval
#print axioms Gtz.leverage_le_inv_floor_of_parseval
#print axioms Gtz.isClosed_collaredSet
#print axioms Gtz.isCompact_collaredSet
#print axioms Gtz.twoByTwoForm_nonneg_iff_trace_det_nonneg
#print axioms Gtz.rank3Discriminant_iff_trace_det_nonneg
#print axioms Gtz.discriminantDet_eq_resolventTie
#print axioms Gtz.rank3Discriminant_iff_trace_and_tie

-- the rank-3 discriminant system: domination of a triple as trace + tie polynomials,
-- and the proved dominant-pairing stratum
#print axioms Gtz.cornerCompleteSquare
#print axioms Gtz.quadThree_nonneg_iff_schur_nonneg
#print axioms Gtz.posSemidef_iff_quadForm_nonneg
#print axioms Gtz.quadForm_three_eq
#print axioms Gtz.tripleMatrix_mul_transpose
#print axioms Gtz.tripleMatrix_transpose_mul_apply
#print axioms Gtz.tripleGap_transpose
#print axioms Gtz.atomPairing_comm
#print axioms Gtz.atomPairing_self
#print axioms Gtz.dominates_triple_iff_discriminantSystem
#print axioms Gtz.gtzWeightedHeavy_three_iff_discriminantCovering
#print axioms Gtz.discriminantSystem_pivot_independent
#print axioms Gtz.discriminantTie_swap
#print axioms Gtz.rank_three_of_discriminantCovering
#print axioms Gtz.discriminantCovering_iff_rank_three
#print axioms Gtz.gtz_original_rank_three_of_discriminantCovering
#print axioms Gtz.discriminantMinorSum_eq
#print axioms Gtz.allHeavy_heavyExcess_pos
#print axioms Gtz.tetraDesign_leverage
#print axioms Gtz.tetraDesign_heavyExcess
#print axioms Gtz.tetraDesign_atomPairing_zeroOne
#print axioms Gtz.tetraDesign_atomPairing_zeroTwo
#print axioms Gtz.tetraDesign_atomPairing_oneTwo
#print axioms Gtz.tetraDesign_discriminantTrace
#print axioms Gtz.tetraDesign_discriminantTie
#print axioms Gtz.tetraDesign_dominates_of_discriminantSystem
#print axioms Gtz.tetraDesign_allHeavy
#print axioms Gtz.dominates_of_dominantPairings
#print axioms Gtz.dominates_of_orthogonalTriple
#print axioms Gtz.discriminantCovering_of_dominantPairingTriple
#print axioms Gtz.tetraDesign_pairing_boundary
#print axioms Gtz.FrameBridge.biquad_p3_closes
#print axioms Gtz.FrameBridge.frameForm_p3_closure
#print axioms Gtz.FrameBridge.no_carriesOpenTriple
#print axioms Gtz.FrameBridge.tie_le_eleven_of_frameForm
#print axioms Gtz.FrameBridge.tie_le_eleven_of_frameForm_explicit
#print axioms Gtz.covector_forces_firing
#print axioms Gtz.firing_margin_ge_of_covector_and_floor
#print axioms Gtz.minWeight_ge_inv_leverageCap
#print axioms Gtz.rate_floor_of_weight_floor
#print axioms Gtz.rate_floor_of_weight_floor_rpow
#print axioms Gtz.collar_rate_positive
#print axioms Gtz.collared_two_piece_law
#print axioms Gtz.offTubeGap_pos
#print axioms Gtz.rate_floor_antitone_in_leverage
#print axioms Gtz.collar_erosion_ratio_exponent_one
#print axioms Gtz.collar_erosion_strict
#print axioms Gtz.collared_law_constant_pos
#print axioms Gtz.collared_law_constant_at_sample
#print axioms Gtz.dominationGap_form
#print axioms Gtz.tightDirection_rayleigh_identity
#print axioms Gtz.tightDirection_minimizes_gap
#print axioms Gtz.tightDirection_isNullVector
#print axioms Gtz.tightDirection_isEigenvector
#print axioms Gtz.parseval_weighted_sum_sq
#print axioms Gtz.exists_charge_ge
#print axioms Gtz.exists_nonneg_margin_of_weighted_average
#print axioms Gtz.tightDirection_subset_eq_weighted
#print axioms Gtz.atomMatrix_frobenius_eq_sq
#print axioms Gtz.atomMatrix_trace_pairing
#print axioms Gtz.tightDirection_complementarySlackness
#print axioms Gtz.tightDirection_gapAnnihilatesMultiplier
#print axioms Gtz.gapAnnihilates_multiplierCandidate
#print axioms Gtz.isTie_yields_tightDirection
#print axioms Gtz.isTie_yields_unitEigenvector
-- GAP-S H1b, restated past the cap-10 refutation: one Positivstellensatz identity
-- with constant multipliers, true below 4 + 2*sqrt 2 and FALSE above it
#print axioms Gtz.capChannelDefect
#print axioms Gtz.capSilenceSum
#print axioms Gtz.capSilenceProduct
#print axioms Gtz.capChannelNumerator
#print axioms Gtz.capChannelNumerator_eq_div
#print axioms Gtz.capArgmaxGap
#print axioms Gtz.capArgmaxGap_certificate
#print axioms Gtz.capArgmax_corner_dominates
#print axioms Gtz.capArgmax_threshold_iff
#print axioms Gtz.capArgmax_corner_dominates_below_threshold
#print axioms Gtz.capArgmaxGap_at_lightAtom
#print axioms Gtz.capArgmaxGap_at_capAtom
#print axioms Gtz.capArgmax_face_refutation
#print axioms Gtz.capRefuterAbscissa
#print axioms Gtz.capRefuterRadius
#print axioms Gtz.capRefuter_onFace
#print axioms Gtz.capRefuter_silenceSum
#print axioms Gtz.capRefuter_defect
#print axioms Gtz.capRefuter_radiusLower
#print axioms Gtz.capRefuter_radiusUpper
#print axioms Gtz.capRefuter_heightSq
#print axioms Gtz.capRefuter_admissible
#print axioms Gtz.capArgmax_fails_above_threshold
#print axioms Gtz.capThirteen_probe_silenceSum
#print axioms Gtz.capThirteen_probe_silenceProduct
#print axioms Gtz.capThirteen_probe_defect
#print axioms Gtz.capThirteen_beats_corner
#print axioms Gtz.capThirteen_corner_exceeded
#print axioms Gtz.twoAtCapSquares
#print axioms Gtz.twoAtCapLeverages
#print axioms Gtz.twoAtCapEntry
#print axioms Gtz.twoAtCapDistanceSq
#print axioms Gtz.twoAtCap_design_valid
#print axioms Gtz.capSilence_sum_and_product
#print axioms Gtz.twoAtCap_capPairContribution
#print axioms Gtz.twoAtCap_lightContribution
#print axioms Gtz.capChannelNumerator_eq_pairEntrySum

#print axioms Gtz.capBoundaryConstant_at_five
#print axioms Gtz.capBoundaryConstant_derivNumerator_nonneg
#print axioms Gtz.capBoundaryConstant_hasDerivAt
#print axioms Gtz.capBoundaryConstant_monotone
#print axioms Gtz.capBoundaryConstant_strictMono
#print axioms Gtz.capBoundaryConstant_at_two
#print axioms Gtz.capBoundaryConstant_at_three
#print axioms Gtz.capBoundaryConstant_at_four
#print axioms Gtz.capBoundaryConstant_strict_chain
#print axioms Gtz.pair_budget_decompose
#print axioms Gtz.tight_pair_second_order_nonpos
#print axioms Gtz.pair_budget_le_firstOrder
#print axioms Gtz.envelope_forces_slack_pos
#print axioms Gtz.complex_sic_slack_neg
#print axioms Gtz.complex_sic_slack_window
#print axioms Gtz.complex_witness_violates_envelope
#print axioms Gtz.transverse_dist_le_of_coercive
#print axioms Gtz.quotient_floor_uniform
#print axioms Gtz.tetra_domination_form_sos
#print axioms Gtz.tetra_domination_form_nonneg
#print axioms Gtz.tetra_tie_direction_vanishes
#print axioms Gtz.tetraGapMatrix_quadForm
#print axioms Gtz.tetraGapMatrix_quadForm_nonneg
#print axioms Gtz.tetraGapMatrix_quadForm_at_null
#print axioms Gtz.tetraGapMatrix_quadForm_null_iff
#print axioms Gtz.rayleigh_bddBelow
#print axioms Gtz.lambdaMinCLM_sub_le
#print axioms Gtz.abs_lambdaMinCLM_sub_le
#print axioms Gtz.lipschitzWith_lambdaMinCLM
#print axioms Gtz.continuous_lambdaMinCLM
#print axioms Gtz.continuous_toEuclideanCLM
#print axioms Gtz.continuous_lambdaMinMat
#print axioms Gtz.rayleigh_toEuclideanCLM_eq
#print axioms Gtz.euclid_norm_sq_eq_dotProduct
#print axioms Gtz.one_le_lambdaMinMat_iff_forall
#print axioms Gtz.one_le_lambdaMinMat_iff_posSemidef
#print axioms Gtz.isHermitian_subsetSumRaw
#print axioms Gtz.dominates_iff_one_le_lambdaMinMat
#print axioms Gtz.continuous_subsetSumRaw
#print axioms Gtz.continuous_dominationMargin
#print axioms Gtz.continuousOn_dominationMargin
#print axioms Gtz.offTubeGap_of_margin_pos
#print axioms Gtz.no_separating_slope_of_stressCertificate
#print axioms Gtz.no_separatingSlope_exists_of_stressCertificate
#print axioms Gtz.tetraDesign
#print axioms Gtz.tetra_no_separating_slope
#print axioms Gtz.exists_isMinOn_rayleighQuotient
#print axioms Gtz.exists_lambdaMinMat_eq_rayleigh
#print axioms Gtz.one_lt_lambdaMinMat_iff_posDef
#print axioms Gtz.strictDominates_iff_one_lt_lambdaMinMat
#print axioms Gtz.margin_pos_iff_exists_strictDominates
#print axioms Gtz.witnessDesign
#print axioms Gtz.witnessDesign_dominates
#print axioms Gtz.witnessSlope_form
#print axioms Gtz.witnessSlope_weightPairing
#print axioms Gtz.witnessDesign_noStressCertificate
#print axioms Gtz.noStressCertificate_of_duplicate_atoms
#print axioms Gtz.splitTetraDesign
#print axioms Gtz.splitTetra_gapForm_zero_of_unusedDir
#print axioms Gtz.splitTetraDesign_dominates
#print axioms Gtz.splitTetraDesign_no_strictDominator
#print axioms Gtz.splitTetraDesign_isTie
#print axioms Gtz.splitTetraDesign_noStressCertificate
#print axioms Gtz.exists_isTie_and_noStressCertificate
#print axioms Gtz.splitTetraRatDesign_toReal_eq
#print axioms Gtz.splitTetraRatDesign_isTie
#print axioms Gtz.exists_isTie_with_ratCertificate
#print axioms Gtz.balanceCoefficient_nonneg
#print axioms Gtz.balanceSubset_dominates
#print axioms Gtz.balanceSubset_tight
#print axioms Gtz.splitTetraDesign_localBalance
#print axioms Gtz.tetraDesign_dominates
#print axioms Gtz.tetraDesign_no_strictDominator
#print axioms Gtz.tetraDesign_isTie
#print axioms Gtz.tetraDesign_stressCertificate
#print axioms Gtz.exists_isTie_and_stressCertificate
#print axioms Gtz.exists_ne_zero_dotProduct_pair_eq_zero
#print axioms Gtz.not_dominates_of_repeated_atom
#print axioms Gtz.not_strictDominator_of_repeated_atom
#print axioms Gtz.sharpDesign
#print axioms Gtz.sharpDesign_dependency
#print axioms Gtz.sharpDesign_dominates
#print axioms Gtz.sharpDesign_no_strictDominator
#print axioms Gtz.sharpDesign_isTie
#print axioms Gtz.leverageOf_orthogonal_image
#print axioms Gtz.sharpDesign_not_rotated_tetrahedron
#print axioms Gtz.exists_isTie_leverages_unequal
#print axioms Gtz.posDef_sub_vecMulVec_iff
#print axioms Gtz.erase_strictDominates_iff_pivot_lt_one
#print axioms Gtz.corank_one_dominating_erasure
#print axioms Gtz.forall_dominates_erase_of_isTie
#print axioms Gtz.isTie_iff_forall_pivot_eq_one
#print axioms Gtz.not_isTie_of_pivot_lt_one
#print axioms Gtz.finrank_ker_atomCombination
#print axioms Gtz.dependency_cross
#print axioms Gtz.row_cross_identity
#print axioms Gtz.leverage_identity_of_forall_pivot_eq_one
#print axioms Gtz.forall_pivot_eq_one_of_leverage_identity
#print axioms Gtz.isTie_iff_leverage_identity
#print axioms Gtz.tetraDesign_leverage_identity
#print axioms Gtz.sharpDesign_leverage_identity
#print axioms Gtz.leverage_identity_forces_corank_one
#print axioms Gtz.no_leverage_identity_at_six_three
#print axioms Gtz.no_leverage_identity_at_corank_two
#print axioms Gtz.exists_isTie_leverage_identity_fails
#print axioms Gtz.unevenPairDesign_leverage_identity_fails
#print axioms Gtz.unevenPairDesign_not_isTie
#print axioms Gtz.unevenPairDesign_strictDominator
#print axioms Gtz.exists_leverage_identity_not_isTie_rank_zero
#print axioms Gtz.reflection_mul_self
#print axioms Gtz.weight_mul_div_sqrt_pair
#print axioms Gtz.weight_lt_one_of_simplex
#print axioms Gtz.tieDefect_sq
#print axioms Gtz.tieDefect_pos
#print axioms Gtz.sum_tieDefect_sq
#print axioms Gtz.tieDefect_head_lt_one
#print axioms Gtz.tieReflector_head
#print axioms Gtz.tieReflector_normSq
#print axioms Gtz.tieHouseholder_apply
#print axioms Gtz.tieHouseholder_symm
#print axioms Gtz.tieHouseholder_mul_self
#print axioms Gtz.tieHouseholder_head
#print axioms Gtz.tieHouseholder_column_pairing
#print axioms Gtz.tieHouseholder_tail_pairing
#print axioms Gtz.simplexTieDesign_weight
#print axioms Gtz.weight_mul_leverage_simplexTieAtom
#print axioms Gtz.simplexTieDesign_leverage_identity
#print axioms Gtz.simplexTieDesign_isTie
#print axioms Gtz.exists_isTie_of_weights
#print axioms Gtz.leverage_of_isTie
#print axioms Gtz.corank_one_tie_stratum
#print axioms Gtz.exists_isTie_uniform

-- realness: the maximal real equiangular design (icosahedron) and the Bargmann sign
#print axioms Gtz.IsEquiangularAt
#print axioms Gtz.DoesSpanSameLine
#print axioms Gtz.ComplexIsEquiangularAt
#print axioms Gtz.DoesComplexSpanSameLine
#print axioms Gtz.tetraAtom_isEquiangular
#print axioms Gtz.tetraAtom_distinct_lines
#print axioms Gtz.splitTetraAtom_not_equiangular
#print axioms Gtz.splitTetraAtom_sameLine_iff
#print axioms Gtz.splitTetraAtom_lineCount_four
#print axioms Gtz.sharpAtom_not_equiangular
#print axioms Gtz.icosaRadius
#print axioms Gtz.icosaRadius_sq
#print axioms Gtz.icosaRadius_pos
#print axioms Gtz.icosaRadius_lower
#print axioms Gtz.icosaRadius_upper
#print axioms Gtz.icosaShort
#print axioms Gtz.icosaLong
#print axioms Gtz.icosaShort_sq
#print axioms Gtz.icosaLong_sq
#print axioms Gtz.icosaShort_mul_icosaLong
#print axioms Gtz.icosaAtom
#print axioms Gtz.icosaAtom_leverage
#print axioms Gtz.icosaAtom_dot_sq_of_ne
#print axioms Gtz.icosaAtom_isEquiangular
#print axioms Gtz.icosaAtom_distinct_lines
#print axioms Gtz.icosaDesign
#print axioms Gtz.icosaDesign_excess_form
#print axioms Gtz.icosaDesign_dominates
#print axioms Gtz.icosaDesign_strictly_dominates
#print axioms Gtz.icosaDesign_rayleigh_floor
#print axioms Gtz.icosaDesign_rayleigh_attained
#print axioms Gtz.icosa_margin_window
#print axioms Gtz.exists_maximal_equiangular_design_strictly_dominating
#print axioms Gtz.paddedAtom_spikes_share_a_line
#print axioms Gtz.paddedAtom_spike_cross
#print axioms Gtz.paddedAtom_spike_four_leverage
#print axioms Gtz.paddedAtom_spike_five_leverage
#print axioms Gtz.paddedAtom_flat_spike_orthogonal
#print axioms Gtz.paddedAtom_spike_flat_orthogonal
#print axioms Gtz.paddedAtom_not_equiangular
#print axioms Gtz.complexify
#print axioms Gtz.starDot_complexify
#print axioms Gtz.triangleBargmann
#print axioms Gtz.HasRealTriangleBargmann
#print axioms Gtz.realTriangle_bargmann_extremal
#print axioms Gtz.realFamily_hasRealTriangleBargmann
#print axioms Gtz.omegaRoot_re
#print axioms Gtz.omegaRoot_im
#print axioms Gtz.sicCube_value
#print axioms Gtz.sicCube_re
#print axioms Gtz.sicCube_im
#print axioms Gtz.sicBargmann_value
#print axioms Gtz.sicBargmann_re
#print axioms Gtz.sicBargmann_im
#print axioms Gtz.sicAtom_not_hasRealTriangleBargmann
#print axioms Gtz.starDot_extendFlat
#print axioms Gtz.starDot_scaledSic
#print axioms Gtz.paddedBargmann_value
#print axioms Gtz.paddedBargmann_im
#print axioms Gtz.paddedAtom_not_hasRealTriangleBargmann
#print axioms Gtz.realness_gate_separates

-- selection is global: no continuous and no label-free dominating-subset rule exists
#print axioms Gtz.not_dominates_of_negativeDirection
#print axioms Gtz.not_dominates_triple_of_negativeDirection
#print axioms Gtz.finset_card_three_cases
#print axioms Gtz.liftingCertificates_of_dominates_atPivot
#print axioms Gtz.heavyPivotDesign
#print axioms Gtz.heavyPivotDesign_dominates_lastThree
#print axioms Gtz.heavyPivotDesign_dominates_iff
#print axioms Gtz.heavyPivotDesign_leverage_one
#print axioms Gtz.heavyPivotDesign_leverage_lt_one
#print axioms Gtz.rotatedHeavyPivotDesign_dominates_firstThree
#print axioms Gtz.rotatedHeavyPivotDesign_not_dominates_lastThree
#print axioms Gtz.no_universal_dominating_subset
#print axioms Gtz.no_universal_goodPair
#print axioms Gtz.exists_designs_with_disjoint_dominationSets
#print axioms Gtz.heaviest_atom_can_lie_outside_every_dominatingSubset
#print axioms Gtz.relabelDesign
#print axioms Gtz.subsetSum_relabelDesign
#print axioms Gtz.dominates_relabelDesign_iff
#print axioms Gtz.doubledTetrahedronDesign
#print axioms Gtz.doubledTetrahedron_dominates_zeroTwoThree
#print axioms Gtz.doubledTetrahedron_zeroOnePair_not_dominates
#print axioms Gtz.doubledTetrahedron_threeFourPair_not_dominates
#print axioms Gtz.doubledTetrahedron_invariantSubset_not_dominates
#print axioms Gtz.doubleTransposition_ne_one
#print axioms Gtz.doubledTetrahedron_atom_invariant
#print axioms Gtz.doubledTetrahedron_weight_invariant
#print axioms Gtz.exists_symmetry_with_no_fixed_dominatingSubset

-- moment directions: the frame form without a subdifferential (R-MECH-3 routed around)
#print axioms Gtz.IsMomentDirection
#print axioms Gtz.IsMomentDirection.smul
#print axioms Gtz.reweighted_isParseval
#print axioms Gtz.congruentReweightedDesign
#print axioms Gtz.subsetSum_congruentReweightedDesign
#print axioms Gtz.transpose_subsetSum_self
#print axioms Gtz.exists_shiftedDominator_of_momentDirection
#print axioms Gtz.exists_strictDominator_of_momentDirection
#print axioms Gtz.deflatedCongruentDesign
#print axioms Gtz.subsetSum_deflatedCongruentDesign
#print axioms Gtz.exists_strictDominator_of_boundaryMomentDirection
#print axioms Gtz.unevenLeveragePair
#print axioms Gtz.exists_design_with_posDefMomentDirection
#print axioms Gtz.totalReweight
#print axioms Gtz.reweightMoment
#print axioms Gtz.designMomentMap
#print axioms Gtz.momentDirection_iff_mem_designMomentRange
#print axioms Gtz.linearFunctional_eq_matrixPairing
#print axioms Gtz.matrixPairing_atomMatrix
#print axioms Gtz.matrixPairing_one
#print axioms Gtz.dotProduct_mulVec_transpose_self
#print axioms Gtz.exists_conicMultiplier_of_identity_notMoment
#print axioms Gtz.exists_symmetricConicMultiplier_of_identity_notMoment
#print axioms Gtz.exists_conicMultiplier_of_noStrictDominator

-- Branch (b) rational congruence route: the seven-three artifacts

-- BranchTwoRational
#print axioms Gtz.dotProduct_congruence_bilinear
#print axioms Gtz.dotProduct_diagonal_single
#print axioms Gtz.dotProduct_diagonal_self
#print axioms Gtz.negativeDirection
#print axioms Gtz.negativeDirection_quadForm
#print axioms Gtz.signatureWitness_of_oneNegativePivot
#print axioms Gtz.det_neg_of_oneNegativePivot
#print axioms Gtz.gramShift_insert
#print axioms Gtz.gramShift_erase
#print axioms Gtz.dominates_of_capWitness
#print axioms Gtz.dominates_of_capCongruence
#print axioms Gtz.ratDominates_of_capCongruence
#print axioms Gtz.ratCapCertificate_exists_dominating
#print axioms Gtz.det_interface_identity
#print axioms Gtz.branchTests_agree
#print axioms Gtz.capWitness_of_dominates
#print axioms Gtz.capCombinations
#print axioms Gtz.capCombinations_card_seven_three
#print axioms Gtz.capCombinations_card_six_three
#print axioms Gtz.gateNormal
#print axioms Gtz.pairGramShift
#print axioms Gtz.gateNormal_selfDot
#print axioms Gtz.cramer_expansion
#print axioms Gtz.pairGramShift_mulVec_gateNormal
#print axioms Gtz.pairGramShift_det
#print axioms Gtz.pairGramShift_firstForm
#print axioms Gtz.pairGramShift_secondForm
#print axioms Gtz.pairGramShift_crossForm
#print axioms Gtz.pairGramShift_crossFormFlipped
#print axioms Gtz.pairGate_signatureWitness
#print axioms Gtz.dominates_of_pairGate
#print axioms Gtz.RatDesign
#print axioms Gtz.ratDominates_of_pairGate
#print axioms Gtz.exists_dominatingTriple_withoutStrictGate
#print axioms Gtz.splitTetraCapGate
#print axioms Gtz.splitTetraCap_gateGram
#print axioms Gtz.splitTetraCap_congruence
#print axioms Gtz.splitTetraCap_capDet
#print axioms Gtz.splitTetraRatDesign_capCertified_dominates
#print axioms Gtz.splitTetraRatDesign_pairGateCertified_dominates

-- BranchTwoMinimal
#print axioms Gtz.isUnit_basisDet_of_oneNegativePivot
#print axioms Gtz.signatureWitness_of_oneNegativePivot_noUnit
#print axioms Gtz.det_neg_of_oneNegativePivot_noUnit
#print axioms Gtz.notMem_of_capDet
#print axioms Gtz.dominates_of_capWitness_noFresh
#print axioms Gtz.dominates_of_capCongruence_minimal
#print axioms Gtz.distinct_of_pairGateScalars
#print axioms Gtz.dominates_of_pairGate_minimal
#print axioms Gtz.ratIsUnit_basisDet_of_oneNegativePivot
#print axioms Gtz.ratDominates_of_capCongruence_minimal
#print axioms Gtz.ratDominates_of_pairGate_minimal

-- BranchTwoCompleteness
#print axioms Gtz.tripleRows
#print axioms Gtz.tripleRows_transpose_mul
#print axioms Gtz.gramShift_posSemidef_of_dominatingTriple
#print axioms Gtz.pairSlack_nonneg_of_dominatingTriple
#print axioms Gtz.pairGramShift_det_nonpos_of_dominatingTriple
#print axioms Gtz.symmetricDet_eq_zero_of_degenerateMinor
#print axioms Gtz.excessDet_eq_gramDet
#print axioms Gtz.shiftedLeverage_nonneg_of_dominatingTriple
#print axioms Gtz.excessDet_eq_zero_of_degenerateGate
#print axioms Gtz.pairSlack_pos_of_strictDominatingTriple
#print axioms Gtz.pairGramShift_det_neg_of_strictDominatingTriple

-- PsdCongruenceConsumer
#print axioms Gtz.dominates_of_psdCongruence
#print axioms Gtz.ratDominates_of_psdCongruence
#print axioms Gtz.ratPsdCertificate_exists_dominating
#print axioms Gtz.degenerateWitnessBasis
#print axioms Gtz.degenerateWitness_gramShift
#print axioms Gtz.degenerateWitness_congruence
#print axioms Gtz.degenerateWitnessBasis_det
#print axioms Gtz.degenerateWitness_isPosSemidef_byCongruence
#print axioms Gtz.splitTetraTriple_psdCongruence
#print axioms Gtz.splitTetraTriple_dominates_byPsdCongruence
#print axioms Gtz.branchTests_agree_isNonvacuous

-- PrincipalMinorsThree
#print axioms Gtz.posSemidef_three_of_principalMinors
#print axioms Gtz.ratDominates_of_principalMinors
#print axioms Gtz.degenerateWitness_byPrincipalMinors

-- Graphic instance + collar exponent (earlier rounds, previously unwired)

-- Gtz.Design.GraphicInstance
#print axioms Gtz.MultigraphOnGround.edgeVector
#print axioms Gtz.groundedPotential
#print axioms Gtz.groundedPotential_castSucc
#print axioms Gtz.groundedPotential_last
#print axioms Gtz.sum_indicator_castSucc_mul
#print axioms Gtz.edgeVector_dotProduct
#print axioms Gtz.laplacianOn
#print axioms Gtz.atomMatrix_smul_form
#print axioms Gtz.laplacianOn_transpose
#print axioms Gtz.laplacianOn_bilinear
#print axioms Gtz.laplacianOn_form
#print axioms Gtz.posSemidef_laplacianOn
#print axioms Gtz.IsEdgeAdjacent
#print axioms Gtz.IsEdgeReachable
#print axioms Gtz.isEdgeAdjacent_symm
#print axioms Gtz.isEdgeReachable_symm
#print axioms Gtz.isEdgeReachable_endpoints
#print axioms Gtz.IsGroundConnected
#print axioms Gtz.IsSpanningTree
#print axioms Gtz.groundedPotential_eq_of_reachable
#print axioms Gtz.posDef_laplacianOn_of_isGroundConnected
#print axioms Gtz.componentIndicator
#print axioms Gtz.componentIndicator_of_reachable
#print axioms Gtz.componentIndicator_of_not_reachable
#print axioms Gtz.isGroundConnected_of_posDef_laplacianOn
#print axioms Gtz.posDef_laplacianOn_iff_isGroundConnected
#print axioms Gtz.GraphDesignData.fullLaplacian
#print axioms Gtz.GraphDesignData.selectedLaplacian
#print axioms Gtz.GraphDesignData.posDef_fullLaplacian
#print axioms Gtz.GraphDesignData.fullLaplacian_transpose
#print axioms Gtz.GraphDesignData.selectedLaplacian_transpose
#print axioms Gtz.GraphDesignData.whitener
#print axioms Gtz.GraphDesignData.whitener_isUnit
#print axioms Gtz.GraphDesignData.whitener_spec
#print axioms Gtz.GraphDesignData.graphicAtom
#print axioms Gtz.GraphDesignData.atomMatrix_graphicAtom
#print axioms Gtz.GraphDesignData.whitener_congr_laplacianOn
#print axioms Gtz.GraphDesignData.toWeightedDesign
#print axioms Gtz.graphicDesign
#print axioms Gtz.graphicDesign_weight
#print axioms Gtz.graphicDesign_subsetSum
#print axioms Gtz.graphicDesign_dominates_iff
#print axioms Gtz.posDef_selectedLaplacian_of_dominates
#print axioms Gtz.isGroundConnected_of_dominates
#print axioms Gtz.isSpanningTree_of_dominates
#print axioms Gtz.not_dominates_of_not_isGroundConnected
#print axioms Gtz.eq_zero_of_orthogonal_to_dominating
#print axioms Gtz.GraphicGtz
#print axioms Gtz.graphicGtz_of_gtzWeighted
#print axioms Gtz.cycleVertex
#print axioms Gtz.cycleGraph
#print axioms Gtz.cycleVertex_val_of_le
#print axioms Gtz.cycleVertex_castSucc
#print axioms Gtz.cycleVertex_top
#print axioms Gtz.cycleVertex_zero
#print axioms Gtz.cycleGraph_edgeHead_cycleVertex
#print axioms Gtz.cycleGraph_reachable_from_zero
#print axioms Gtz.cycleGraph_isGroundConnected
#print axioms Gtz.cycleGraphData
#print axioms Gtz.cycleNode
#print axioms Gtz.cycleNode_top
#print axioms Gtz.cycleDrop_castSucc
#print axioms Gtz.cycleDrop_last
#print axioms Gtz.sum_erase_last_eq
#print axioms Gtz.cycleGap_form
#print axioms Gtz.cycleGraphData_dominates
#print axioms Gtz.cycleGraphData_path_card
#print axioms Gtz.cycleGraphData_not_posDef
#print axioms Gtz.cycleGraphData_isSpanningTree
#print axioms Gtz.laplacianOn_erase
#print axioms Gtz.dominates_of_deleted_dominates
#print axioms Gtz.laplacianOn_form_erase_of_orthogonal
#print axioms Gtz.completeFourGraph
#print axioms Gtz.completeFourStar
#print axioms Gtz.completeFourGraph_isGroundConnected
#print axioms Gtz.completeFourData
#print axioms Gtz.groundedPotential_four_zero
#print axioms Gtz.groundedPotential_four_one
#print axioms Gtz.groundedPotential_four_two
#print axioms Gtz.groundedPotential_four_three
#print axioms Gtz.completeFourGap_form
#print axioms Gtz.completeFourData_dominates_strictly
#print axioms Gtz.completeFourData_dominates
#print axioms Gtz.completeFourStar_card
#print axioms Gtz.completeFourData_isSpanningTree

-- Gtz.Quantitative.CollarExponent
#print axioms Gtz.collarRate_tendsto_zero
#print axioms Gtz.linearLaw_scaleInvariant_at_exponent_one
#print axioms Gtz.linearLaw_collapses_of_exponent_gt_one
#print axioms Gtz.linearLaw_diverges_of_exponent_lt_one
#print axioms Gtz.erosionExponents_incomparable
#print axioms Gtz.tubeRadius_mono_in_rate
#print axioms Gtz.tubeRadius_antitone_in_leverage
#print axioms Gtz.consumedModulus
#print axioms Gtz.margin_le_lipschitz_mul_dist
#print axioms Gtz.consumedModulus_le_lipschitzConstant
#print axioms Gtz.tieLocus
#print axioms Gtz.margin_nonpos_iff_no_gate_strictDominates
#print axioms Gtz.mem_tieLocus_iff
#print axioms Gtz.effectiveLojasiewiczUpperBound_exceeds_ten_pow_ninety
#print axioms Gtz.effectiveLojasiewiczLowerBound_exceeds_ten_pow_fifteen
#print axioms Gtz.effectiveLojasiewiczBounds_worsen_at_rank_six

-- the one-sentence rank-three frontier (all-heavy size monotonicity)
#print axioms Gtz.replicatedDesign_allHeavy
#print axioms Gtz.gtzWeightedHeavy_of_succ
#print axioms Gtz.gtzWeightedHeavy_of_add
#print axioms Gtz.gtzWeightedHeavy_of_le
#print axioms Gtz.rank_three_of_heavy_top
#print axioms Gtz.discriminantCovering_of_le
#print axioms Gtz.rank_three_of_discriminantCovering_seven
#print axioms Gtz.discriminantCovering_seven_iff_rank_three
#print axioms Gtz.gtz_original_rank_three_of_discriminantCovering_seven

-- the rank-four minor system + the named induction-step wall

#print axioms Gtz.gapDiagonal
#print axioms Gtz.gapPairing
#print axioms Gtz.gapPairing_comm
#print axioms Gtz.gapPairing_self
#print axioms Gtz.gapDiagonal_pos_of_heavy
#print axioms Gtz.gapPairMinor
#print axioms Gtz.gapTripleMinor
#print axioms Gtz.gapQuadMinor
#print axioms Gtz.schurCross
#print axioms Gtz.gapDiagonal_eq_heavyExcess
#print axioms Gtz.gapPairing_eq_atomPairing
#print axioms Gtz.gapTripleMinor_eq_discriminantTie
#print axioms Gtz.gapPairMinor_add_eq_discriminantTrace
#print axioms Gtz.quadAtom
#print axioms Gtz.quadAtom_pivot
#print axioms Gtz.quadAtom_first
#print axioms Gtz.quadAtom_second
#print axioms Gtz.quadAtom_third
#print axioms Gtz.quadMatrix
#print axioms Gtz.quadMatrix_mul_transpose
#print axioms Gtz.quadMatrix_transpose_mul_apply
#print axioms Gtz.gramGap_transpose
#print axioms Gtz.quadForm_four_eq
#print axioms Gtz.cornerCompleteSquareFour
#print axioms Gtz.quadFour_nonneg_iff_schur_nonneg
#print axioms Gtz.schurBlockFour
#print axioms Gtz.schurBlockFour_transpose
#print axioms Gtz.schurBlockFour_pairMinor_eq
#print axioms Gtz.schurBlockFour_det
#print axioms Gtz.dominates_quad_iff_pivotMinorSystem
#print axioms Gtz.PivotMinorCoveringFour
#print axioms Gtz.gtzWeightedHeavy_four_iff_pivotMinorCoveringFour
#print axioms Gtz.pivotMinorSystem_pivot_independent
#print axioms Gtz.gtzWeightedAll_of_heavyTop
#print axioms Gtz.rank_four_of_heavy_top
#print axioms Gtz.rank_five_of_heavy_top
#print axioms Gtz.pivotMinorCoveringFour_of_le
#print axioms Gtz.pivotMinorCoveringFour_eleven_iff_rank_four
#print axioms Gtz.gtz_original_rank_four_of_pivotMinorCoveringFour
#print axioms Gtz.quadTraceLeg
#print axioms Gtz.quadMinorLeg
#print axioms Gtz.quadTieLeg
#print axioms Gtz.schurBlockFour_trace_eq_quadTraceLeg
#print axioms Gtz.schurBlockFour_minorSum_eq_quadMinorLeg
#print axioms Gtz.schurBlockFour_det_eq_quadTieLeg
#print axioms Gtz.quadLegs_nonneg_of_dominates
#print axioms Gtz.exists_negative_form_with_pivotMinors_zero
#print axioms Gtz.tetraDesign_gapTripleMinor
#print axioms Gtz.tetraDesign_gapPairMinor_sum
#print axioms Gtz.deflator_kills_pivotUnit
#print axioms Gtz.borderedQuadratic_nonneg_of_dominates_insert
#print axioms Gtz.discriminant_of_dominates_insert
#print axioms Gtz.crossSum_eq_zero_of_dominates_insert_of_tight
#print axioms Gtz.not_dominates_insert_of_tight_direction
#print axioms Gtz.exists_borderedData_failing_discriminant_at_every_floor
#print axioms Gtz.dominates_of_coercive
#print axioms Gtz.dominates_pushforward_of_dominates_insert
#print axioms Gtz.HasHeavyPivotInDominator
#print axioms Gtz.gtzWeighted_succ_of_heavyPivotInDominator
#print axioms Gtz.exists_projected_dominator_of_dominating_pivot

-- the heavy-pivot decision + the refuted leverage threshold
#print axioms Gtz.pairMinorOffPivot
#print axioms Gtz.pivotTiltForm
#print axioms Gtz.deflatedPairMinorAtLeverage
#print axioms Gtz.discriminantTie_eq_heavyExcess_mul_pairMinorOffPivot_sub_tilt
#print axioms Gtz.discriminantTie_eq_deflatedPairMinorAtLeverage_sub_pairMinorOffPivot
#print axioms Gtz.pairMinorOffPivot_mul_discriminantTrace
#print axioms Gtz.discriminantTrace_nonneg_of_pairMinorOffPivot_pos
#print axioms Gtz.dominates_of_heavyExcess_mul_pairMinorOffPivot_ge
#print axioms Gtz.dominates_iff_heavyExcess_mul_pairMinorOffPivot_ge
#print axioms Gtz.dominates_of_deflatedPairMinorAtLeverage_ge
#print axioms Gtz.tetraDesign_pairMinorOffPivot
#print axioms Gtz.tetraDesign_pivotTiltForm
#print axioms Gtz.tetraDesign_deflatedPairMinorAtLeverage
#print axioms Gtz.tetraDesign_threshold_tight
#print axioms Gtz.CappedDiscriminantCovering
#print axioms Gtz.HeavyAtomCovering
#print axioms Gtz.HeavyPivotCovering
#print axioms Gtz.heavyAtomCovering_of_heavyPivotCovering
#print axioms Gtz.discriminantCovering_of_heavyAtomCovering_of_capped
#print axioms Gtz.rank_three_of_heavyAtomCovering_of_capped
#print axioms Gtz.rank_three_of_heavyPivotCovering_of_capped
#print axioms Gtz.crossBracketValue
#print axioms Gtz.repeatBracketValue
#print axioms Gtz.planeHalfSq_pos
#print axioms Gtz.twoPlaneHalfSq_gt_one
#print axioms Gtz.spikeHeightSq_gt_one
#print axioms Gtz.discriminantTie_eq_crossValue_of_spikeGramData
#print axioms Gtz.discriminantTie_scaled_eq_repeatValue_of_spikeGramData
#print axioms Gtz.discriminantTie_neg_of_spikeGramData
#print axioms Gtz.deflation_pos_and_below_threshold_of_spikeGramData
#print axioms Gtz.discriminantTie_eq_crossTripleValue
#print axioms Gtz.discriminantTrace_eq_crossTripleValue
#print axioms Gtz.dominates_of_crossDirectionGramData
#print axioms Gtz.liftedMercedesAtom
#print axioms Gtz.liftedMercedesWeight
#print axioms Gtz.liftedMercedesAtom_spike
#print axioms Gtz.liftedMercedesAtom_firstDirection
#print axioms Gtz.liftedMercedesAtom_secondDirection
#print axioms Gtz.liftedMercedesAtom_thirdDirection
#print axioms Gtz.liftedMercedesAtom_direction
#print axioms Gtz.liftedMercedesDesign
#print axioms Gtz.liftedMercedesDesign_atom
#print axioms Gtz.liftedMercedesDesign_weight
#print axioms Gtz.liftedMercedesDesign_spike_leverage
#print axioms Gtz.liftedMercedesDesign_offSpike_leverage
#print axioms Gtz.liftedMercedesDesign_spike_heavyExcess
#print axioms Gtz.liftedMercedesDesign_offSpike_heavyExcess
#print axioms Gtz.liftedMercedesDesign_spike_pairing
#print axioms Gtz.liftedMercedesDesign_offSpike_pairing
#print axioms Gtz.liftedMercedesDesign_pairing_firstSecond
#print axioms Gtz.liftedMercedesDesign_pairing_firstThird
#print axioms Gtz.liftedMercedesDesign_pairing_secondThird
#print axioms Gtz.liftedMercedesDesign_allHeavy
#print axioms Gtz.liftedMercedesDesign_spike_leverageScore
#print axioms Gtz.liftedMercedesDesign_not_dominates_spike_triple
#print axioms Gtz.liftedMercedesDesign_dominates_directionTriple
#print axioms Gtz.exists_allHeavy_seven_design_with_unusable_heavy_atom
#print axioms Gtz.not_heavyPivotCovering

-- the (7,3) frontier: decision atlas + tie locus

-- Gtz.Quantitative.DecisionAtlasSevenThree
#print axioms Gtz.splitSevenDirection
#print axioms Gtz.splitSevenAtom
#print axioms Gtz.splitSevenDesign
#print axioms Gtz.splitSevenDesign_leverage
#print axioms Gtz.splitSevenDesign_allHeavy
#print axioms Gtz.splitSevenDesign_heavyExcess
#print axioms Gtz.tetraAtom_dot_of_ne
#print axioms Gtz.splitSevenDesign_atomPairing_of_sameDirection
#print axioms Gtz.splitSevenDesign_atomPairing_of_differentDirection
#print axioms Gtz.splitSevenDirection_no_tripleRepeat
#print axioms Gtz.splitSevenDesign_discriminantTie_eq
#print axioms Gtz.splitSevenDesign_discriminantTie_of_rainbowDirections
#print axioms Gtz.splitSevenDesign_discriminantTie_of_repeatedDirection
#print axioms Gtz.splitSevenDesign_discriminantTie_nonpos
#print axioms Gtz.increasingTriplesSeven
#print axioms Gtz.increasingTriplesSeven_card
#print axioms Gtz.increasingTriplesSeven_distinct
#print axioms Gtz.HasRainbowDirections
#print axioms Gtz.rainbowTriplesSeven_card
#print axioms Gtz.repeatedTriplesSeven_card
#print axioms Gtz.splitSevenDesign_discriminantTie_of_notRainbow
#print axioms Gtz.splitSevenDesign_discriminantTie_sum
#print axioms Gtz.splitSevenDesign_discriminantTrace_of_rainbowDirections
#print axioms Gtz.splitSevenDesign_dominates_of_rainbowDirections
#print axioms Gtz.splitSevenDesign_discriminantTrace_zeroOneTwo
#print axioms Gtz.splitSevenDesign_discriminantTie_zeroOneTwo
#print axioms Gtz.splitSevenDesign_dominates_zeroOneTwo
#print axioms Gtz.splitSevenDesign_tieMean_negative_but_tieMax_zero
#print axioms Gtz.IsInCell
#print axioms Gtz.DoesCellDischarge
#print axioms Gtz.DoesAtlasCover
#print axioms Gtz.DoesAtlasDischarge
#print axioms Gtz.discriminantCovering_of_atlas
#print axioms Gtz.gtzWeightedAll_three_of_atlasSeven
#print axioms Gtz.gtzOriginal_rank_three_of_atlasSeven

-- Gtz.Certificates.PositivstellensatzObstruction
#print axioms Gtz.HasUniformTieAggregateSeven
#print axioms Gtz.splitSevenDesign_weightedTieAggregate_nonpos
#print axioms Gtz.not_hasUniformTieAggregateSeven
#print axioms Gtz.closedTieFailure_inhabited_seven
#print axioms Gtz.closedCoveringFailure_inhabited_seven
#print axioms Gtz.discriminantCovering_seven_iff_strictFailure_empty
#print axioms Gtz.tautologicalCell
#print axioms Gtz.isInCell_tautologicalCell_iff
#print axioms Gtz.tautologicalCell_discharges
#print axioms Gtz.tautologicalAtlas
#print axioms Gtz.tautologicalAtlas_discharges
#print axioms Gtz.tautologicalAtlas_covers_iff
#print axioms Gtz.exists_atlas_iff_discriminantCovering
#print axioms Gtz.exists_atlas_seven_iff_rank_three
#print axioms Gtz.discriminantTie_eq_gramMinorForm
#print axioms Gtz.dominates_of_radiusBox
#print axioms Gtz.symmetricHalfRadius_admissible
#print axioms Gtz.dominates_of_symmetricHalfBox
#print axioms Gtz.dominates_of_coherentPairings
#print axioms Gtz.dominates_of_leverageFloor_and_pairingCap
#print axioms Gtz.tripleGramDet
#print axioms Gtz.tripleGramDet_eq_symmetricFunctionSum
#print axioms Gtz.minLegArgmax_succeeds_iff
#print axioms Gtz.splitSevenDesign_leverage_constant
#print axioms Gtz.splitSevenDesign_tripleGramDet_of_rainbowDirections
#print axioms Gtz.splitSevenDesign_tripleGramDet_of_repeatedDirection
#print axioms Gtz.splitSevenDesign_gramDetArgmax_dominates
#print axioms Gtz.dominates_image_replicationMerge
#print axioms Gtz.subsetSum_replicatedDesign_image_castSucc
#print axioms Gtz.heavyPivotDesign_allHeavy
#print axioms Gtz.heavyPivotSplitSeven
#print axioms Gtz.heavyPivotSplitSeven_atom_castSucc
#print axioms Gtz.heavyPivotSplitSeven_atom_last
#print axioms Gtz.heavyPivotSplitSeven_allHeavy
#print axioms Gtz.heavyPivotSplitSeven_leverage_lt
#print axioms Gtz.heavyPivotSplitSeven_dominates_liftedLastThree
#print axioms Gtz.heavyPivotSplitSeven_heaviest_notIn_dominatingTriple
#print axioms Gtz.heaviestAtomRule_refuted_at_seven

-- Gtz.Ties.SevenThreeTieLocus
#print axioms Gtz.subsetSum_congr_atom
#print axioms Gtz.dominates_congr_atom
#print axioms Gtz.allHeavy_congr_atom
#print axioms Gtz.isTie_congr_atom
#print axioms Gtz.heavyExcess_congr_atom
#print axioms Gtz.atomPairing_congr_atom
#print axioms Gtz.discriminantTrace_congr_atom
#print axioms Gtz.discriminantTie_congr_atom
#print axioms Gtz.tripleSplitTetraDesign
#print axioms Gtz.tripleSplitTetraDesign_atom
#print axioms Gtz.tripleSplitTetraDesign_weight
#print axioms Gtz.tripleSplitTetraDesign_eq_splitSevenDesign
#print axioms Gtz.tripleSplitTetraDesign_allHeavy
#print axioms Gtz.exists_unusedDirection_seven
#print axioms Gtz.splitSevenDesign_gapForm_zero_of_unusedDirection
#print axioms Gtz.splitSevenDesign_no_strictDominator
#print axioms Gtz.splitSevenDesign_isTie
#print axioms Gtz.splitSevenDesign_rainbowTriple_isTie
#print axioms Gtz.splitSevenDesign_not_dominates_of_repeatedDirection
#print axioms Gtz.splitSevenDesign_dominates_iff_rainbowDirections
#print axioms Gtz.splitSevenDesign_dominates_iff_hasRainbowDirections
#print axioms Gtz.splitSevenDesign_excessSum
#print axioms Gtz.splitSevenDesign_discriminantMinorSum_of_rainbowDirections
#print axioms Gtz.splitSevenDesign_gapCharPoly_of_rainbowDirections
#print axioms Gtz.splitSevenDesign_pairingBoundary_of_differentDirection
#print axioms Gtz.splitSevenDesign_normalizedPairing_of_differentDirection
#print axioms Gtz.splitSevenDesign_pairingBoundary_fails_of_sameDirection
#print axioms Gtz.no_leverage_identity_at_seven_three
#print axioms Gtz.splitSevenDesign_leverage_identity_fails
#print axioms Gtz.exists_allHeavy_isTie_and_leverage_identity_fails_at_seven
#print axioms Gtz.splitSevenReweighted
#print axioms Gtz.splitSevenReweighted_atom
#print axioms Gtz.splitSevenReweighted_allHeavy
#print axioms Gtz.splitSevenReweighted_discriminantTie
#print axioms Gtz.splitSevenReweighted_discriminantTrace
#print axioms Gtz.splitSevenReweighted_discriminantTie_sum
#print axioms Gtz.splitSevenReweighted_isTie
#print axioms Gtz.splitSevenReweighted_dominates_iff_rainbowDirections
#print axioms Gtz.splitSevenReweighted_noStressCertificate
#print axioms Gtz.exists_isTie_seven_without_stressCertificate
#print axioms Gtz.splitSevenDesign_tieBoundary_reading

-- the complex per-rank ledger: the trine witness + the phase-defect separation
#print axioms Gtz.complexAtom_apply
#print axioms Gtz.not_posSemidef_of_diag_re_neg
#print axioms Gtz.not_posSemidef_of_det_re_neg_gen
#print axioms Gtz.omegaPow
#print axioms Gtz.omegaPow_zero
#print axioms Gtz.omegaPow_one
#print axioms Gtz.omegaPow_two
#print axioms Gtz.omegaPow_unit
#print axioms Gtz.omegaPow_cross
#print axioms Gtz.trineLeft
#print axioms Gtz.trineRight
#print axioms Gtz.trineAtom
#print axioms Gtz.trineAtom_zero
#print axioms Gtz.trineAtom_one
#print axioms Gtz.trineAtom_two
#print axioms Gtz.trineAtom_three
#print axioms Gtz.trineAtom_four
#print axioms Gtz.trineAtom_five
#print axioms Gtz.trineLeft_coordZero
#print axioms Gtz.trineLeft_coordOne
#print axioms Gtz.trineLeft_coordTwo
#print axioms Gtz.trineRight_coordZero
#print axioms Gtz.trineRight_coordOne
#print axioms Gtz.trineRight_coordTwo
#print axioms Gtz.trineLeft_leverage
#print axioms Gtz.trineRight_leverage
#print axioms Gtz.omegaPow_sum
#print axioms Gtz.omegaPow_conj_sum
#print axioms Gtz.trineParseval
#print axioms Gtz.trineDesign
#print axioms Gtz.det_fin_three_of_offDiag_zero
#print axioms Gtz.tripleGap_apply
#print axioms Gtz.tripleGap_at_one
#print axioms Gtz.trineShape_det
#print axioms Gtz.splitPairLeft_shifted_det
#print axioms Gtz.splitPairRight_shifted_det
#print axioms Gtz.trineMixedLeftPair_charpoly
#print axioms Gtz.trineMixedRightPair_charpoly
#print axioms Gtz.trineMixedLeftPair_det_one
#print axioms Gtz.trineMixedRightPair_det_one
#print axioms Gtz.trineMixedLeftPair_not_psd
#print axioms Gtz.trineMixedRightPair_not_psd
#print axioms Gtz.trinePureLeft_not_psd
#print axioms Gtz.trinePureRight_not_psd
#print axioms Gtz.tripleSubset_enumeration
#print axioms Gtz.trine_no_dominating_triple
#print axioms Gtz.complexGtzWeighted_six_three_fails_via_trine
#print axioms Gtz.rootFiveC
#print axioms Gtz.rootFiveC_sq
#print axioms Gtz.trineCharpoly_factored
#print axioms Gtz.trineMixed_spectrum
#print axioms Gtz.trineMarginRankThree
#print axioms Gtz.trineMargin_isRoot
#print axioms Gtz.trineMargin_window
#print axioms Gtz.trineMargin_lt_one
#print axioms Gtz.pairGap_shifted_det
#print axioms Gtz.sicPair_shifted_det
#print axioms Gtz.alphaRankTwo
#print axioms Gtz.alphaRankTwo_isRoot
#print axioms Gtz.sicPair_det_at_alphaRankTwo
#print axioms Gtz.alphaRankTwo_window
#print axioms Gtz.starDot_conj
#print axioms Gtz.triangleBargmann_swap
#print axioms Gtz.triangleBargmann_add_swap
#print axioms Gtz.gramTriple
#print axioms Gtz.gramTripleExcess_det_expand
#print axioms Gtz.gramTripleExcess_det_split
#print axioms Gtz.bargmannPhaseDefect
#print axioms Gtz.bargmannPhaseDefect_eq_imSq
#print axioms Gtz.bargmannPhaseDefect_nonneg
#print axioms Gtz.realTriple_phaseDefect_zero
#print axioms Gtz.trineOverlap_leftZero_leftOne
#print axioms Gtz.trineOverlap_leftOne_leftZero
#print axioms Gtz.trineOverlap_leftZero_rightZero
#print axioms Gtz.trineOverlap_rightZero_leftZero
#print axioms Gtz.trineOverlap_leftOne_rightZero
#print axioms Gtz.trineOverlap_rightZero_leftOne
#print axioms Gtz.trineOverlapModulus_withinTrine
#print axioms Gtz.trineOverlapModulus_acrossFirst
#print axioms Gtz.trineOverlapModulus_acrossSecond
#print axioms Gtz.trineTriple_bargmann
#print axioms Gtz.trineTriple_bargmann_re
#print axioms Gtz.trineTriple_bargmann_im
#print axioms Gtz.trineTriple_phaseDefect
#print axioms Gtz.trineTriple_bargmann_normSq
#print axioms Gtz.trineTriple_gramExcess_det
#print axioms Gtz.trineTriple_realAvatar_det_pos
#print axioms Gtz.icosaDot_zeroTwo
#print axioms Gtz.icosaDot_twoFour
#print axioms Gtz.icosaDot_fourZero
#print axioms Gtz.icosaTriple_phaseDefect
#print axioms Gtz.icosaTriple_bargmann
#print axioms Gtz.icosaTriple_bargmann_re
#print axioms Gtz.icosaTriple_leverage
#print axioms Gtz.icosaOverlapModulus_zeroTwo
#print axioms Gtz.icosaOverlapModulus_twoFour
#print axioms Gtz.icosaOverlapModulus_zeroFour
#print axioms Gtz.icosaTriple_gramExcess_det
#print axioms Gtz.icosaTriple_modulusBudget_neg
#print axioms Gtz.icosaTriple_gramExcess_det_pos
#print axioms Gtz.realness_separation_mechanism
#print axioms Gtz.paddedMarginRankThree
#print axioms Gtz.scaledSicPair_shifted_det
#print axioms Gtz.paddedMargin_isRoot
#print axioms Gtz.scaledSicPair_det_at_paddedMargin
#print axioms Gtz.paddedMargin_window
#print axioms Gtz.trineMargin_lt_paddedMargin
#print axioms Gtz.trineMargin_lt_alphaRankTwo
#print axioms Gtz.exactValueRankFourAtSix
#print axioms Gtz.ledger_ordering
#print axioms Gtz.hesseCubic_neg_at_seven_tenths
#print axioms Gtz.hesseCubic_pos_at_seventyOne_hundredths
#print axioms Gtz.hesseCubic_hasRootIn
#print axioms Gtz.trineCharpoly_matchesFamilyCubic
#print axioms Gtz.trineFamilyCubic_at_threeQuarters
#print axioms Gtz.trineFamilyCubicRankFour_hasRootIn
#print axioms Gtz.trineFamilyCubicRankFive_hasRootIn
#print axioms Gtz.measuredRankFourCapOne
#print axioms Gtz.measuredRankFourUncapped
#print axioms Gtz.measuredRankFiveCapOne
#print axioms Gtz.measuredRankFiveCapTwo
#print axioms Gtz.petersenConferenceMargin_gt_one
#print axioms Gtz.complexLedger_provenPart

-- Gtz/Reduction/ExchangeRepair.lean
#print axioms Gtz.size_pos_of_weightedDesign
#print axioms Gtz.exists_atom_covering_direction
#print axioms Gtz.atom_mem_failing_lt
#print axioms Gtz.coveringAtom_notMem_of_failing
#print axioms Gtz.swap_repairs_direction
#print axioms Gtz.swap_gapForm_nonneg
#print axioms Gtz.card_swap_eq_card
#print axioms Gtz.exists_swap_repairing_worstDirection
#print axioms Gtz.DoesExchangeImprove
#print axioms Gtz.gtzWeighted_of_exchangeImproves
#print axioms Gtz.gtzWeightedAll_of_exchangeImproves

-- Gtz/Quantitative/GoodTripleGraph.lean
#print axioms Gtz.pairMinor_comm
#print axioms Gtz.discriminantTrace_eq_pairMinor_add
#print axioms Gtz.pairMinor_product_eq_tieSchur
#print axioms Gtz.discriminantTie_swapPair
#print axioms Gtz.IsCompatiblePair
#print axioms Gtz.IsBoxGoodPair
#print axioms Gtz.boxSlack
#print axioms Gtz.isBoxGoodPair_iff_boxSlack_nonneg
#print axioms Gtz.isBoxGoodPair_comm
#print axioms Gtz.isCompatiblePair_comm
#print axioms Gtz.isCompatiblePair_of_isBoxGoodPair
#print axioms Gtz.not_isBoxGoodPair_of_atom_eq
#print axioms Gtz.not_isCompatiblePair_of_atom_eq
#print axioms Gtz.IsBoxGoodTriangle
#print axioms Gtz.IsCompatibleTriangle
#print axioms Gtz.IsElliptopeGoodTriangle
#print axioms Gtz.dominates_of_isBoxGoodTriangle
#print axioms Gtz.pairMinor_nonneg_of_dominates
#print axioms Gtz.isCompatibleTriangle_of_dominates
#print axioms Gtz.dominates_triple_iff_isElliptopeGoodTriangle
#print axioms Gtz.isElliptopeGoodTriangle_of_isBoxGoodTriangle
#print axioms Gtz.isCompatibleTriangle_of_isElliptopeGoodTriangle
#print axioms Gtz.normalizedPairing
#print axioms Gtz.elliptopeBracket
#print axioms Gtz.normalizedPairing_sq
#print axioms Gtz.normalizedPairing_product
#print axioms Gtz.discriminantTie_eq_excessProduct_mul_elliptopeBracket
#print axioms Gtz.discriminantTie_nonneg_iff_elliptopeBracket_nonneg
#print axioms Gtz.isBoxGoodPair_iff_normalizedPairing_sq_le
#print axioms Gtz.isBoxGoodPair_iff_abs_normalizedPairing_le_half
#print axioms Gtz.isCompatiblePair_iff_abs_normalizedPairing_le_one
#print axioms Gtz.BoxGoodTriangleCovering
#print axioms Gtz.ElliptopeGoodTriangleCovering
#print axioms Gtz.CompatibleTriangleCovering
#print axioms Gtz.elliptopeGoodTriangleCovering_iff_gtzWeightedHeavy
#print axioms Gtz.elliptopeGoodTriangleCovering_iff_discriminantCovering
#print axioms Gtz.elliptopeGoodTriangleCovering_seven_iff_rank_three
#print axioms Gtz.discriminantCovering_of_boxGoodTriangleCovering
#print axioms Gtz.compatibleTriangleCovering_of_gtzWeightedHeavy
#print axioms Gtz.not_gtzWeightedAll_three_of_no_compatibleTriangle
#print axioms Gtz.elliptopeGoodTriangleCovering_of_le
#print axioms Gtz.heavyExcess_eq_of_atom_eq
#print axioms Gtz.atomPairing_eq_of_atom_eq
#print axioms Gtz.isBoxGoodPair_iff_of_atom_eq
#print axioms Gtz.isBoxGoodPair_replicatedDesign_iff
#print axioms Gtz.replicationMerge_ne_of_isBoxGoodPair
#print axioms Gtz.boxGoodTriangleCovering_of_succ
#print axioms Gtz.boxGoodTriangleCovering_of_add
#print axioms Gtz.boxGoodTriangleCovering_of_le
#print axioms Gtz.icosaDesign_leverage
#print axioms Gtz.icosaDesign_allHeavy
#print axioms Gtz.icosaDesign_heavyExcess
#print axioms Gtz.icosaDesign_atomPairing_sq_of_ne
#print axioms Gtz.icosaDesign_boxSlack_of_ne
#print axioms Gtz.icosaDesign_boxSlack_self
#print axioms Gtz.icosaDesign_no_isBoxGoodPair
#print axioms Gtz.not_boxGoodTriangleCovering_six
#print axioms Gtz.not_boxGoodTriangleCovering_of_six_le
#print axioms Gtz.not_boxGoodTriangleCovering_seven
#print axioms Gtz.icosaSevenDesign
#print axioms Gtz.icosaSevenDesign_allHeavy
#print axioms Gtz.icosaSevenDesign_no_isBoxGoodPair
#print axioms Gtz.not_boxGoodTriangleCovering_seven_of_icosaSeven
#print axioms Gtz.splitSevenDesign_isBoxGoodPair_of_differentDirection
#print axioms Gtz.splitSevenDesign_isBoxGoodTriangle
#print axioms Gtz.splitSevenDesign_dominates_of_isBoxGoodTriangle
#print axioms Gtz.splitSevenDesign_no_strictBoxGoodPair
#print axioms Gtz.splitSevenDesign_boxSlack_of_differentDirection
#print axioms Gtz.splitSevenDesign_boxSlack_of_sameDirection
#print axioms Gtz.excessGap
#print axioms Gtz.discriminantTie_eq_excessGap_add_tripleProduct
#print axioms Gtz.IsSignBlindGoodTriple
#print axioms Gtz.excessGap_nonneg_of_isSignBlindGoodTriple
#print axioms Gtz.discriminantTie_nonneg_of_isSignBlindGoodTriple
#print axioms Gtz.discriminantTrace_nonneg_of_excessGap_nonneg
#print axioms Gtz.dominates_of_isSignBlindGoodTriple
#print axioms Gtz.isSignBlindGoodTriple_of_isBoxGoodTriangle
#print axioms Gtz.ballRadius_sharp
#print axioms Gtz.SignBlindGoodTripleCovering
#print axioms Gtz.signBlindGoodTripleCovering_of_boxGoodTriangleCovering
#print axioms Gtz.discriminantCovering_of_signBlindGoodTripleCovering
#print axioms Gtz.icosaDesign_atomPairing_sq_ge
#print axioms Gtz.icosaDesign_excessGap_le
#print axioms Gtz.icosaDesign_excessGap_of_distinct
#print axioms Gtz.icosaDesign_no_isSignBlindGoodTriple
#print axioms Gtz.not_signBlindGoodTripleCovering_six
#print axioms Gtz.not_boxGoodTriangleCovering_six_of_signBlind
#print axioms Gtz.excessGap_eq_of_atom_eq
#print axioms Gtz.isSignBlindGoodTriple_iff_of_atom_eq
#print axioms Gtz.isSignBlindGoodTriple_replicatedDesign_iff
#print axioms Gtz.icosaSevenDesign_no_isSignBlindGoodTriple
#print axioms Gtz.not_signBlindGoodTripleCovering_seven
#print axioms Gtz.tetraDesign_excessGap
#print axioms Gtz.tetraDesign_isSignBlindGoodTriple
#print axioms Gtz.splitSevenDesign_excessGap
#print axioms Gtz.splitSevenDesign_isSignBlindGoodTriple
#print axioms Gtz.icosaDesign_heavyExcess_pos
#print axioms Gtz.icosaDesign_normalizedPairing_sq_of_ne
#print axioms Gtz.icosaDesign_isCompatiblePair_of_ne
#print axioms Gtz.icosaDesign_elliptopeBracket_of_distinct
#print axioms Gtz.icosaDesign_dominates_iff_pairingProduct

-- Gtz/Reduction/StrengthenedInductionHypothesis.lean
#print axioms Gtz.quadForm_nonneg_of_posSemidef
#print axioms Gtz.quadForm_sq_le_mul_of_posSemidef
#print axioms Gtz.solutionRate_eq_quadForm
#print axioms Gtz.solutionRate_nonneg
#print axioms Gtz.solutionRate_unique
#print axioms Gtz.exists_solution_of_isUnit_det
#print axioms Gtz.rankOneForm_le_of_solutionRate_le
#print axioms Gtz.solutionRate_le_of_rankOneForm_le
#print axioms Gtz.rankOneForm_le_iff_solutionRate_le
#print axioms Gtz.posSemidef_smul_sub_vecMulVec_of_solutionRate_le
#print axioms Gtz.borderedMatrix
#print axioms Gtz.borderedMatrix_transpose
#print axioms Gtz.borderedMatrix_isHermitian
#print axioms Gtz.borderedMatrix_mulVec_inl
#print axioms Gtz.borderedMatrix_mulVec_inr
#print axioms Gtz.borderedMatrix_form_eq
#print axioms Gtz.borderedMatrix_posSemidef_of_solutionRate_le
#print axioms Gtz.solutionRate_le_of_borderedMatrix_posSemidef
#print axioms Gtz.borderedMatrix_posSemidef_iff_solutionRate_le
#print axioms Gtz.not_posSemidef_transpose_mul_sub_one_of_overfull
#print axioms Gtz.not_posSemidef_gramShift_of_overfull
#print axioms Gtz.couplingVector
#print axioms Gtz.liftBudget
#print axioms Gtz.liftBudget_eq
#print axioms Gtz.projectedGap
#print axioms Gtz.dominates_pushforward_iff_projectedGap_posSemidef
#print axioms Gtz.projectedGap_transpose
#print axioms Gtz.couplingVector_dotProduct
#print axioms Gtz.projectedGap_form
#print axioms Gtz.discriminantConjunct_iff_loewnerSlack
#print axioms Gtz.discriminantConjunct_of_solutionRate_le
#print axioms Gtz.solutionRate_le_of_discriminantConjunct
#print axioms Gtz.dominates_insert_iff_loewnerSlack
#print axioms Gtz.BorderedSlackLifting
#print axioms Gtz.liftingLemma_of_borderedSlackLifting
#print axioms Gtz.gtzWeighted_succ_of_borderedSlackLifting
#print axioms Gtz.gtzWeightedAll_of_borderedSlackLifting
#print axioms Gtz.DoesPropagateBorderedSlack
#print axioms Gtz.gtzWeightedAll_of_base_of_propagates
#print axioms Gtz.HasUniformDominationSlack
#print axioms Gtz.posDef_of_uniformSlack
#print axioms Gtz.not_hasUniformDominationSlack_four_three
#print axioms Gtz.lightTopSide
#print axioms Gtz.lightTopHeight
#print axioms Gtz.lightTopLift
#print axioms Gtz.lightTopPivotHeight
#print axioms Gtz.lightTopSide_sq
#print axioms Gtz.lightTopHeight_sq
#print axioms Gtz.lightTopLift_sq
#print axioms Gtz.lightTopPivotHeight_sq
#print axioms Gtz.lightTopAtom
#print axioms Gtz.lightTopAtom_pivot
#print axioms Gtz.lightTopAtom_one
#print axioms Gtz.lightTopAtom_two
#print axioms Gtz.lightTopAtom_three
#print axioms Gtz.lightTopDesign
#print axioms Gtz.lightTopDesign_atom
#print axioms Gtz.lightTopAtom_leverage_pivot
#print axioms Gtz.lightTopAtom_leverage_one
#print axioms Gtz.lightTopAtom_leverage_two
#print axioms Gtz.lightTopAtom_leverage_three
#print axioms Gtz.lightTopAtom_leverage_simplex
#print axioms Gtz.lightTopAtom_pairing_pivotOne
#print axioms Gtz.lightTopAtom_pairing_pivotTwo
#print axioms Gtz.lightTopAtom_pairing_pivotThree
#print axioms Gtz.lightTopPivotPairing_sq
#print axioms Gtz.lightTopAtom_pairing_oneTwo
#print axioms Gtz.lightTopAtom_pairing_oneThree
#print axioms Gtz.lightTopAtom_pairing_twoThree
#print axioms Gtz.lightTopDesign_dominates_simplexTriple
#print axioms Gtz.lightTopDesign_not_dominates_zeroOneTwo
#print axioms Gtz.lightTopDesign_not_dominates_zeroOneThree
#print axioms Gtz.lightTopDesign_not_dominates_zeroTwoThree
#print axioms Gtz.pivotTriples_enumerated
#print axioms Gtz.lightTopAtom_heavy_iff_pivot
#print axioms Gtz.not_heavyPivotInDominator_four_two
#print axioms Gtz.lightTopDesign_allHeavy

-- projection coordinates: P = VᵀV, the shadow/Pythagoras form of a design
#print axioms Gtz.scaledAtomRows
#print axioms Gtz.scaledAtomRows_row
#print axioms Gtz.transpose_mul_scaledAtomRows
#print axioms Gtz.projectionOfDesign
#print axioms Gtz.projectionOfDesign_apply
#print axioms Gtz.projectionOfDesign_transpose
#print axioms Gtz.projectionOfDesign_mul_self
#print axioms Gtz.projectionOfDesign_diagonal
#print axioms Gtz.trace_projectionOfDesign
#print axioms Gtz.sum_weight_mul_leverage
#print axioms Gtz.selectedAtomRows
#print axioms Gtz.sqrtWeightDiagonal
#print axioms Gtz.isUnit_det_sqrtWeightDiagonal
#print axioms Gtz.selectedGramGap_transpose
#print axioms Gtz.projectionBlock_sub_weightDiagonal
#print axioms Gtz.posSemidef_projectionBlock_iff
#print axioms Gtz.det_projectionBlock_sub_weightDiagonal
#print axioms Gtz.transpose_mul_selectedAtomRows
#print axioms Gtz.dominates_iff_posSemidef_projectionBlock
#print axioms Gtz.dominates_iff_posSemidef_projectionBlock_finset
#print axioms Gtz.posSemidef_smul_iff
#print axioms Gtz.posSemidef_transpose_mul_sub_smul_one_comm
#print axioms Gtz.ProjectionCovering
#print axioms Gtz.FrameProjectionCovering
#print axioms Gtz.submatrix_mul_transpose_eq
#print axioms Gtz.mul_transpose_transpose
#print axioms Gtz.mul_transpose_mul_self
#print axioms Gtz.trace_mul_transpose
#print axioms Gtz.gtzOriginal_iff_frameProjectionCovering
#print axioms Gtz.gtzOriginal_of_projectionCovering
#print axioms Gtz.projectionOfDesign_rowDesign
#print axioms Gtz.frameProjectionCovering_of_gtzWeighted
#print axioms Gtz.det_one_add_smul_mul_transpose
#print axioms Gtz.transpose_mul_scaledAtomRows_map
#print axioms Gtz.projectionOfDesign_map
#print axioms Gtz.det_one_add_X_smul_projectionOfDesign
#print axioms Gtz.sum_det_projectionMinors
#print axioms Gtz.sum_det_projectionMinors_rank
#print axioms Gtz.det_one_add_smul_shifted_real

-- maximal volume: the classical benchmark and the exact deficit to GTZ
#print axioms Gtz.sq_le_mul_diag_of_posSemidef
#print axioms Gtz.twice_crossTerm_le_of_posSemidef
#print axioms Gtz.quadForm_le_trace_mul_dotProduct
#print axioms Gtz.quadForm_le_trace_sub_of_one_le
#print axioms Gtz.classicalDenominator_eq_gtzDenominator_add_deficit
#print axioms Gtz.gtzDenominator_add_deficit_eq_classical
#print axioms Gtz.selectedFrameRows
#print axioms Gtz.projectionBlock_eq_selectedFrameRows_mul_transpose
#print axioms Gtz.det_projectionBlock_eq_sq_volume
#print axioms Gtz.sum_det_frameMinors_rank
#print axioms Gtz.exists_injective_pick_det_ne_zero
#print axioms Gtz.exists_maximalVolume_pick
#print axioms Gtz.solveMatrix
#print axioms Gtz.solveMatrix_mul_selectedFrameRows
#print axioms Gtz.frameRow_eq_solveCombination
#print axioms Gtz.updateRow_selectedFrameRows
#print axioms Gtz.det_selectedFrameRows_update
#print axioms Gtz.injective_update_of_forall_ne
#print axioms Gtz.abs_solveMatrix_le_one_of_maximalVolume
#print axioms Gtz.solveMatrix_submatrix_pick

-- the radius-2 exchange conjecture, REFUTED at rank three
#print axioms Gtz.exchangeDistance
#print axioms Gtz.exchangeDistance_self
#print axioms Gtz.exchangeDistance_le_card
#print axioms Gtz.exchangeDistance_comm_of_card_eq
#print axioms Gtz.exchangeDistance_eq_zero_iff_of_card_eq
#print axioms Gtz.exchangeDistance_swap_eq_one
#print axioms Gtz.le_lambdaMinMat_of_forall
#print axioms Gtz.lambdaMinMat_le_diagonal
#print axioms Gtz.leastEigenvalue
#print axioms Gtz.leastEigenvalue_le_diagonal
#print axioms Gtz.dominates_iff_one_le_leastEigenvalue
#print axioms Gtz.DoesExchangeImproveWithinRadius
#print axioms Gtz.DoesExchangeImproveWithinRadiusHeavy
#print axioms Gtz.IsExchangeStuck
#print axioms Gtz.doesExchangeImprove_of_withinRadius
#print axioms Gtz.doesExchangeImproveWithinRadius_mono
#print axioms Gtz.gtzWeighted_of_exchangeImprovesWithinRadius
#print axioms Gtz.doesExchangeImproveWithinRadius_iff_unbounded_of_rank_le
#print axioms Gtz.doesExchangeImprove_leastEigenvalue_iff_gtzWeighted
#print axioms Gtz.rank_lt_trace_subsetSum_of_allHeavy
#print axioms Gtz.subsetSum_diagonal
#print axioms Gtz.sum_over_triple
#print axioms Gtz.radiusTwoStuckAtom
#print axioms Gtz.radiusTwoStuckDesign
#print axioms Gtz.radiusTwoStuckSubset
#print axioms Gtz.radiusTwoStuckSubset_card
#print axioms Gtz.fin_six_index_cases
#print axioms Gtz.radiusTwoStuckDesign_allHeavy
#print axioms Gtz.radiusTwoStuckSubset_form
#print axioms Gtz.radiusTwoStuckDesign_not_dominates
#print axioms Gtz.radiusTwoStuckDesign_dominates_axisTriple
#print axioms Gtz.stuckSubset_le_leastEigenvalue
#print axioms Gtz.radiusTwoStuckDesign_diagonal_triple
#print axioms Gtz.radiusTwoStuckDesign_diagonal_le
#print axioms Gtz.radiusTwoNeighbour_leastEigenvalue_le
#print axioms Gtz.radiusTwoStuckSubset_isExchangeStuck
#print axioms Gtz.not_exchangeImprovesWithinRadius_two_rankThree
#print axioms Gtz.not_exchangeImprovesWithinRadius_of_le_two_rankThree
#print axioms Gtz.not_exchangeImprovesWithinRadiusHeavy_two_rankThree
#print axioms Gtz.not_exchangeImprovesWithinRadiusHeavy_of_le_two_rankThree

-- ExchangeInvariant grown: (7,3) lambda_min + clipped-trace stalls, shadow-determinant argmax refuted
#print axioms Gtz.exchangeDistance_le_iff_le_card_inter_add
#print axioms Gtz.lambdaMinMat_mul_dotProduct_self_le
#print axioms Gtz.le_lambdaMinMat_iff_forall_dotProduct
#print axioms Gtz.doesExchangeImprove_iff_gtzWeighted_ofThreshold
#print axioms Gtz.DoesExchangeImproveHeavy
#print axioms Gtz.doesExchangeImproveHeavy_of_doesExchangeImprove
#print axioms Gtz.gtzWeightedHeavy_of_exchangeImprovesHeavy
#print axioms Gtz.doesExchangeImproveHeavy_of_withinRadiusHeavy
#print axioms Gtz.gtzWeightedHeavy_of_exchangeImprovesWithinRadiusHeavy
#print axioms Gtz.doesExchangeImproveWithinRadiusHeavy_of_withinRadius
#print axioms Gtz.HasLeastEigenvalueAtLeast
#print axioms Gtz.posSemidef_subsetSum
#print axioms Gtz.transpose_subsetSum_sub_smul
#print axioms Gtz.shiftedGap_form
#print axioms Gtz.hasLeastEigenvalueAtLeast_iff
#print axioms Gtz.hasLeastEigenvalueAtLeast_mono
#print axioms Gtz.dominates_iff_leastEigenvalueAtLeast_one
#print axioms Gtz.not_leastEigenvalueAtLeast_of_witness
#print axioms Gtz.not_leastEigenvalueAtLeast_of_subsetBound
#print axioms Gtz.dominatedLevels
#print axioms Gtz.IsLeastEigenvalueScore
#print axioms Gtz.leastEigenvalueScore
#print axioms Gtz.zero_mem_dominatedLevels
#print axioms Gtz.bddAbove_dominatedLevels
#print axioms Gtz.hasLeastEigenvalueAtLeast_sSup
#print axioms Gtz.isLeastEigenvalueScore_leastEigenvalueScore
#print axioms Gtz.eq_of_isLeastEigenvalueScore
#print axioms Gtz.isLeastEigenvalueScore_leastEigenvalue
#print axioms Gtz.doesExchangeImprove_iff_gtzWeighted_ofSpec
#print axioms Gtz.isHermitian_sub_smul_one
#print axioms Gtz.eigenvalue_ge_of_posSemidef_sub_smul_one
#print axioms Gtz.posSemidef_sub_smul_one_of_eigenvalue_ge
#print axioms Gtz.scalar_eq_smul_one
#print axioms Gtz.prod_level_sub_eigenvalues
#print axioms Gtz.subsetSum_isHermitian
#print axioms Gtz.clippedTrace
#print axioms Gtz.clippedTrace_le_rank
#print axioms Gtz.clippedTrace_eq_rank_of_dominates
#print axioms Gtz.dominates_of_clippedTrace_eq_rank
#print axioms Gtz.dominates_iff_clippedTrace_eq_rank
#print axioms Gtz.clippedTrace_lt_rank_of_not_dominates
#print axioms Gtz.doesExchangeImprove_clippedTrace_iff_gtzWeighted
#print axioms Gtz.two_add_level_le_clipped_sum
#print axioms Gtz.clippedTrace_ge_of_certificates
#print axioms Gtz.clippedTrace_lt_of_det_pos
#print axioms Gtz.subsetSum_apply
#print axioms Gtz.shadowDeterminant
#print axioms Gtz.sum_shadowDeterminant_eq_one
#print axioms Gtz.enumerationEquiv
#print axioms Gtz.shadowDeterminant_eq_det_submatrix
#print axioms Gtz.submatrix_scaledAtomRows_eq
#print axioms Gtz.shadowDeterminant_eq_weightProduct_mul_detSq
#print axioms Gtz.image_orderEmbOfFin
#print axioms Gtz.shadowDeterminant_eq_orderEmb
#print axioms Gtz.shadowDeterminant_nonneg
#print axioms Gtz.shadowDeterminant_pos_of_dominates
#print axioms Gtz.exists_shadowDeterminant_ge_inv_binomial
#print axioms Gtz.shadowDeterminant_le_one
#print axioms Gtz.sevenThreeStallAtom
#print axioms Gtz.sevenThreeStallWeight
#print axioms Gtz.sevenThreeStallAtom_zero
#print axioms Gtz.sevenThreeStallAtom_one
#print axioms Gtz.sevenThreeStallAtom_two
#print axioms Gtz.sevenThreeStallAtom_three
#print axioms Gtz.sevenThreeStallAtom_four
#print axioms Gtz.sevenThreeStallAtom_five
#print axioms Gtz.sevenThreeStallAtom_six
#print axioms Gtz.sevenThreeStallWeight_zero
#print axioms Gtz.sevenThreeStallWeight_one
#print axioms Gtz.sevenThreeStallWeight_two
#print axioms Gtz.sevenThreeStallWeight_three
#print axioms Gtz.sevenThreeStallWeight_four
#print axioms Gtz.sevenThreeStallWeight_five
#print axioms Gtz.sevenThreeStallWeight_six
#print axioms Gtz.sevenThreeStallDesign
#print axioms Gtz.sevenThreeStallDesign_atom
#print axioms Gtz.sevenThreeStallDesign_weight
#print axioms Gtz.allHeavy_sevenThreeStallDesign
#print axioms Gtz.sevenThreeStallTriple
#print axioms Gtz.card_sevenThreeStallTriple
#print axioms Gtz.not_dominates_sevenThreeStallTriple
#print axioms Gtz.hasLeastEigenvalueAtLeast_sevenThreeStallTriple
#print axioms Gtz.bound_sevenThreeFamilyOne
#print axioms Gtz.bound_sevenThreeFamilyTwo
#print axioms Gtz.bound_sevenThreeFamilyThree
#print axioms Gtz.bound_sevenThreeFamilyFour
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeFamilyOne
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeFamilyTwo
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeFamilyThree
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeFamilyFour
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeOneTwoFive
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeZeroOneTwo
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeZeroTwoFive
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeOneTwoThree
#print axioms Gtz.not_leastEigenvalueAtLeast_sevenThreeOneThreeFive
#print axioms Gtz.not_leastEigenvalueAtLeast_of_meetsSevenThreeStall
#print axioms Gtz.dominates_sevenThreeDominatingTriple
#print axioms Gtz.dominates_sevenThreeSecondDominatingTriple
#print axioms Gtz.disjoint_sevenThreeStallTriple_dominators
#print axioms Gtz.sevenThreeStallTriple_isExchangeStuck
#print axioms Gtz.not_exchangeImprovesWithinRadius_two_sevenThree
#print axioms Gtz.not_exchangeImprovesWithinRadiusHeavy_two_sevenThree
#print axioms Gtz.not_exchangeImprovesWithinRadius_of_le_two_sevenThree
#print axioms Gtz.not_exchangeImprovesWithinRadius_two_leastEigenvalueScore
#print axioms Gtz.not_exchangeImprovesWithinRadius_two_leastEigenvalue
#print axioms Gtz.not_exchangeImprovesWithinRadiusHeavy_two_leastEigenvalue
#print axioms Gtz.exists_allHeavy_sevenThreeRadiusTwoStall
#print axioms Gtz.clippedTraceStallDesign
#print axioms Gtz.clippedTraceStallDesign_isAllHeavy
#print axioms Gtz.clippedTraceStallSubset
#print axioms Gtz.clippedTraceStallSubset_card
#print axioms Gtz.subsetSum_clippedTraceStallSubset
#print axioms Gtz.clippedTraceStallSubset_gap
#print axioms Gtz.clippedTraceStallSubset_not_dominates
#print axioms Gtz.clippedTraceStallSubset_floorGap
#print axioms Gtz.clippedTraceStallSubset_floorPsd
#print axioms Gtz.clippedTraceStallSubset_reflectedGap
#print axioms Gtz.clippedTraceStallSubset_reflectedDetPos
#print axioms Gtz.clippedTraceStallSubset_traceGt
#print axioms Gtz.subsetSum_clippedTraceStallDominator
#print axioms Gtz.clippedTraceStallDominator_gap
#print axioms Gtz.clippedTraceStallDominator_dominates
#print axioms Gtz.clippedTraceStallDesign_hasDominatingSubset
#print axioms Gtz.clippedTraceStallSubset_clippedTrace_ge
#print axioms Gtz.clippedTraceNeighbour_cases
#print axioms Gtz.clippedTraceNeighbour_013_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_014_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_015_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_023_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_024_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_025_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_034_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_035_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_036_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_045_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_046_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_056_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_123_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_124_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_125_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_134_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_135_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_136_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_145_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_146_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_156_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_234_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_235_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_236_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_245_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_246_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_256_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_346_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_356_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_456_clippedTrace_lt
#print axioms Gtz.clippedTraceNeighbour_lt
#print axioms Gtz.clippedTraceStallSubset_isExchangeStuck
#print axioms Gtz.not_exchangeImprovesWithinRadius_clippedTrace_two
#print axioms Gtz.not_exchangeImprovesWithinRadiusHeavy_clippedTrace_two
#print axioms Gtz.not_exchangeImprovesWithinRadius_clippedTrace_of_le_two
#print axioms Gtz.not_exchangeImprovesWithinRadiusHeavy_clippedTrace_of_le_two
#print axioms Gtz.dominating_disjoint_from_clippedTraceStallSubset
#print axioms Gtz.shadowArgmaxVector
#print axioms Gtz.shadowArgmaxNumerator
#print axioms Gtz.shadowArgmaxAtom
#print axioms Gtz.shadowArgmaxWeight
#print axioms Gtz.shadowArgmaxDesign
#print axioms Gtz.shadowArgmaxDesign_atom
#print axioms Gtz.shadowArgmaxDesign_weight
#print axioms Gtz.shadowArgmaxLeverage
#print axioms Gtz.shadowArgmaxLeverage_ge_two
#print axioms Gtz.shadowArgmaxDesign_allHeavy
#print axioms Gtz.shadowArgmaxSubset
#print axioms Gtz.shadowArgmaxPick
#print axioms Gtz.shadowArgmaxSubset_card
#print axioms Gtz.shadowArgmaxPick_injective
#print axioms Gtz.shadowArgmaxPick_image
#print axioms Gtz.subsetSum_shadowArgmaxSubset
#print axioms Gtz.gap_shadowArgmaxSubset
#print axioms Gtz.shadowArgmaxSubset_not_dominates
#print axioms Gtz.shadowArgmaxDet
#print axioms Gtz.shadowArgmaxIntegerShadow
#print axioms Gtz.shadowArgmaxIntegerShadow_le
#print axioms Gtz.shadowArgmaxIntegerShadow_attained
#print axioms Gtz.det_selectedAtomRows_shadowArgmaxDesign
#print axioms Gtz.shadowDeterminant_shadowArgmaxDesign
#print axioms Gtz.shadowDeterminant_shadowArgmaxSubset
#print axioms Gtz.shadowDeterminant_le_shadowArgmaxSubset
#print axioms Gtz.not_exchangeImprovesHeavy_shadowDeterminant
#print axioms Gtz.not_exchangeImproves_shadowDeterminant
#print axioms Gtz.not_exchangeImproves_shadowDeterminant_family
#print axioms Gtz.shadowArgmaxDesign_hasDominatingSubset
#print axioms Gtz.boundedRadiusExchange_refuted_sevenThree
#print axioms Gtz.boundedRadiusExchangeHeavy_refuted_sevenThree
#print axioms Gtz.doesExchangeImproveWithinRadius_three_sevenThree_iff_gtzWeighted
#print axioms Gtz.gtzWeighted_sevenThree_of_exchangeImprovesWithinRadius

#print axioms Gtz.starDot_swap
#print axioms Gtz.complexAtom_mulVec
#print axioms Gtz.quadForm_complexAtom
#print axioms Gtz.complexParseval_quadForm
#print axioms Gtz.complexParseval_normSq
#print axioms Gtz.starDot_self_eq_sumNormSq
#print axioms Gtz.complexAtom_posSemidef
#print axioms Gtz.posSemidef_atomSum
#print axioms Gtz.posSemidef_atomSum_sub_smul_one
#print axioms Gtz.complexSize_pos
#print axioms Gtz.exists_atom_covering_direction_complex
#print axioms Gtz.complexGtzWeighted_rankOne
#print axioms Gtz.conjugateAtomRows
#print axioms Gtz.weightDiagonal
#print axioms Gtz.conjugateAtomRows_mulVec
#print axioms Gtz.conjTranspose_mul_weightDiagonal_mul_conjugateAtomRows
#print axioms Gtz.indexShadow
#print axioms Gtz.det_one_add_smul_mul_of_leftInverse
#print axioms Gtz.sum_det_indexShadowMinors_rank
#print axioms Gtz.selectedComplexRows
#print axioms Gtz.submatrix_mul_diagonal
#print axioms Gtz.submatrix_mul_conjTranspose
#print axioms Gtz.det_indexShadow_submatrix
#print axioms Gtz.det_indexShadow_subtypeSubmatrix
#print axioms Gtz.exists_pick_det_ne_zero
#print axioms Gtz.exists_maximalVolume_pick_complex
#print axioms Gtz.complexSolveMatrix
#print axioms Gtz.complexSolveMatrix_mul_selected
#print axioms Gtz.complexRow_eq_solveCombination
#print axioms Gtz.updateRow_selectedComplexRows
#print axioms Gtz.det_selectedComplexRows_update
#print axioms Gtz.norm_complexSolveMatrix_le_one_of_maximalVolume
#print axioms Gtz.normSq_solveCombination_le
#print axioms Gtz.selectedComplexRows_mulVec
#print axioms Gtz.exists_maximalVolume_covering
#print axioms Gtz.ComplexGtzWeightedAtLevel
#print axioms Gtz.complexGtzWeightedAtLevel_one_iff
#print axioms Gtz.exists_subset_atomSum_sub_rankInverse_posSemidef
#print axioms Gtz.exists_subset_atomSum_sub_maximalVolumeLevel_posSemidef
#print axioms Gtz.complexGtzWeightedAtLevel_rankInverse
#print axioms Gtz.exists_subset_atomSum_sub_third_posSemidef
#print axioms Gtz.shadowVolume
#print axioms Gtz.shadowVolume_nonneg
#print axioms Gtz.det_indexShadow_submatrix_real
#print axioms Gtz.exists_pick_shadowVolume_ge_average
#print axioms Gtz.ComplexUniformLevel
#print axioms Gtz.not_complexUniformLevel_one
#print axioms Gtz.rootFiveC_conj
#print axioms Gtz.splitPairLeft_binding_decomp
#print axioms Gtz.splitPairRight_binding_decomp
#print axioms Gtz.trineMargin_cast
#print axioms Gtz.bindingWeightPair_nonneg
#print axioms Gtz.bindingWeightSingle_nonneg
#print axioms Gtz.trineMixedLeftPair_psd_at_margin
#print axioms Gtz.trineMixedRightPair_psd_at_margin
#print axioms Gtz.trineMargin_pos
#print axioms Gtz.trineMixedDet_neg_of_le
#print axioms Gtz.trineMixedLeftPair_not_psd_above
#print axioms Gtz.trineMixedRightPair_not_psd_above
#print axioms Gtz.trinePureLeft_not_psd_above
#print axioms Gtz.trinePureRight_not_psd_above
#print axioms Gtz.tripleAtomSum_expand
#print axioms Gtz.trine_no_triple_above_margin
#print axioms Gtz.trine_bindingTriple_psd_at_margin
#print axioms Gtz.trineMargin_isLeastAndAttained
#print axioms Gtz.posSemidef_sub_smul_one_of_le
#print axioms Gtz.trineDominatedShifts
#print axioms Gtz.trineDominatedShifts_eq_Iic
#print axioms Gtz.trineMargin_isGreatest
#print axioms Gtz.trine_psd_at_margin_iff
#print axioms Gtz.trine_optimalSubsets_count
#print axioms Gtz.trinePureLeft_dominatedShifts_isGreatest_zero
#print axioms Gtz.eigenvalue_real_and_ge_of_posSemidef_sub
#print axioms Gtz.splitPairLeftNullVector
#print axioms Gtz.splitPairLeftNullVector_orthogonal_pairAtom
#print axioms Gtz.splitPairLeftNullVector_orthogonal_singleAtom
#print axioms Gtz.splitPairLeftNullVector_ne_zero
#print axioms Gtz.splitPairLeft_binding_mulVec_zero
#print axioms Gtz.splitPairLeft_binding_mulVec
#print axioms Gtz.trineBindingNullVector
#print axioms Gtz.trineBindingNullVector_ne_zero
#print axioms Gtz.trineBinding_mulVec_nullVector
#print axioms Gtz.trineBinding_spectrum_real_and_ge
#print axioms Gtz.trineBinding_leastEigenvalue
#print axioms Gtz.trineMargin_isExactRankThreeValue
#print axioms Gtz.omegaRoot_conj_sq
#print axioms Gtz.starDot_triple
#print axioms Gtz.sumUnivNine
#print axioms Gtz.hesseUnit
#print axioms Gtz.hesseUnit_leverage
#print axioms Gtz.hesseUnit_overlapCube
#print axioms Gtz.hesseUnit_parseval
#print axioms Gtz.hesseAmpC
#print axioms Gtz.hesseAmpC_conj
#print axioms Gtz.hesseAmpC_sq
#print axioms Gtz.hesseAtom
#print axioms Gtz.hesseAtom_starDot
#print axioms Gtz.hesseAtom_leverage
#print axioms Gtz.hesseAtom_overlapCube
#print axioms Gtz.eq_of_cube_eq_cube_of_nonneg
#print axioms Gtz.hesseAtom_overlapModulus
#print axioms Gtz.hesseTriple_bargmannCube
#print axioms Gtz.re_le_half_of_cube_eq_neg
#print axioms Gtz.hesseTriple_bargmann_re_le
#print axioms Gtz.tripleAtomSum_shifted_det
#print axioms Gtz.hesseTriple_shifted_det
#print axioms Gtz.hesseTriple_not_posSemidef
#print axioms Gtz.complexAtom_hesseAtom
#print axioms Gtz.hesseParseval
#print axioms Gtz.hesseDesign
#print axioms Gtz.hesseDesign_atom
#print axioms Gtz.hesseTripleSum_expand
#print axioms Gtz.hesse_no_triple_above
#print axioms Gtz.complexGtzWeighted_nine_three_fails_via_hesse
#print axioms Gtz.hesseMarginRankThree
#print axioms Gtz.cosTwoPiNinth_isRoot
#print axioms Gtz.hesseMargin_isRoot
#print axioms Gtz.cosTwoPiNinth_gt_half
#print axioms Gtz.hesseMargin_nonneg
#print axioms Gtz.hesseMargin_lt_threeHalves
#print axioms Gtz.hesseMargin_window
#print axioms Gtz.hesseCubic_pos_above_margin
#print axioms Gtz.hesseCubicRoot_eq_hesseMargin
#print axioms Gtz.hesseCubic_at_trineMargin
#print axioms Gtz.hesseCubic_pos_at_trineMargin
#print axioms Gtz.hesseMargin_lt_trineMargin
#print axioms Gtz.cosTwoPiNinth_gt_rootFive_div_three
#print axioms Gtz.hesseWindowMember_lt_trineMargin
#print axioms Gtz.rankThree_recordOrdering
#print axioms Gtz.hesse_no_triple_above_margin
#print axioms Gtz.hesse_no_triple_at_trineMargin
#print axioms Gtz.hesseBeatsTrine
#print axioms Gtz.ComplexDominatesAtLevel
#print axioms Gtz.complexDominatesAtLevel_one
#print axioms Gtz.ComplexDesignValueAtMost
#print axioms Gtz.complexDesignValueAtMost_mono
#print axioms Gtz.not_complexGtzWeighted_of_designValueAtMost
#print axioms Gtz.ComplexRankConstantAtMost
#print axioms Gtz.complexRankConstantAtMost_mono
#print axioms Gtz.ComplexRankConstantAtLeast
#print axioms Gtz.complexRankConstantAtLeast_rankInverse
#print axioms Gtz.unitRankOneDesign
#print axioms Gtz.unitRankOneDesign_atom
#print axioms Gtz.unitRankOneDesign_valueAtMost
#print axioms Gtz.complexRankConstantAtMost_one
#print axioms Gtz.complexRankConstantAtLeast_one
#print axioms Gtz.sicDesign_atom
#print axioms Gtz.sicPairCharpoly_factored
#print axioms Gtz.sicPairCharpoly_neg_of_le
#print axioms Gtz.sicPair_not_posSemidef_above_alphaRankTwo
#print axioms Gtz.sicDesign_valueAtMost
#print axioms Gtz.complexRankConstantAtMost_two_sic
#print axioms Gtz.trineDesign_valueAtMost
#print axioms Gtz.hesseDesign_valueAtMost
#print axioms Gtz.complexRankConstantAtMost_three_hesse
#print axioms Gtz.complexRankConstantAtMost_three_trine
#print axioms Gtz.complexRankOne_closed
#print axioms Gtz.complexRankTwo_provedWindow
#print axioms Gtz.complexRankThree_provedWindow
#print axioms Gtz.complexPerRankLedger

#print axioms Gtz.atomRowMatrix
#print axioms Gtz.atomRowMatrix_row
#print axioms Gtz.selectedFrameRows_atomRowMatrix
#print axioms Gtz.selectedFrameRows_scaledAtomRows
#print axioms Gtz.exists_injective_pick_det_atomRowMatrix_ne_zero
#print axioms Gtz.exists_maximalVolumePick_of_witness
#print axioms Gtz.abs_solveMatrix_le_one_of_maximalVolume_row
#print axioms Gtz.dotProduct_atomMatrix_mulVec
#print axioms Gtz.dotProduct_self_eq_sum_weight_mul_sq
#print axioms Gtz.dotProduct_subsetSum_mulVec
#print axioms Gtz.sum_sq_selected_nonneg
#print axioms Gtz.sq_dotProduct_le_rank_mul_selected
#print axioms Gtz.dotProduct_self_le_rank_mul_selected
#print axioms Gtz.sq_dotProduct_le_selected_of_mem
#print axioms Gtz.dotProduct_self_le_selectedWeight_mul_selected
#print axioms Gtz.GtzWeightedFloor
#print axioms Gtz.posSemidef_sub_smul_one_of_level_le
#print axioms Gtz.sum_weight_subset_le_one
#print axioms Gtz.exists_selection_posSemidef_sub_selectedWeight_level
#print axioms Gtz.gtzWeightedFloor_inv_rank
#print axioms Gtz.exists_rowPick_posSemidef_sub_inv_size_mul_rank

#print axioms Gtz.abs_le_sqrt_mul_sqrt_diag_of_posSemidef
#print axioms Gtz.quadForm_le_sq_sum_sqrt_diag
#print axioms Gtz.posSemidef_diagonal_sub_of_sum_diag_div_le_one
#print axioms Gtz.exists_residual_notPosSemidef_of_mass_gt_one
#print axioms Gtz.complementProjection
#print axioms Gtz.complementProjection_transpose
#print axioms Gtz.complementProjection_mul_self
#print axioms Gtz.complementProjection_posSemidef
#print axioms Gtz.coLeverageScore
#print axioms Gtz.complementProjection_diagonal
#print axioms Gtz.coLeverageScore_nonneg
#print axioms Gtz.sum_coLeverageScore
#print axioms Gtz.coLeverageRatio
#print axioms Gtz.coLeverageRatio_nonneg
#print axioms Gtz.one_sub_weight_mul_coLeverageRatio
#print axioms Gtz.sum_one_sub_weight_mul_coLeverageRatio
#print axioms Gtz.sum_orderEmbOfFin_eq_sum
#print axioms Gtz.projectionBlock_sub_weightDiagonal_eq_coWeight_sub_complementBlock
#print axioms Gtz.dominates_of_sum_coLeverageRatio_le_one
#print axioms Gtz.sum_weight_mul_le_max
#print axioms Gtz.exists_erase_sum_coLeverageRatio_le_one
#print axioms Gtz.exists_erase_dominates_of_corank_one
#print axioms Gtz.IsCoLeverageBalanced
#print axioms Gtz.isCoLeverageBalanced_of_uniformWeight_of_equalLeverage
#print axioms Gtz.coLeverageRatio_of_isCoLeverageBalanced
#print axioms Gtz.sum_coLeverageRatio_of_isCoLeverageBalanced
#print axioms Gtz.classicalDenominator_le_frameSize_iff_diagonalRung
#print axioms Gtz.sum_coLeverageRatio_le_one_iff_of_isCoLeverageBalanced
#print axioms Gtz.balancedPairDesign
#print axioms Gtz.isCoLeverageBalanced_balancedPairDesign
#print axioms Gtz.balancedPairDesign_dominated_and_criterion_blind
#print axioms Gtz.balancedOctahedronDesign
#print axioms Gtz.leverageOf_balancedOctahedronDesign
#print axioms Gtz.isCoLeverageBalanced_balancedOctahedronDesign
#print axioms Gtz.sum_coLeverageRatio_balancedOctahedronDesign
#print axioms Gtz.dominates_balancedOctahedronDesign_coordinateTriple
#print axioms Gtz.balancedOctahedronDesign_criterion_blind
#print axioms Gtz.balancedOctahedronDesign_dominated_and_criterion_blind
#print axioms Gtz.selectiveAxisDesign
#print axioms Gtz.coLeverageRatio_selectiveAxisDesign
#print axioms Gtz.sum_coLeverageRatio_selectiveAxisDesign_heavyTriple
#print axioms Gtz.dominates_selectiveAxisDesign_heavyTriple
#print axioms Gtz.selectiveAxisDesign_criterion_blindOnLightTriple
#print axioms Gtz.isEmpty_weightedDesign_of_sizeZero
#print axioms Gtz.nonempty_weightedDesign_square_of_rank_pos

-- Gtz.Ties.SplitClassTieFamily: the tie stratum over the whole weight simplex
#print axioms Gtz.classTotalWeight
#print axioms Gtz.classTotalWeight_pos
#print axioms Gtz.classTotalWeight_eq
#print axioms Gtz.classTotalWeight_sum
#print axioms Gtz.splitClassAtom
#print axioms Gtz.splitClassAtom_eq_of_sameClass
#print axioms Gtz.sum_weight_smul_splitClassAtomMatrix
#print axioms Gtz.splitClassDesign
#print axioms Gtz.splitClassDesign_weight
#print axioms Gtz.splitClassDesign_atom
#print axioms Gtz.subsetSum_splitClassDesign_of_injOn
#print axioms Gtz.splitClassDesign_isTie
#print axioms Gtz.exists_isTie_of_weights_of_classes
#print axioms Gtz.sixIntoFourBalanced
#print axioms Gtz.sixIntoFourHeavy
#print axioms Gtz.sevenIntoFourBalanced
#print axioms Gtz.sixIntoFourBalanced_surjective
#print axioms Gtz.sixIntoFourHeavy_surjective
#print axioms Gtz.sevenIntoFourBalanced_surjective
#print axioms Gtz.exists_isTie_six_three
#print axioms Gtz.exists_isTie_seven_three

-- Gtz.Quantitative.PhaseFreeNoGo: no phase-free certificate exists, at any degree
#print axioms Gtz.dotProduct_eq_sum_weight_mul_pair
#print axioms Gtz.phaseFreeOfDesign
#print axioms Gtz.discriminantTrace_eq_traceLeg
#print axioms Gtz.discriminantTie_eq_determinantLeg
#print axioms Gtz.isPhaseFreeAdmissible_of_design
#print axioms Gtz.discriminantCovering_of_phaseFreeCovering
#print axioms Gtz.sum_eq_sum_directionMass
#print axioms Gtz.trineOverlap_uniform_sum
#print axioms Gtz.trineTriangleTable_uniform_sum
#print axioms Gtz.trineTriangleTable_cap
#print axioms Gtz.trineTriangleTable_determinant_neg
#print axioms Gtz.trinePoint_generic
#print axioms Gtz.trinePoint_determinantLeg_neg
#print axioms Gtz.trineSixData_isPhaseFreeAdmissible
#print axioms Gtz.trineSixData_determinantLeg_neg
#print axioms Gtz.trineSevenDirection_collision
#print axioms Gtz.trineSevenData_isPhaseFreeAdmissible
#print axioms Gtz.trineSevenData_determinantLeg_neg
#print axioms Gtz.not_phaseFreeCovering_six
#print axioms Gtz.not_phaseFreeCovering_seven
#print axioms Gtz.phaseFree_certificates_cannot_prove_rank_three

-- Gtz.Quantitative.TwoMomentCertificate: the two-moment certificate + the icosahedron cap
#print axioms Gtz.twoMoment_factorisation
#print axioms Gtz.twoMoment_multiplier_pos
#print axioms Gtz.one_le_of_twoMoment
#print axioms Gtz.eigenvector_congruence
#print axioms Gtz.posSemidef_sub_one_of_eigenvalues_ge_one
#print axioms Gtz.posSemidef_sub_one_of_twoMoment
#print axioms Gtz.twoMomentGap
#print axioms Gtz.twoMomentGap_eq_det_trace
#print axioms Gtz.dominates_of_twoMomentGap_nonneg
#print axioms Gtz.icosa_twoMomentGap_eq
#print axioms Gtz.icosa_twoMomentGap_neg
#print axioms Gtz.icosa_no_twoMoment_certificate
#print axioms Gtz.tetra_twoMomentGap_eq_zero

-- Gtz.Ties.StratumFirstOrder: first-order Farkas stuckness at the (7,3) tie stratum
#print axioms Gtz.sum_atomMatrix_tetraAtom_eq_four_smul_one
#print axioms Gtz.sum_three_atomMatrix_tetraAtom
#print axioms Gtz.splitSevenDesign_weight_apply
#print axioms Gtz.rainbowSevenFirst
#print axioms Gtz.rainbowSevenSecond
#print axioms Gtz.rainbowSevenThird
#print axioms Gtz.rainbowSevenTriple
#print axioms Gtz.rainbowSevenMissedDirection
#print axioms Gtz.rainbowSevenMultiplier
#print axioms Gtz.rainbowSevenIndices_distinct
#print axioms Gtz.rainbowSevenDirections_distinct
#print axioms Gtz.rainbowSevenDirections_ne_missed
#print axioms Gtz.rainbowSevenDirections_cover
#print axioms Gtz.sum_rainbowSevenTriple
#print axioms Gtz.rainbowSevenTriple_card
#print axioms Gtz.rainbowSevenTriple_injective
#print axioms Gtz.rainbowSevenTriple_eq_rainbowFamily
#print axioms Gtz.mem_rainbowSevenTriple_iff
#print axioms Gtz.rainbowSevenTriple_direction_ne_missed
#print axioms Gtz.rainbowSevenMultiplier_pos
#print axioms Gtz.rainbowSevenMultiplier_sum_one
#print axioms Gtz.splitSevenDesign_subsetSum_rainbow
#print axioms Gtz.splitSevenDesign_rainbowGap
#print axioms Gtz.splitSevenDesign_rainbowGap_form
#print axioms Gtz.rainbowSevenTriple_dominates
#print axioms Gtz.rainbowSevenTriple_gapForm_missedDirection
#print axioms Gtz.rainbowSevenTriple_tightEigenvector
#print axioms Gtz.rainbowSevenTriple_gap_mulVec_of_orthogonal
#print axioms Gtz.rainbowSevenTriple_not_posDef
#print axioms Gtz.rainbowSevenTriple_lambdaMinMat_eq_one
#print axioms Gtz.tetraNormalDirection
#print axioms Gtz.tetraNormalDirection_dot_left
#print axioms Gtz.tetraNormalDirection_dot_right
#print axioms Gtz.tetraNormalDirection_dot_self
#print axioms Gtz.exists_twoDirectionCover_of_repeated
#print axioms Gtz.splitSevenDesign_twoDirection_gapForm_negative
#print axioms Gtz.splitSevenDesign_repeatedDirection_fails_at_pairNormal
#print axioms Gtz.gapFormVelocity
#print axioms Gtz.gapForm_ray_expansion
#print axioms Gtz.rayAtomSum
#print axioms Gtz.rayAtomSum_gap_form
#print axioms Gtz.leverageOf_ray
#print axioms Gtz.parsevalTraceVelocity
#print axioms Gtz.traceIdentity_ray_expansion
#print axioms Gtz.tetraAtom_dotProduct_zero
#print axioms Gtz.tetraAtom_dotProduct_one
#print axioms Gtz.tetraAtom_dotProduct_two
#print axioms Gtz.tetraAtom_dotProduct_three
#print axioms Gtz.rainbowSevenMultiplier_marginal
#print axioms Gtz.splitSevenDesign_farkasIdentity
#print axioms Gtz.splitSevenDesign_velocityPairing_zero
#print axioms Gtz.splitSevenDesign_farkasIdentity_zero
#print axioms Gtz.rainbowSeven_exists_nonnegative_velocity
#print axioms Gtz.rainbowSeven_exists_positive_velocity
#print axioms Gtz.rainbowSevenTriple_rayGapForm_missedDirection
#print axioms Gtz.rainbowSevenTriple_ray_not_posSemidef_of_velocity_neg
#print axioms Gtz.stratumCriticalAtomVelocity
#print axioms Gtz.stratumCriticalWeightVelocity
#print axioms Gtz.stratumCriticalVelocity_mass_zero
#print axioms Gtz.stratumCriticalVelocity_parsevalTrace_zero
#print axioms Gtz.stratumCriticalVelocity_gapFormVelocity_zero
#print axioms Gtz.stratumCriticalVelocity_frozenQuadratic_eq_two
#print axioms Gtz.stratumCriticalRay_gap_eq
#print axioms Gtz.stratumCriticalRay_gap_det
#print axioms Gtz.stratumCriticalRay_not_posSemidef
#print axioms Gtz.projectionBlock_eq_congruence
#print axioms Gtz.det_projectionBlock_of_design
#print axioms Gtz.det_four_smul_one_sub_atomMatrix_tetraAtom
#print axioms Gtz.rainbowSevenPick
#print axioms Gtz.transpose_mul_selectedAtomRows_rainbow
#print axioms Gtz.splitSevenDesign_rainbowGram_det
#print axioms Gtz.rainbowSevenMultiplier_eq_det_projectionBlock
#print axioms Gtz.SplitSevenNeighbourhoodCovering
#print axioms Gtz.splitSevenNeighbourhoodCovering_of_gtzWeighted

-- Gtz.Ties.StratumSharpMaximum: the first-order certificate with a constant attached
#print axioms Gtz.rainbowSevenVelocityFamily
#print axioms Gtz.rainbowSevenMultiplier_floor
#print axioms Gtz.rainbowSeven_firingMargin_ge_multiplier_mul_descent
#print axioms Gtz.rainbowSeven_firingMargin_ge_floor_mul_bound

-- Gtz.Reduction.MixedCharPolynomial: the MSS volume-sampling route refuted at both residuals
#print axioms Gtz.mixedCharPoly
#print axioms Gtz.mixedCharPoly_coeff_rank
#print axioms Gtz.mixedCharPoly_natDegree_le
#print axioms Gtz.mixedCharPoly_monic
#print axioms Gtz.mixedCharPoly_natDegree
#print axioms Gtz.mixedCharPoly_ne_zero
#print axioms Gtz.mixedCharPoly_eval
#print axioms Gtz.shadowDeterminant_eq_weightProduct_mul_detSubsetSum
#print axioms Gtz.shadowDeterminant_eq_zero_of_atom_eq
#print axioms Gtz.mixedCharPoly_eval_zero
#print axioms Gtz.sum_weightProduct_mul_detSubsetSum_sq_nonneg
#print axioms Gtz.mixedCharPoly_eval_zero_nonpos_of_odd
#print axioms Gtz.mixedCharPoly_eval_zero_neg_of_odd
#print axioms Gtz.mixedCharPoly_eq_of_classes
#print axioms Gtz.charpoly_fin_three_expand
#print axioms Gtz.sum_tetraAtomMatrix_eq_fourSmulOne
#print axioms Gtz.charpoly_eq_oneFourFour_of_coefficients
#print axioms Gtz.charpoly_four_smul_sub_tetraAtom
#print axioms Gtz.subsetSum_splitSevenDesign_of_distinctDirections
#print axioms Gtz.mixedCharPoly_splitSevenDesign
#print axioms Gtz.mixedCharPoly_splitSevenDesign_eval_lt_zero
#print axioms Gtz.mixedCharPoly_splitSevenDesign_isRoot_one
#print axioms Gtz.DoesMixtureInterlaceAt
#print axioms Gtz.HasMixedRootAtLeastOne
#print axioms Gtz.gtzWeightedHeavy_of_mixtureInterlacesAt
#print axioms Gtz.doesMixtureInterlaceAtOne_of_gtzWeighted
#print axioms Gtz.detThreeInt
#print axioms Gtz.rootKillVector
#print axioms Gtz.rootKillVector_parseval
#print axioms Gtz.rootKillVector_lengthSq
#print axioms Gtz.rootKillScale
#print axioms Gtz.rootKillScale_mul_self
#print axioms Gtz.rootKillAtom
#print axioms Gtz.rootKillDesign
#print axioms Gtz.rootKillDesign_atom
#print axioms Gtz.rootKillDesign_weight
#print axioms Gtz.leverageOf_rootKillAtom
#print axioms Gtz.rootKillDesign_allHeavy
#print axioms Gtz.rootKillGram
#print axioms Gtz.rootKillShadowNumerator
#print axioms Gtz.rootKillGapNumerator
#print axioms Gtz.rootKillNumeratorSum_one
#print axioms Gtz.subsetSum_rootKillDesign_apply
#print axioms Gtz.det_subsetSum_rootKillDesign
#print axioms Gtz.shadowDeterminant_rootKillDesign
#print axioms Gtz.det_scalarOne_sub_subsetSum_rootKillDesign
#print axioms Gtz.mixedCharPoly_rootKillDesign_eval_one
#print axioms Gtz.rootKillShadowNumerator_zeroTwoFour
#print axioms Gtz.det_subsetSum_rootKillDesign_zeroTwoFour_ne_zero
#print axioms Gtz.mixedCharPoly_rootKillDesign_eval_zero_neg
#print axioms Gtz.exists_root_rootKillDesign_lt_one
#print axioms Gtz.not_mixedRootAtLeastOne_sixThree
#print axioms Gtz.rootKillWitnessVector
#print axioms Gtz.rootKillWitnessAtom
#print axioms Gtz.rootKillGram_zeroTwoFour
#print axioms Gtz.rootKillDesign_hasDominatingSubset
#print axioms Gtz.axisKillVector
#print axioms Gtz.axisKillVector_parseval
#print axioms Gtz.axisKillVector_lengthSq_ge
#print axioms Gtz.axisKillScale
#print axioms Gtz.axisKillScale_mul_self
#print axioms Gtz.axisKillAtom
#print axioms Gtz.axisKillDesign
#print axioms Gtz.axisKillDesign_atom
#print axioms Gtz.axisKillDesign_weight
#print axioms Gtz.leverageOf_axisKillAtom
#print axioms Gtz.axisKillDesign_allHeavy
#print axioms Gtz.axisKillGram
#print axioms Gtz.axisKillShadowNumerator
#print axioms Gtz.axisKillGapNumerator
#print axioms Gtz.axisKillNumeratorSum_one
#print axioms Gtz.subsetSum_axisKillDesign_apply
#print axioms Gtz.det_subsetSum_axisKillDesign
#print axioms Gtz.shadowDeterminant_axisKillDesign
#print axioms Gtz.det_scalarOne_sub_subsetSum_axisKillDesign
#print axioms Gtz.mixedCharPoly_axisKillDesign_eval_one
#print axioms Gtz.axisKillGram_fourFiveSix
#print axioms Gtz.axisKillShadowNumerator_fourFiveSix
#print axioms Gtz.det_subsetSum_axisKillDesign_fourFiveSix_ne_zero
#print axioms Gtz.mixedCharPoly_axisKillDesign_eval_zero_neg
#print axioms Gtz.exists_root_axisKillDesign_lt_one
#print axioms Gtz.not_mixedRootAtLeastOne_sevenThree
#print axioms Gtz.axisKillDesign_hasDominatingSubset
#print axioms Gtz.mixedCharPoly_splitSevenDesign_noRoot_below_one
#print axioms Gtz.not_mixedRootAtLeastOne_rankThreeResiduals
#print axioms Gtz.not_mixedRootAtLeastOne_rankThreeConjunction
#print axioms Gtz.exists_leastEigenvalue_ge_of_mixtureInterlacesAt

-- Gtz.Quantitative.GlobalMinimumRankThree: the exact rank-three ceiling,
-- the spike-stratum excision, and the corank-three correction
#print axioms Gtz.posDef_sub_one_of_posSemidef_sub_smul_one
#print axioms Gtz.not_exists_card_posSemidef_sub_smul_one_of_isTie
#print axioms Gtz.not_gtzWeightedFloor_of_isTie
#print axioms Gtz.gtzWeightedFloor_level_le_one_of_isTie
#print axioms Gtz.paddedTetraCorner
#print axioms Gtz.paddedTetraVertex
#print axioms Gtz.paddedTetraWeight
#print axioms Gtz.paddedTetraVertex_corner
#print axioms Gtz.paddedTetraVertex_copy
#print axioms Gtz.paddedTetraWeight_corner
#print axioms Gtz.paddedTetraWeight_copy
#print axioms Gtz.paddedTetraWeight_sum_one
#print axioms Gtz.tetraAtom_parseval
#print axioms Gtz.paddedTetraDesign
#print axioms Gtz.paddedTetraDesign_atom
#print axioms Gtz.exists_unusedPaddedVertex
#print axioms Gtz.paddedTetraDesign_no_strictDominator
#print axioms Gtz.paddedTetraCornerTriple
#print axioms Gtz.card_paddedTetraCornerTriple
#print axioms Gtz.subsetSum_paddedTetraCornerTriple
#print axioms Gtz.paddedTetraDesign_dominates
#print axioms Gtz.paddedTetraDesign_isTie
#print axioms Gtz.not_gtzWeightedFloor_rankThree_of_one_lt
#print axioms Gtz.gtzWeightedFloor_rankThree_level_le_one
#print axioms Gtz.gtzWeightedFloor_rankThree_bracket
#print axioms Gtz.not_gtzWeightedFloor_sevenThree_of_one_lt
#print axioms Gtz.exists_isTie_sevenThree
#print axioms Gtz.exists_atom_dotProduct_sq_ge_self
#print axioms Gtz.dominationGap_form_of_annihilated
#print axioms Gtz.dotProduct_sq_ge_self_of_dominates
#print axioms Gtz.posDef_subsetSum_univ_sub_one
#print axioms Gtz.subsetSum_univ_sub_one_eq_zero_of_single
#print axioms Gtz.gtzWeighted_corank_one_and_two
#print axioms Gtz.gtzWeightedAll_three_of_corank_three

-- Audit-coverage completion: declarations that were proved but never listed here.
-- Gtz.Certificates.FrameBridge
#print axioms Gtz.FrameBridge.biquadTight_symm
-- Gtz.Complex.ComplexPadding
#print axioms Gtz.topLeftBlock_add
#print axioms Gtz.topLeftBlock_sub
#print axioms Gtz.extendFlat_zero
#print axioms Gtz.extendFlat_one
#print axioms Gtz.extendFlat_two
#print axioms Gtz.topLeftBlock_one
#print axioms Gtz.quadForm_extendFlat
#print axioms Gtz.scaleAmpC_conj
#print axioms Gtz.scaleAmpC_sq
#print axioms Gtz.scaledSic_norm
#print axioms Gtz.scaledSic_overlap
#print axioms Gtz.scaledSingle_not_posSemidef
#print axioms Gtz.spikeAmpC_conj
#print axioms Gtz.spikeAmpC_sq
#print axioms Gtz.paddedAtom_spike_four
#print axioms Gtz.paddedAtom_spike_five
#print axioms Gtz.oldIndexOf_ne
#print axioms Gtz.paddedAtom_old
#print axioms Gtz.extendFlat_castSucc
#print axioms Gtz.topLeft_atom_extend
#print axioms Gtz.topLeft_atom_spike
#print axioms Gtz.complexAtom_zero_plane
#print axioms Gtz.topLeft_spike_four
#print axioms Gtz.topLeft_spike_five
#print axioms Gtz.scaledSingle_excess_not_psd
#print axioms Gtz.quadForm_basisTwo
-- Gtz.Complex.ComplexWitness
#print axioms Gtz.det_pair_excess_value
#print axioms Gtz.omegaRoot_star_mul
#print axioms Gtz.omegaRoot_sq
#print axioms Gtz.topAmpC_conj
#print axioms Gtz.sideAmpC_conj
#print axioms Gtz.waveAmpC_conj
#print axioms Gtz.topAmpC_sq
#print axioms Gtz.sideAmpC_sq
#print axioms Gtz.waveAmpC_sq
#print axioms Gtz.omegaRoot_conj_sum
#print axioms Gtz.omegaRoot_conj_eq
#print axioms Gtz.starDot_pair
#print axioms Gtz.sicAtom_zero
#print axioms Gtz.sicAtom_one
#print axioms Gtz.sicAtom_two
#print axioms Gtz.sicAtom_three
#print axioms Gtz.sicOverlap_zero_side
#print axioms Gtz.sicOv_one_two
#print axioms Gtz.sicOv_two_one
#print axioms Gtz.sicOv_one_three
#print axioms Gtz.sicOv_three_one
#print axioms Gtz.sicOv_two_three
#print axioms Gtz.sicOv_three_two
#print axioms Gtz.sicOverlap_side_zero
#print axioms Gtz.sicProd_one_two
#print axioms Gtz.sicProd_two_one
#print axioms Gtz.sicProd_one_three
#print axioms Gtz.sicProd_three_one
#print axioms Gtz.sicProd_two_three
#print axioms Gtz.sicProd_three_two
-- Gtz.Core.Sanity
#print axioms Gtz.Dominates
-- Gtz.Corner.IdempotentSplitting
#print axioms Gtz.sylvesterMap_add
#print axioms Gtz.sylvesterMap_sub
#print axioms Gtz.transpose_idempotent
#print axioms Gtz.idem_mul_compl
#print axioms Gtz.compl_mul_idem
#print axioms Gtz.complT_mul_idemT
-- Gtz.Design.CapSlack
#print axioms Gtz.sub_atomMatrix_eq_add_replicate
#print axioms Gtz.add_atomMatrix_eq_add_replicate
#print axioms Gtz.det_one_add_row_inv_col
-- Gtz.Design.CollaredCompact
#print axioms Gtz.atom_entry_sq_le_leverage
#print axioms Gtz.weight_le_one_of_sum_one
-- Gtz.Design.EqualityLocus
#print axioms Gtz.graphicDesign_posDef_iff
#print axioms Gtz.whitener_gram_mul_fullLaplacian
#print axioms Gtz.graphicDesign_atom
#print axioms Gtz.graphicAtom_eq_whitenedRow
#print axioms Gtz.leverageOf_graphicAtom_of_solves
#print axioms Gtz.cycleDropAt
#print axioms Gtz.groundedPotential_zero
#print axioms Gtz.cycleDropAt_zero
#print axioms Gtz.ne_zero_of_cycleDropAt_ne_zero
#print axioms Gtz.sum_cycleDropAt_eq_zero
#print axioms Gtz.dropPrefix
#print axioms Gtz.cycleVertex_val_self
#print axioms Gtz.dropPrefix_zero
#print axioms Gtz.dropPrefix_succ
#print axioms Gtz.dropPrefix_full
#print axioms Gtz.dropPrefix_last
#print axioms Gtz.potentialOfDrops
#print axioms Gtz.groundedPotential_potentialOfDrops
#print axioms Gtz.cycleDropAt_potentialOfDrops
#print axioms Gtz.bundleSize
#print axioms Gtz.sum_of_bundleValue
#print axioms Gtz.sum_bundleSize_cast
#print axioms Gtz.CycleBundling
#print axioms Gtz.CycleBundling.bundleSize_pos
#print axioms Gtz.CycleBundling.bundleSize_lt
#print axioms Gtz.CycleBundling.edgeCount_pos
#print axioms Gtz.CycleBundling.graphInducedWeight
#print axioms Gtz.CycleBundling.coBundleSize_pos
#print axioms Gtz.CycleBundling.bundleSize_pos_cast
#print axioms Gtz.CycleBundling.graphInducedWeight_pos
#print axioms Gtz.cycleBundlingWitness
#print axioms Gtz.cycleBundlingWitness_bundleSize
#print axioms Gtz.bundledCycleGraph
#print axioms Gtz.edgeVector_congr
#print axioms Gtz.bundledCycleGraph_edgeVector_congr
#print axioms Gtz.bundledCycleGraph_edgeVector_dotProduct
#print axioms Gtz.bundledCycle_reachable_from_zero
#print axioms Gtz.bundledCycle_isGroundConnected
#print axioms Gtz.bundledCycleData
#print axioms Gtz.bundledCycleDesign
#print axioms Gtz.bundledCycleDesign_weight
#print axioms Gtz.bundledCycle_atom_eq_of_sameBundle
#print axioms Gtz.bundledCycleData_selected_conductance
#print axioms Gtz.bundledCycle_selectedLaplacian_form
#print axioms Gtz.sum_of_bundleValue_univ
#print axioms Gtz.bundledCycle_fullLaplacian_bilinear
#print axioms Gtz.bundledCycle_fullLaplacian_form
#print axioms Gtz.bundledCycle_gap_eq_engelDeficiency
#print axioms Gtz.bundledCycle_gap_nonneg
#print axioms Gtz.bundledCycle_dominates
#print axioms Gtz.bundleSection
#print axioms Gtz.bundleSection_spec
#print axioms Gtz.bundleSection_injective
#print axioms Gtz.bundledCycleTree
#print axioms Gtz.bundledCycleTree_card
#print axioms Gtz.bundledCycleTree_injOn
#print axioms Gtz.bundledCycleTree_image
#print axioms Gtz.bundledCycleTree_dominates
#print axioms Gtz.bundledCycleTree_isSpanningTree
#print axioms Gtz.bundleTightDrops
#print axioms Gtz.sum_bundleTightDrops
#print axioms Gtz.erase_nonempty_of_rank
#print axioms Gtz.bundleTightPotential_ne_zero
#print axioms Gtz.bundledCycle_gap_eq_zero_at_tight
#print axioms Gtz.bundleSeparatingDrops
#print axioms Gtz.sum_bundleSeparatingDrops
#print axioms Gtz.bundleSeparatingDrops_eq_zero
#print axioms Gtz.bundledCycle_not_posDef_of_missesTwo
#print axioms Gtz.bundledCycle_not_posDef
#print axioms Gtz.bundledCycle_isTie
#print axioms Gtz.bundleCurrentScale
#print axioms Gtz.bundleCurrentDrops
#print axioms Gtz.sum_coBundleSize
#print axioms Gtz.sum_bundleCurrentDrops
#print axioms Gtz.bundleCurrent_solves
#print axioms Gtz.bundledCycle_leverage
#print axioms Gtz.bundledCycle_leverage_identity_at_arcTotal
#print axioms Gtz.bundledCycle_projection_diagonal
#print axioms Gtz.bundledCycle_rankTwo_clusterMagnitude
#print axioms Gtz.cycleBundlingWitness_isTie
#print axioms Gtz.cycleBundlingWitness_leverage
#print axioms Gtz.cycleBundlingWitness_rankTwo_clusterMagnitude
#print axioms Gtz.engelDeficiency_two
#print axioms Gtz.bundledCycle_gap_eq_squareQuotient
#print axioms Gtz.exists_arcPair_rankTwo
#print axioms Gtz.bundledCycle_rankTwo_gap_squareQuotient
#print axioms Gtz.bundlingSixThreeHeavy
#print axioms Gtz.bundlingSixThreePaired
#print axioms Gtz.bundlingSevenThreeHeavy
#print axioms Gtz.bundlingSevenThreeMixed
#print axioms Gtz.bundlingSevenThreePaired
#print axioms Gtz.bundlingSixThreeHeavy_isTie
#print axioms Gtz.bundlingSixThreePaired_isTie
#print axioms Gtz.bundlingSevenThreeHeavy_isTie
#print axioms Gtz.bundlingSevenThreeMixed_isTie
#print axioms Gtz.bundlingSevenThreePaired_isTie
#print axioms Gtz.bundlingSixThreeHeavy_leverage_tripleArc
#print axioms Gtz.bundlingSixThreeHeavy_leverage_singleArc
#print axioms Gtz.bundlingSixThreePaired_leverage_doubleArc
#print axioms Gtz.bundlingSevenThreeHeavy_leverage_quadArc
#print axioms Gtz.bundlingSevenThreeHeavy_leverage_singleArc
#print axioms Gtz.bundlingSevenThreeMixed_leverage_tripleArc
#print axioms Gtz.bundlingSevenThreeMixed_leverage_doubleArc
#print axioms Gtz.bundlingSevenThreePaired_leverage_doubleArc
#print axioms Gtz.bundlingSevenThreePaired_leverage_singleArc
#print axioms Gtz.bundlingNineTwoHeavy
#print axioms Gtz.bundlingNineTwoSpread
#print axioms Gtz.bundlingNineTwoHeavy_isTie
#print axioms Gtz.bundlingNineTwoSpread_isTie
#print axioms Gtz.bundlingNineTwoHeavy_cluster_sevenArc
#print axioms Gtz.bundlingNineTwoHeavy_cluster_singleArc
#print axioms Gtz.bundlingNineTwoSpread_cluster_quadArc
#print axioms Gtz.bundlingNineTwoSpread_cluster_tripleArc
#print axioms Gtz.bundlingNineTwoSpread_cluster_doubleArc
-- Gtz.Design.StressCertificate
#print axioms Gtz.tetraAtom_dot_self
#print axioms Gtz.tetraAtom_ne_zero
#print axioms Gtz.tetraAtom_dot_sq_of_ne
-- Gtz.LinAlg.PsdKit
#print axioms Gtz.sqrt_three_sq
#print axioms Gtz.dotProduct_self_nonneg
#print axioms Gtz.dotProduct_self_eq_sum_sq
#print axioms Gtz.eq_zero_of_dotProduct_self_eq_zero
#print axioms Gtz.dotProduct_sq_le_mul
-- Gtz.LinAlg.ResolventPerturbation
#print axioms Gtz.neg_le_of_sq_le_sq
-- Gtz.LinAlg.SchurRankOne
-- Gtz.Planar.CertificateFrame
#print axioms Gtz.planarDet_smul_left
-- Gtz.Planar.LawCounterexample
#print axioms Gtz.cexBudget_exceeds_law
-- Gtz.Planar.Pushoff
#print axioms Gtz.planarNorm_nonneg
#print axioms Gtz.planarNorm_sq
#print axioms Gtz.planarNorm_zero
#print axioms Gtz.abs_dotProduct_le_planarNorm_mul
#print axioms Gtz.planarDefect_zero
#print axioms Gtz.planarNorm_eq_of_sq
-- Gtz.Planar.SilenceDictionary
#print axioms Gtz.pair_excess_transpose
#print axioms Gtz.pair_excess_trace
-- Gtz.Planar.TightGraph
#print axioms Gtz.perpCoord_sq_of_unit
#print axioms Gtz.eq_of_coords_eq
-- Gtz.Quantitative.CollarFloor
#print axioms Gtz.collarDenominator_pos
#print axioms Gtz.sqrt_three_lt
-- Gtz.Quantitative.Interface
#print axioms Gtz.cornerDistanceRate_lower
#print axioms Gtz.cornerDistanceRate_upper
-- Gtz.Quantitative.PhaseFreeNoGo
#print axioms Gtz.phaseFreeOfDesign_excess_add_one
#print axioms Gtz.trineOverlap_symm
#print axioms Gtz.trineOverlap_self
#print axioms Gtz.trineOverlap_nonneg
#print axioms Gtz.trineOverlap_le_nine
#print axioms Gtz.trineTriangleTable_swap
#print axioms Gtz.trineTriangleTable_rotate
-- Gtz.Reduction.DescentLadder
#print axioms Gtz.one_sub_weight_mem
-- Gtz.Reduction.RatCertificateInstance
#print axioms Gtz.WeightedDesign
-- Gtz.Ties.CorankOneTieCriterion
#print axioms Gtz.exists_erase_eq_of_card_eq
#print axioms Gtz.card_erase_univ
#print axioms Gtz.forall_pivot_eq_one_of_one_le
#print axioms Gtz.parseval_reproduces
#print axioms Gtz.coParseval_reproduces
#print axioms Gtz.atomCombination_apply
#print axioms Gtz.atomCombination_surjective
#print axioms Gtz.parsevalRow_isDependency
#print axioms Gtz.resolventRow_isDependency
#print axioms Gtz.parsevalRow_symm
#print axioms Gtz.resolventRow_symm
#print axioms Gtz.resolventRow_diag_of_pivot_eq_one
#print axioms Gtz.parsevalRow_diag
-- Gtz.Ties.NonTetrahedralTie
#print axioms Gtz.sharpDesign_leverage_zero
#print axioms Gtz.sharpDesign_leverage_one
-- Gtz.Ties.SelectionObstruction
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroOneTwo
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroOneThree
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroOneFour
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroOneFive
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroTwoThree
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroTwoFour
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroTwoFive
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroThreeFour
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroThreeFive
#print axioms Gtz.heavyPivotDesign_not_dominates_ZeroFourFive
#print axioms Gtz.heavyPivotDesign_not_dominates_OneTwoThree
#print axioms Gtz.heavyPivotDesign_not_dominates_OneTwoFour
#print axioms Gtz.heavyPivotDesign_not_dominates_OneTwoFive
#print axioms Gtz.heavyPivotDesign_not_dominates_OneThreeFour
#print axioms Gtz.heavyPivotDesign_not_dominates_OneThreeFive
#print axioms Gtz.heavyPivotDesign_not_dominates_OneFourFive
#print axioms Gtz.heavyPivotDesign_not_dominates_TwoThreeFour
#print axioms Gtz.heavyPivotDesign_not_dominates_TwoThreeFive
#print axioms Gtz.heavyPivotDesign_not_dominates_TwoFourFive
#print axioms Gtz.doubleTransposition_zero
#print axioms Gtz.doubleTransposition_one
#print axioms Gtz.doubleTransposition_two
#print axioms Gtz.doubleTransposition_three
#print axioms Gtz.doubleTransposition_four
#print axioms Gtz.doubleTransposition_five
-- Gtz.Ties.SplitTetrahedronTie
#print axioms Gtz.splitTetraAtom_dot_sq_of_ne
#print axioms Gtz.exists_unusedDir
-- Gtz.Ties.TetrahedronCertifiedTie
#print axioms Gtz.exists_unusedVertex
#print axioms Gtz.tetraDesign_gapForm_zero_of_unusedVertex
-- Gtz.Complex.AtomSplitting
#print axioms Gtz.conjugatedSubsetRows_mulVec
#print axioms Gtz.not_posSemidef_atomSum_sub_of_repeatedAtom
#print axioms Gtz.splitAtomWeight
#print axioms Gtz.splitAtomWeight_atom_castSucc
#print axioms Gtz.splitAtomWeight_atom_last
#print axioms Gtz.exists_preimage_of_last_notMem
#print axioms Gtz.atomSum_map_castSucc
#print axioms Gtz.splitAtomWeight_valueAtMost
#print axioms Gtz.complexRankConstantAtMost_of_atSize
#print axioms Gtz.complexRankConstantAtMostAtSize_succ
#print axioms Gtz.complexRankConstantAtMostAtSize_of_le
#print axioms Gtz.complexRankConstantAtMostAtSize_nine_hesse
#print axioms Gtz.complexRankConstantAtMostAtSize_three_hesse
#print axioms Gtz.not_complexGtzWeighted_three_of_nine_le

-- Gtz.Quantitative.PositivstellensatzRankThree: the pivot-free covering chart,
-- the tetrahedral block family, and the Stengle multiplier-support floor.
-- All 53 public declarations of that file are probed here, definitions
-- included: 44 at [propext, Classical.choice, Quot.sound], 6 at
-- [propext, Quot.sound], and 3 axiom-free. That hasSharedBlockForEveryTrio_true
-- carries no Classical.choice is what makes the 35^3 search a genuine kernel
-- evaluation rather than a classical decidability instance.
#print axioms Gtz.discriminantTie_rotate
#print axioms Gtz.discriminantMinorSum_swapFirstTwo
#print axioms Gtz.discriminantMinorSum_rotate
#print axioms Gtz.discriminantTrace_pivotSum
#print axioms Gtz.dominates_triple_iff_symmetricLegs
#print axioms Gtz.SymmetricCovering
#print axioms Gtz.symmetricCovering_iff_discriminantCovering
#print axioms Gtz.symmetricCoveringSeven_iff_rank_three
#print axioms Gtz.notDominates_symmetricSignature
#print axioms Gtz.exists_increasing_symmetricLegs
#print axioms Gtz.symmetricCoveringSeven_iff_increasingTriples
#print axioms Gtz.blockFibre
#print axioms Gtz.blockFibre_card_pos
#print axioms Gtz.blockLabelWeight
#print axioms Gtz.blockLabelWeight_pos
#print axioms Gtz.blockFibre_card_mul_labelWeight
#print axioms Gtz.tetraBlockDesign
#print axioms Gtz.tetraBlockDesign_atom
#print axioms Gtz.tetraBlockDesign_leverage
#print axioms Gtz.tetraBlockDesign_allHeavy
#print axioms Gtz.tetraBlockDesign_heavyExcess
#print axioms Gtz.tetraBlockDesign_atomPairing_of_sameBlock
#print axioms Gtz.tetraBlockDesign_atomPairing_of_differentBlock
#print axioms Gtz.tetraBlockDesign_discriminantTie_eq
#print axioms Gtz.tetraBlockDesign_discriminantMinorSum_eq
#print axioms Gtz.tetraBlockDesign_discriminantTie_of_rainbow
#print axioms Gtz.tetraBlockDesign_discriminantMinorSum_of_rainbow
#print axioms Gtz.IsThinBlockMap
#print axioms Gtz.isThinBlockMapBool
#print axioms Gtz.isThinBlockMap_of_bool
#print axioms Gtz.tetraBlockDesign_discriminantTie_of_repeated
#print axioms Gtz.tetraBlockDesign_discriminantMinorSum_of_repeated
#print axioms Gtz.tetraBlockDesign_discriminantTie_nonpos
#print axioms Gtz.tetraBlockDesign_symmetricSignature
#print axioms Gtz.splitSevenDirection_surjective
#print axioms Gtz.blockLabelWeight_splitSeven
#print axioms Gtz.splitSevenDesign_eq_tetraBlockDesign
#print axioms Gtz.crowdedBlockMap
#print axioms Gtz.crowdedBlockMap_surjective
#print axioms Gtz.exists_tieNonneg_notDominates_seven
#print axioms Gtz.triplesSevenList
#print axioms Gtz.blockMapsSeven
#print axioms Gtz.blockMapsSeven_thin
#print axioms Gtz.isBlockSharedInTriple
#print axioms Gtz.blocksAgreeSomewhere_of_isBlockSharedInTriple
#print axioms Gtz.hasSharedBlockForEveryTrio
#print axioms Gtz.hasSharedBlockForEveryTrio_true
#print axioms Gtz.exists_blockMap_sharing
#print axioms Gtz.mem_triplesSevenList_of_mem_increasing
#print axioms Gtz.IsStengleTieSupportSeven
#print axioms Gtz.isStengleTieSupportSeven_increasing_iff
#print axioms Gtz.not_isStengleTieSupportSeven_of_card_le_three
#print axioms Gtz.four_le_card_of_isStengleTieSupportSeven

-- Gtz.Reduction.SplitTransfer: split/dual transfer, the definite congruence kit,
-- and the three-branch Covered+ shell (hypotheses named, nothing claims GtzWeighted 6 3)
#print axioms Gtz.DominatesAtLevel
#print axioms Gtz.dominatesAtLevel_one_iff_dominates
#print axioms Gtz.gtzWeightedFloor_iff_dominatesAtLevel
#print axioms Gtz.dominatesAtLevel_mono
#print axioms Gtz.dominatesAtLevel_iff_form
#print axioms Gtz.posDef_subsetSum_sub_smul_one_iff_form
#print axioms Gtz.splitAtoms
#print axioms Gtz.splitAtoms_eq_replicatedAtoms
#print axioms Gtz.splitWeights
#print axioms Gtz.splitWeights_last
#print axioms Gtz.splitWeights_castSucc_self
#print axioms Gtz.splitWeights_castSucc_of_ne
#print axioms Gtz.sum_splitWeights
#print axioms Gtz.sum_splitFrameOperator
#print axioms Gtz.splitDesign
#print axioms Gtz.splitDesign_atom_castSucc
#print axioms Gtz.splitDesign_atom_last
#print axioms Gtz.splitDesign_weight_last
#print axioms Gtz.splitDesign_weight_castSucc_self
#print axioms Gtz.splitDesign_weight_castSucc_of_ne
#print axioms Gtz.splitDesign_frameOperator_eq
#print axioms Gtz.replicatedDesign_eq_splitDesign_half
#print axioms Gtz.injOn_replicationMerge_of_not_both
#print axioms Gtz.subsetSum_image_replicationMerge
#print axioms Gtz.subsetSum_splitDesign_image_castSucc
#print axioms Gtz.card_image_castSucc_eq
#print axioms Gtz.splitDesign_subsetSum_trichotomy
#print axioms Gtz.not_dominates_splitDesign_of_both_copies
#print axioms Gtz.dominatesAtLevel_splitDesign_image_castSucc_iff
#print axioms Gtz.dominates_splitDesign_image_castSucc_iff
#print axioms Gtz.posDef_splitDesign_image_castSucc_iff
#print axioms Gtz.exists_dominating_splitDesign_iff
#print axioms Gtz.isTie_splitDesign_iff
#print axioms Gtz.posDef_one_sub_iff_strictContraction
#print axioms Gtz.strictContraction_flip
#print axioms Gtz.posDef_one_sub_transpose_comm
#print axioms Gtz.posDef_transpose_mul_sub_one_comm
#print axioms Gtz.LoewnerEquiv
#print axioms Gtz.LoewnerEquiv.refl
#print axioms Gtz.LoewnerEquiv.symm
#print axioms Gtz.LoewnerEquiv.trans
#print axioms Gtz.LoewnerEquiv.of_eq
#print axioms Gtz.loewnerEquiv_congr_right
#print axioms Gtz.loewnerEquiv_one_sub_transpose_comm
#print axioms Gtz.loewnerEquiv_transpose_mul_sub_one_comm
#print axioms Gtz.exists_naimarkDual_loewnerEquiv
#print axioms Gtz.weighted_naimark_duality_of_loewnerEquiv
#print axioms Gtz.isTie_naimarkDual
#print axioms Gtz.whitenedFamilyDesign
#print axioms Gtz.FrameOperatorIsPinched
#print axioms Gtz.framePinched_form_lower
#print axioms Gtz.framePinched_form_upper
#print axioms Gtz.posDef_of_framePinched
#print axioms Gtz.exists_whitener_of_framePinched
#print axioms Gtz.exists_whitenedDesign_of_framePinched
#print axioms Gtz.whitenedDesign_subsetSum_eq
#print axioms Gtz.rawForm_ge_of_whitenedForm_ge
#print axioms Gtz.whitenedForm_ge_of_rawForm_ge
#print axioms Gtz.mergeScaleSq
#print axioms Gtz.mergedParallelDesign
#print axioms Gtz.mergedParallelDesign_atom_kept
#print axioms Gtz.mergedParallelDesign_atom_of_ne
#print axioms Gtz.exists_longerParallelLabel
#print axioms Gtz.exists_dominating_of_mergedParallel_dominates
#print axioms Gtz.dominating_of_parallel_pair
#print axioms Gtz.posDef_one_sub_smul_atomMatrix_of_share_lt_one
#print axioms Gtz.subsetSum_deflatedDesign
#print axioms Gtz.dominates_image_of_deflated_dominatesAtLevel
#print axioms Gtz.exists_dominating_of_dust_atom
#print axioms Gtz.exists_dominating_of_dust_atom_of_deflatedLevel
#print axioms Gtz.dustBudget_forces_leverage_le_one
#print axioms Gtz.dustDropCertificate_of_floor_collapses_to_lightAtom
#print axioms Gtz.atomShare_graphicDesign_of_solves
#print axioms Gtz.HasParallelPair
#print axioms Gtz.exists_edgeVector_parallel_of_graphicAtom_parallel
#print axioms Gtz.diamondEdgeVector_eq
#print axioms Gtz.not_hasParallelPair_diamondDesign
#print axioms Gtz.HingeHoldsAtSize
#print axioms Gtz.not_hingeHoldsAtSize_five_three
#print axioms Gtz.HasDustAtom
#print axioms Gtz.IsSpreadAndFloored
#print axioms Gtz.DustDropCertificate
#print axioms Gtz.SpreadFloorCertificate
#print axioms Gtz.exists_weight_le_sizeInv
#print axioms Gtz.hasDustAtom_of_sizeInv_lt_floor
#print axioms Gtz.not_isSpreadAndFloored_of_sizeInv_lt_floor
#print axioms Gtz.spreadFloorCertificate_of_sizeInv_lt_floor
#print axioms Gtz.dustDropCertificate_iff_gtzWeighted_of_sizeInv_lt_floor
#print axioms Gtz.not_isTie_of_hinge_of_spread
#print axioms Gtz.dustDropCertificate_of_floor
#print axioms Gtz.dustDropCertificate_of_floorOnRegion
#print axioms Gtz.gtzWeighted_of_branches
#print axioms Gtz.gtzWeightedSix_of_branches
#print axioms Gtz.gtzWeightedSeven_of_branches
#print axioms Gtz.gtzWeightedAll_three_of_branches
#print axioms Gtz.NearParallelCertificate
#print axioms Gtz.FlooredSpreadDominationCertificate
#print axioms Gtz.hasDustAtom_iff_not_hasWeightFloor
#print axioms Gtz.not_isFlooredSpreadDesign_of_sizeInv_lt_floor
#print axioms Gtz.flooredSpreadDominationCertificate_of_sizeInv_lt_floor
#print axioms Gtz.gtzWeightedRankThree_of_compactBranches
#print axioms Gtz.flooredSpreadDominationCertificate_six_of_flooredSpreadCovering
#print axioms Gtz.gtzWeightedSix_of_compactBranches
#print axioms Gtz.gtzWeightedSeven_of_compactBranches
#print axioms Gtz.gtzWeightedAll_three_of_compactBranches

-- Gtz.Ties.StratumLocalCovering: the flat space at the split tetrahedron is
-- exactly nine-dimensional (stacked Jacobian rank 19), and the first-order dichotomy
#print axioms Gtz.parsevalMatrixVelocity
#print axioms Gtz.parsevalMatrixVelocity_apply
#print axioms Gtz.parsevalTraceVelocity_eq_trace
#print axioms Gtz.parsevalMatrix_ray_expansion
#print axioms Gtz.IsSplitSevenTraceTangent
#print axioms Gtz.IsSplitSevenTangent
#print axioms Gtz.IsSplitSevenFlat
#print axioms Gtz.IsSplitSevenTangent.parsevalTraceVelocity_eq_zero
#print axioms Gtz.IsSplitSevenTangent.isTraceTangent
#print axioms Gtz.rainbowSevenVelocityFamily_eq
#print axioms Gtz.rainbowSeven_multiplierSum_velocity_eq_zero
#print axioms Gtz.rainbowSeven_velocity_eq_zero_of_all_nonpos
#print axioms Gtz.rainbowSeven_supVelocity_nonneg
#print axioms Gtz.rainbowSeven_supVelocity_eq_zero_iff
#print axioms Gtz.rainbowSeven_supVelocity_eq_zero_iff_flat
#print axioms Gtz.rainbowSeven_exists_strictly_positive_velocity_of_not_stationary
#print axioms Gtz.rainbowSeven_exists_strictly_positive_velocity_of_not_flat
#print axioms Gtz.weightSplitWeightVelocity
#print axioms Gtz.bundleTotalAtomVelocity
#print axioms Gtz.bundleTotalWeightVelocity
#print axioms Gtz.gaugeRotationAtomVelocity
#print axioms Gtz.stratumFlatDirectionAtom
#print axioms Gtz.stratumFlatDirectionWeight
#print axioms Gtz.stratumFlatDirection_mass_zero
#print axioms Gtz.stratumFlatDirection_parsevalMatrixVelocity_zero
#print axioms Gtz.stratumFlatDirection_velocity_zero
#print axioms Gtz.stratumFlatDirection_isFlat
#print axioms Gtz.stratumFlatDirection_independent
#print axioms Gtz.rainbowSeven_bundleRigid_of_velocity_zero
#print axioms Gtz.stratumFlatCoefficient
#print axioms Gtz.stratumFlat_eq_combination
#print axioms Gtz.stratumFlat_coefficient_unique
#print axioms Gtz.parsevalMatrixVelocity_add
#print axioms Gtz.parsevalMatrixVelocity_smul
#print axioms Gtz.rainbowSevenVelocityFamily_add
#print axioms Gtz.rainbowSevenVelocityFamily_smul
#print axioms Gtz.stratumStackedJacobian
#print axioms Gtz.stratumStackedJacobian_apply
#print axioms Gtz.mem_ker_stratumStackedJacobian_iff
#print axioms Gtz.stratumFlatDirectionPair
#print axioms Gtz.stratumFlatDirectionPair_mem_ker
#print axioms Gtz.stratumFlatKernelFamily
#print axioms Gtz.stratumFlatKernelFamily_linearIndependent
#print axioms Gtz.stratumFlatKernelFamily_span
#print axioms Gtz.stratumFlatKernelBasis
#print axioms Gtz.stratumStackedJacobian_finrank_ker
#print axioms Gtz.stratumDirectionSpace_finrank
#print axioms Gtz.stratumStackedJacobian_finrank_range
#print axioms Gtz.splitSevenClassDesign
#print axioms Gtz.splitSevenClassDesign_weight
#print axioms Gtz.splitSevenClassDesign_isTie
#print axioms Gtz.splitSevenClassDesign_exists_dominatingTriple
#print axioms Gtz.splitSevenClassTotalWeight_eq_quarter
#print axioms Gtz.tieDefect_uniformQuarter
#print axioms Gtz.tieReflector_uniformQuarter
#print axioms Gtz.simplexTieAtom_uniformQuarter_eq_tetraAtom
#print axioms Gtz.splitSevenClassDesign_eq_splitSevenDesign
#print axioms Gtz.bundledCycle_exists_dominatingSubset
#print axioms Gtz.tetraAtom_abs_eq_one
#print axioms Gtz.tetraAtom_mul_self_eq_one
#print axioms Gtz.splitSevenDesign_atom_abs_eq_one
#print axioms Gtz.rainbowSevenTriple_gapEntry
#print axioms Gtz.rainbowSevenTriple_gapEntry_diagonal
#print axioms Gtz.rainbowSevenTriple_gapEntry_abs_offDiagonal
#print axioms Gtz.rainbowSeven_gapEntry_dist_le
#print axioms Gtz.rainbowSeven_dominates_of_tube_of_determinant
#print axioms Gtz.SplitSevenTubeDeterminantWitness
#print axioms Gtz.splitSevenNeighbourhoodCovering_of_determinantWitness
#print axioms Gtz.rainbowSeven_displacement_frozenForm

-- Gtz.Complex.HesseMarginAttained
#print axioms Gtz.complexAtom_smul_selfConj
#print axioms Gtz.hesseTriple_unitAtomSum
#print axioms Gtz.hesseTriple_scaledDecomposition
#print axioms Gtz.hesseBindingTriple_atomSum
#print axioms Gtz.hesseMarginC_isRoot
#print axioms Gtz.hesseMargin_firstPivot_pos
#print axioms Gtz.hesseMargin_secondPivot_pos
#print axioms Gtz.hesseBindingTriple_excess_posSemidef
#print axioms Gtz.hesseBindingTriple_card
#print axioms Gtz.hesse_bindingTriple_dominatesAtLevel
#print axioms Gtz.hesseDominatedShifts
#print axioms Gtz.hesseDominatedShifts_eq_Iic
#print axioms Gtz.hesseMargin_isGreatest
#print axioms Gtz.hesseMargin_isAttainedAndLeast
#print axioms Gtz.flattenedAtom
#print axioms Gtz.spikeAtom
#print axioms Gtz.spikePaddedAtom
#print axioms Gtz.spikePaddedWeight
#print axioms Gtz.spikePaddedWeight_pos
#print axioms Gtz.spikePaddedWeight_sum_one
#print axioms Gtz.spikePaddedDesign_parseval
#print axioms Gtz.spikePaddedDesign

-- Gtz.Complex.AttainmentRankThree
#print axioms Gtz.solveRowNormSq
#print axioms Gtz.solveRowNormSq_nonneg
#print axioms Gtz.solveRowNormSq_le_rank
#print axioms Gtz.normSq_solveCombination_le_rowNormSq
#print axioms Gtz.solveTraceWeight
#print axioms Gtz.solveTraceWeight_nonneg
#print axioms Gtz.solveTraceWeight_le_rank
#print axioms Gtz.exists_maximalVolume_solveTrace_covering
#print axioms Gtz.exists_subset_atomSum_sub_solveLevel_posSemidef
#print axioms Gtz.exchangeSelection
#print axioms Gtz.exchangeSelection_card
#print axioms Gtz.coveringAtom_notMem_of_undominated
#print axioms Gtz.exists_subset_atomSum_sub_capInverse_posSemidef
#print axioms Gtz.exchangeFloorRankThree
#print axioms Gtz.sqrt34_sq
#print axioms Gtz.sqrt34_nonneg
#print axioms Gtz.exchangeFloor_isRoot
#print axioms Gtz.sqrt34_window
#print axioms Gtz.exchangeFloor_window
#print axioms Gtz.exchangeFloor_lt_otherRoot
#print axioms Gtz.exchangeFloor_lt_hesseMargin
#print axioms Gtz.complexRankConstantAtLeast_three_third

-- Gtz.Complex.SpikePaddingLadder
#print axioms Gtz.flattenedAtom_castSucc
#print axioms Gtz.flattenedAtom_last
#print axioms Gtz.spikeAtom_castSucc
#print axioms Gtz.spikePaddedAtom_castSucc
#print axioms Gtz.spikePaddedAtom_last
#print axioms Gtz.spikePaddedDesign_atom
#print axioms Gtz.sumNormSq_snocZero
#print axioms Gtz.starDot_spikeAtom_snocZero
#print axioms Gtz.starDot_flattenedAtom_snocZero
#print axioms Gtz.normSq_starDot_flattenedAtom_snocZero
#print axioms Gtz.covering_of_posSemidef_atomSum_sub_smul_one
#print axioms Gtz.not_posSemidef_paddedAtomSum_sub_of_last_notMem
#print axioms Gtz.spikePaddedDesign_valueAtMost
#print axioms Gtz.complexRankConstantAtMostAtSize_padded
#print axioms Gtz.paddedBound_gt_of_pos
#print axioms Gtz.complexRankConstantAtMostAtSize_succ_of_gt
#print axioms Gtz.complexRankConstantAtMostAtSize_rank_add
#print axioms Gtz.paddedMargin_eq_scaledAlphaRankTwo
#print axioms Gtz.alphaRankTwo_nonneg
#print axioms Gtz.paddedMargin_nonneg
#print axioms Gtz.paddedMargin_lt_one
#print axioms Gtz.complexRankConstantAtMostAtSize_four_two
#print axioms Gtz.complexRankConstantAtMostAtSize_five_three
#print axioms Gtz.complexRankConstantAtMost_three_padded
#print axioms Gtz.complexRankConstantAtMostAtSize_three_padded
#print axioms Gtz.not_complexGtzWeighted_three_of_five_le
#print axioms Gtz.alphaRankTwo_lt_847_1000
#print axioms Gtz.complexRankConstantAtMostAtSize_six_four
#print axioms Gtz.not_complexGtzWeighted_four_of_six_le
#print axioms Gtz.complexRankConstantAtMostAtSize_ten_four_of_gt
#print axioms Gtz.complexRankConstantAtMostAtSize_three_le_rank
#print axioms Gtz.complexRankConstantAtMost_three_le_rank
#print axioms Gtz.not_complexGtzWeighted_of_two_le_rank
#print axioms Gtz.alphaRankTwo_pos
#print axioms Gtz.complexRankConstantAtMostAtSize_two_le_rank
#print axioms Gtz.complexRankConstantAtMostAtSize_five_three_of_gt
#print axioms Gtz.complexRankConstantAtMostAtSize_six_four_of_gt
#print axioms Gtz.alphaRankTwo_lt_seventeen_twentieths
#print axioms Gtz.ladderUndercuts_exactValueRankFourAtSix
#print axioms Gtz.ladderUndercuts_paddedMarginRankThree
#print axioms Gtz.not_complexGtzWeighted_of_rank_add_two_le_size
#print axioms Gtz.complexPaddingLadder
#print axioms Gtz.complexPaddingLadderAtMinimalSize

-- Gtz.Ties.TotalTieCorankOne
#print axioms Gtz.HasCommonOrthogonal
#print axioms Gtz.dotProduct_subsetSum_mulVec_of_finset
#print axioms Gtz.subsetSum_mulVec_eq_zero_of_commonOrthogonal
#print axioms Gtz.not_dominates_of_commonOrthogonal
#print axioms Gtz.subsetPick
#print axioms Gtz.subsetPick_mem
#print axioms Gtz.subsetPick_injective
#print axioms Gtz.subsetPick_surjOn
#print axioms Gtz.subsetRowMatrix
#print axioms Gtz.subsetRowMatrix_row
#print axioms Gtz.hasCommonOrthogonal_of_det_eq_zero
#print axioms Gtz.dominates_det_ne_zero
#print axioms Gtz.hasCommonOrthogonal_of_parallel
#print axioms Gtz.not_dominates_of_parallel
#print axioms Gtz.corankOne_isTie_dominates
#print axioms Gtz.corankOne_isTie_exactlyTied
#print axioms Gtz.corankOne_isTie_not_commonOrthogonal
#print axioms Gtz.corankOne_isTie_det_ne_zero
#print axioms Gtz.exists_erase_mem_pair
#print axioms Gtz.corankOne_isTie_not_parallel
#print axioms Gtz.tieAtFourThree_isTotal
#print axioms Gtz.tieAtFourThree_isUniformMatroid
#print axioms Gtz.tieAtFourThree_isPrimitive
#print axioms Gtz.tieAtFourThree_witness

-- Gtz.Design.PrimitiveTightClassification
#print axioms Gtz.tripleBracket
#print axioms Gtz.tripleBracket_eq
#print axioms Gtz.tripleBracket_swapLeft
#print axioms Gtz.tripleBracket_swapRight
#print axioms Gtz.tripleBracket_eq_zero_of_parallel
#print axioms Gtz.atomBracket
#print axioms Gtz.IsPrimitiveDesign
#print axioms Gtz.bracketNormal
#print axioms Gtz.tripleBracket_eq_bracketNormal_dotProduct
#print axioms Gtz.smul_dotProduct_self_eq_of_bracketNormal_eq_zero
#print axioms Gtz.eq_smul_of_bracketNormal_eq_zero
#print axioms Gtz.bracketNormal_ne_zero_of_not_parallel
#print axioms Gtz.atom_ne_zero_of_isPrimitiveDesign
#print axioms Gtz.bracketNormal_atom_ne_zero_of_isPrimitiveDesign
#print axioms Gtz.hasCommonOrthogonal_of_atomBracket_eq_zero
#print axioms Gtz.not_dominates_of_atomBracket_eq_zero
#print axioms Gtz.atomBracket_ne_zero_of_dominates
#print axioms Gtz.exists_basisTriple_of_isTie
#print axioms Gtz.trace_probe_mul_atomMatrix
#print axioms Gtz.not_parseval_of_traceNegativeProbe
#print axioms Gtz.no_design_of_traceNegativeProbe
#print axioms Gtz.smul_atomMatrix_mulVec
#print axioms Gtz.soleOffPlane_normal_eq_smul_pole
#print axioms Gtz.soleOffPlane_share_eq_one
#print axioms Gtz.soleOffPlane_leverage_one_lt
#print axioms Gtz.not_dominates_of_missing_pole
#print axioms Gtz.exists_sharedNormal_of_isPrimitiveDesign
#print axioms Gtz.fanoCoordinates_impossible
#print axioms Gtz.fanoBrackets_impossible
#print axioms Gtz.LinePattern
#print axioms Gtz.HasLinePattern
#print axioms Gtz.StratumIsTieFree
#print axioms Gtz.PatternListIsComplete
#print axioms Gtz.hingeHoldsAtSize_of_stratumLedger
#print axioms Gtz.atomBracket_relabelDesign
#print axioms Gtz.card_map_relabelEmbedding
#print axioms Gtz.map_relabelSymm_then_relabel
#print axioms Gtz.isTie_relabelDesign_iff
#print axioms Gtz.hasLinePattern_relabelDesign_symm
#print axioms Gtz.stratumIsTieFree_comp_relabel
#print axioms Gtz.PatternListIsCompleteUpToRelabel
#print axioms Gtz.hingeHoldsAtSize_of_relabelLedger
#print axioms Gtz.fanoLinePattern
#print axioms Gtz.not_hasLinePattern_fano
#print axioms Gtz.stratumIsTieFree_fano
#print axioms Gtz.tieAtFourThree_atomBracket_ne_zero
#print axioms Gtz.stratumIsTieFree_fourThree_of_line
#print axioms Gtz.tetraDesign_atomBracket_ne_zero
#print axioms Gtz.tetraDesign_hasUniformLinePattern
#print axioms Gtz.not_stratumIsTieFree_fourThree_uniform
#print axioms Gtz.parallelPairAtom
#print axioms Gtz.parallelPairDesign
#print axioms Gtz.parallelPairLinePattern
#print axioms Gtz.parallelPairDesign_hasLinePattern
#print axioms Gtz.parallelPairStratum_isNonempty_and_tieFree

-- Gtz.Quantitative.SpreadCertificateSixThree: the floored-spread hypothesis,
-- its chart-matrix bridge, and the boundaries where it is vacuous
#print axioms Gtz.HasLegMarginAtLeast
#print axioms Gtz.hasLegMarginAtLeast_weaken
#print axioms Gtz.SpreadFloorCertificateSixThree
#print axioms Gtz.spreadFloorCertificateSixThree_zero_iff_flooredSpreadCovering
#print axioms Gtz.flooredSpreadCovering_of_spreadFloorCertificateSixThree
#print axioms Gtz.spreadFloorCertificateSixThree_weakenMargin
#print axioms Gtz.spreadFloorCertificateSixThree_shrinkRegion
#print axioms Gtz.spreadFloorCertificateSixThree_of_symmetricCovering
#print axioms Gtz.leverageOf_le_of_hasWeightFloor
#print axioms Gtz.heavyExcess_le_of_hasWeightFloor
#print axioms Gtz.atomPairing_sq_le_leverage_product
#print axioms Gtz.atomPairing_sq_le_of_hasWeightFloor
#print axioms Gtz.weightTripleSum_le_one
#print axioms Gtz.weightProduct_le_cube_div_twentySeven
#print axioms Gtz.weightProduct_le_inv_twentySeven
#print axioms Gtz.weightTripleSum_le_of_hasWeightFloor
#print axioms Gtz.weightProduct_le_of_hasWeightFloor
#print axioms Gtz.floorCube_le_weightProduct
#print axioms Gtz.HasChartLegMarginAtLeast
#print axioms Gtz.hasLegMarginAtLeast_of_hasChartLegMarginAtLeast
#print axioms Gtz.hasLegMarginAtLeast_of_hasChartLegMarginAtLeast_floored
#print axioms Gtz.hasChartLegMarginAtLeast_of_hasLegMarginAtLeast
#print axioms Gtz.ChartSpreadFloorCertificateSixThree
#print axioms Gtz.spreadFloorCertificateSixThree_of_chartCertificate
#print axioms Gtz.chartCertificate_of_spreadFloorCertificateSixThree
#print axioms Gtz.chartFrame
#print axioms Gtz.chartMatrix
#print axioms Gtz.weightedAtomProduct_sum
#print axioms Gtz.chartFrame_transpose_mul_self
#print axioms Gtz.chartMatrix_eq_frame_mul_transpose
#print axioms Gtz.chartMatrix_isIdempotent
#print axioms Gtz.chartMatrix_isSymm
#print axioms Gtz.chartMatrix_trace
#print axioms Gtz.chartGapDiagonalOf
#print axioms Gtz.chartGapDeterminantOf
#print axioms Gtz.chartGapWeightedMinorSumOf
#print axioms Gtz.chartGapDeterminantOf_eq
#print axioms Gtz.chartGapWeightedMinorSumOf_eq
#print axioms Gtz.chartMatrix_diagonal_gt_weight_of_allHeavy
#print axioms Gtz.FreeChartCertificateSixThree
#print axioms Gtz.chartCertificateSixThree_of_freeChartCertificate
#print axioms Gtz.spreadFloorCertificateSixThree_of_freeChartCertificate
#print axioms Gtz.spreadFloorCertificateSixThree_of_sixth_lt_floor
#print axioms Gtz.spreadFloorCertificateSixThree_of_one_lt_spread
#print axioms Gtz.icosaDesign_discriminantMinorSum_eq
#print axioms Gtz.icosaDesign_discriminantTie_le
#print axioms Gtz.margin_le_of_spreadFloorCertificateSixThree

-- Gtz/Ties/CriticalTieMultiplier.lean -- the critical-multiplier quadric obstruction
#print axioms Gtz.IsCriticalMultiplierAt
#print axioms Gtz.trace_mul_subsetSum
#print axioms Gtz.trace_mul_gap_of_quadricLaw
#print axioms Gtz.not_isCriticalMultiplierAt
#print axioms Gtz.not_isCriticalMultiplierAt_rankThree

-- Gtz/Design/NearPencilStrictDomination.lean -- the near-pencil pole deflation and strict domination
#print axioms Gtz.exists_planeFrame_of_ne_zero
#print axioms Gtz.poleDeflation
#print axioms Gtz.poleDeflation_pos
#print axioms Gtz.poleDeflation_lt_one
#print axioms Gtz.poleDeflation_mul_half
#print axioms Gtz.nearPencilPlaneDesign
#print axioms Gtz.not_posSemidef_atomMatrix_sub_one
#print axioms Gtz.notMem_of_dominates_nearPencilPlane
#print axioms Gtz.posDef_estimate_of_nearPencilBlocks
#print axioms Gtz.exists_posDef_of_soleOffPlane
#print axioms Gtz.dominates_of_soleOffPlane
#print axioms Gtz.not_isTie_of_soleOffPlane
#print axioms Gtz.nearPencilLinePattern
#print axioms Gtz.bracketNormal_ne_zero_of_hasNearPencilLinePattern
#print axioms Gtz.sharedNormal_of_hasNearPencilLinePattern
#print axioms Gtz.stratumIsTieFree_nearPencil
#print axioms Gtz.stratumIsTieFree_nearPencil_sixThree
#print axioms Gtz.stratumIsTieFree_nearPencil_sevenThree
#print axioms Gtz.stratumIsTieFree_nearPencil_relabelled_sixThree
#print axioms Gtz.stratumIsTieFree_nearPencil_relabelled_sevenThree

-- Gtz/Design/NearPencilTransport.lean -- the rank-two transport closing q6m3 and q7m4
#print axioms Gtz.leverageOf_eq_dotProduct_self
#print axioms Gtz.atomMatrix_eq_zero
#print axioms Gtz.atomMatrix_mulVec_eq_smul
#print axioms Gtz.exists_orthonormalPlane_of_ne_zero
#print axioms Gtz.exists_ne_zero_orthogonal_planar
#print axioms Gtz.not_dominates_of_zero_atom_planar
#print axioms Gtz.rescaledPlanarDesign
#print axioms Gtz.exists_planar_pair_strictFloor
#print axioms Gtz.dotProduct_pole_eq_zero_of_solePole
#print axioms Gtz.exists_posDef_triple_of_solePole
#print axioms Gtz.not_isTie_of_solePole
#print axioms Gtz.tripleBracket_eq_zero_of_repeatMid
#print axioms Gtz.tripleBracket_eq_zero_of_repeatRight
#print axioms Gtz.stratumIsTieFree_of_solePoleOffLine
#print axioms Gtz.solePoleLinePattern
#print axioms Gtz.stratumIsTieFree_solePoleLinePattern
#print axioms Gtz.nearPencilSixAtom
#print axioms Gtz.nearPencilSixDesign
#print axioms Gtz.nearPencilSevenAtom
#print axioms Gtz.nearPencilSevenDesign
#print axioms Gtz.nearPencilSixDesign_hasLinePattern
#print axioms Gtz.nearPencilSevenDesign_hasLinePattern
#print axioms Gtz.nearPencilSixStratum_isNonempty_and_tieFree
#print axioms Gtz.nearPencilSevenStratum_isNonempty_and_tieFree

-- Gtz/Design/StratumEmptinessLedger.lean -- the per-stratum tie-emptiness ledger and the leverage floor
#print axioms Gtz.posDef_one_sub_atomMatrix_of_leverage_lt_one
#print axioms Gtz.exists_deflatedGapBound
#print axioms Gtz.posDef_on_orthogonal_of_deflatedGapBound
#print axioms Gtz.exists_posDef_of_lightAtom
#print axioms Gtz.not_isTie_of_lightAtom
#print axioms Gtz.leverage_one_le_of_isTie
#print axioms Gtz.leverage_one_le_of_isTie_sixThree
#print axioms Gtz.leverage_one_le_of_isTie_sevenThree
#print axioms Gtz.leverage_one_le_of_isTie_fourThree
#print axioms Gtz.leverage_one_le_of_isTie_fiveThree
#print axioms Gtz.allHeavy_or_exists_leverage_eq_one_of_isTie
#print axioms Gtz.allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree
#print axioms Gtz.allHeavy_or_exists_leverage_eq_one_of_isTie_sevenThree
#print axioms Gtz.share_bracket_of_isTie
#print axioms Gtz.sum_weighted_leverage_excess_of_isTie
#print axioms Gtz.design_mem_collaredSet_of_isTie_sixThree
#print axioms Gtz.StratumIsTieFreeAmongHeavy
#print axioms Gtz.stratumIsTieFreeAmongHeavy_of_stratumIsTieFree
#print axioms Gtz.stratumIsTieFree_of_amongHeavy
#print axioms Gtz.stratumIsTieFree_of_amongHeavy_sixThree
#print axioms Gtz.stratumIsTieFree_of_amongHeavy_sevenThree
#print axioms Gtz.StratumIsTieFreeAmongAllHeavy
#print axioms Gtz.StratumIsTieFreeAtUnitLeverage
#print axioms Gtz.stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage
#print axioms Gtz.stratumIsTieFree_of_allHeavy_and_unitLeverage_sixThree
#print axioms Gtz.stratumIsTieFree_of_allHeavy_and_unitLeverage_sevenThree
#print axioms Gtz.AgreesOnDistinctTriples
#print axioms Gtz.agreesOnDistinctTriples_refl
#print axioms Gtz.hasLinePattern_of_agreesOnDistinctTriples
#print axioms Gtz.stratumIsTieFree_of_agreesOnDistinctTriples
#print axioms Gtz.IsRelabelOf
#print axioms Gtz.isRelabelOf_refl
#print axioms Gtz.stratumIsTieFree_of_isRelabelOf
#print axioms Gtz.IsRelabelOfOnDistinctTriples
#print axioms Gtz.isRelabelOfOnDistinctTriples_of_isRelabelOf
#print axioms Gtz.stratumIsTieFree_of_isRelabelOfOnDistinctTriples
#print axioms Gtz.IsNearPencilClass
#print axioms Gtz.IsFanoClass
#print axioms Gtz.nearPencilLinePattern_comp_relabel
#print axioms Gtz.isNearPencilClass_iff_exists_pole
#print axioms Gtz.stratumIsTieFree_of_isNearPencilClass
#print axioms Gtz.stratumIsTieFree_of_isFanoClass
#print axioms Gtz.nearPencilLinePattern_self_of_ne
#print axioms Gtz.not_fanoLinePattern_diagonal
#print axioms Gtz.nearPencilStrictPattern
#print axioms Gtz.agreesOnDistinctTriples_nearPencilStrictPattern
#print axioms Gtz.isNearPencilClass_nearPencilStrictPattern
#print axioms Gtz.not_isRelabelOf_nearPencilStrictPattern
#print axioms Gtz.isPrimitiveDesign_iff_not_hasParallelPair
#print axioms Gtz.hingeHoldsAtSize_of_residualLedger
#print axioms Gtz.hingeHoldsAtSize_of_residualLedger_sevenThree
#print axioms Gtz.hingeHoldsAtSize_of_heavyResidualLedger_sixThree
#print axioms Gtz.hingeHoldsAtSize_of_heavyResidualLedger_sevenThree
#print axioms Gtz.hingeHoldsAtSize_of_allHeavyResidualLedger_sixThree
#print axioms Gtz.hingeHoldsAtSize_of_allHeavyResidualLedger_sevenThree
#print axioms Gtz.not_isNearPencilClass_lineFree
#print axioms Gtz.tetraDesign_forall_leverage_one_le
#print axioms Gtz.diamondDesign_forall_leverage_one_le
#print axioms Gtz.splitTetraDesign_forall_leverage_one_le
#print axioms Gtz.splitTetraDesign_allHeavy
#print axioms Gtz.splitTetraDesign_hasParallelPair
#print axioms Gtz.not_stratumIsTieFreeAmongHeavy_fourThree_lineFree
#print axioms Gtz.nearPencilLinePattern_eq_solePoleLinePattern
#print axioms Gtz.nearPencilSixDesign_hasNearPencilLinePattern
#print axioms Gtz.nearPencilSevenDesign_hasNearPencilLinePattern
#print axioms Gtz.nearPencilSixDesign_allHeavy
#print axioms Gtz.nearPencilSixEntry_isInhabitedHeavyAndTieFree

-- the field-generic ladder and the complex size axis
#print axioms Gtz.fieldAtom
#print axioms Gtz.fieldAtom_apply
#print axioms Gtz.fieldAtom_eq_atomMatrix
#print axioms Gtz.fieldAtom_posSemidef
#print axioms Gtz.fieldAtom_isHermitian
#print axioms Gtz.fieldLeverageOf
#print axioms Gtz.fieldLeverageOf_nonneg
#print axioms Gtz.fieldLeverageOf_eq_leverageOf
#print axioms Gtz.dotProduct_star_self_eq_fieldLeverage
#print axioms Gtz.trace_fieldAtom
#print axioms Gtz.FieldWeightedDesign
#print axioms Gtz.fieldSubsetSum
#print axioms Gtz.FieldDominates
#print axioms Gtz.FieldGtzWeighted
#print axioms Gtz.fieldWeight_le_one
#print axioms Gtz.fieldWeight_lt_one
#print axioms Gtz.sum_coWeight
#print axioms Gtz.sum_weight_mul_fieldLeverage
#print axioms Gtz.fieldAtom_eq_replicateCol_mul_conjTranspose
#print axioms Gtz.posSemidef_oneByOne_iff
#print axioms Gtz.posSemidef_sub_fieldAtom_iff
#print axioms Gtz.posSemidef_congr_conjTranspose
#print axioms Gtz.posDef_congr_conjTranspose
#print axioms Gtz.posSemidef_one_sub_conjTranspose_mul_comm
#print axioms Gtz.isUnit_of_posSemidef_conjTranspose_mul_sub_one
#print axioms Gtz.isUnit_nonsing_inv
#print axioms Gtz.isUnit_conjTranspose
#print axioms Gtz.conjTranspose_inv_mul_gap_mul_inv
#print axioms Gtz.posSemidef_conjTranspose_mul_sub_one_comm
#print axioms Gtz.coParsevalOperator
#print axioms Gtz.coParsevalOperator_eq_universalGap
#print axioms Gtz.coParsevalOperator_posSemidef
#print axioms Gtz.coParsevalOperator_posDef
#print axioms Gtz.fieldGtzWeighted_square
#print axioms Gtz.fieldWeightedDesign_zero_size_isEmpty
#print axioms Gtz.rank_le_size_of_fieldDesign
#print axioms Gtz.scaledFrame
#print axioms Gtz.conjTranspose_mul_scaledFrame
#print axioms Gtz.projectionChart
#print axioms Gtz.projectionChart_apply
#print axioms Gtz.projectionChart_conjTranspose
#print axioms Gtz.projectionChart_isHermitian
#print axioms Gtz.projectionChart_mul_self
#print axioms Gtz.projectionChart_mulVec_mulVec
#print axioms Gtz.projectionChart_diagonal
#print axioms Gtz.trace_projectionChart
#print axioms Gtz.ofRealDesign
#print axioms Gtz.scaledFrame_eq_scaledAtomRows
#print axioms Gtz.projectionChart_eq_projectionOfDesign
#print axioms Gtz.fieldSubsetSum_eq_subsetSum
#print axioms Gtz.fieldDominates_iff_dominates
#print axioms Gtz.selectedFieldRows
#print axioms Gtz.sqrtWeightDiagonalField
#print axioms Gtz.sqrtWeightDiagonalField_conjTranspose
#print axioms Gtz.isUnit_sqrtWeightDiagonalField
#print axioms Gtz.conjTranspose_mul_selectedFieldRows
#print axioms Gtz.chartBlock_sub_weightDiagonal
#print axioms Gtz.posSemidef_chartBlock_iff
#print axioms Gtz.fieldDominates_iff_posSemidef_chartBlock
#print axioms Gtz.fieldDominates_iff_posSemidef_chartBlock_finset
#print axioms Gtz.chartGap
#print axioms Gtz.chartGap_submatrix
#print axioms Gtz.chartGap_eq_projectionBlockGap
#print axioms Gtz.chartGapRayleigh
#print axioms Gtz.re_dotProduct_weightDiagonal_mulVec
#print axioms Gtz.re_dotProduct_projectionChart_mulVec_of_fixed
#print axioms Gtz.chartGapRayleigh_eq_of_fixed
#print axioms Gtz.chartGapRayleigh_pos_of_fixed
#print axioms Gtz.chartGapRayleigh_eq_of_killed
#print axioms Gtz.chartGapRayleigh_neg_of_killed
#print axioms Gtz.degenerateSingletonDesign
#print axioms Gtz.degenerateSingleton_chartGap_eq_zero
#print axioms Gtz.degenerateSingleton_chartGapRayleigh_eq_zero
#print axioms Gtz.no_posSemidef_principal_of_diag_neg
#print axioms Gtz.inertiaNoGoMatrix
#print axioms Gtz.inertiaNoGoMatrix_isHermitian
#print axioms Gtz.inertiaNoGoMatrix_det
#print axioms Gtz.inertiaNoGoMatrix_det_neg
#print axioms Gtz.inertiaNoGoMatrix_positive_direction
#print axioms Gtz.inertiaNoGoMatrix_negative_direction
#print axioms Gtz.inertiaNoGoMatrix_diag_neg
#print axioms Gtz.inertiaNoGoMatrix_no_posSemidef_principal
#print axioms Gtz.inertiaNoGoMatrixThree
#print axioms Gtz.inertiaNoGoMatrixThree_isHermitian
#print axioms Gtz.inertiaNoGoMatrixThree_det
#print axioms Gtz.inertiaNoGoMatrixThree_det_neg
#print axioms Gtz.inertiaNoGoMatrixThree_diag_neg
#print axioms Gtz.inertiaNoGoMatrixThree_no_posSemidef_principal
#print axioms Gtz.inertiaNoGoMatrixThree_positive_plane
#print axioms Gtz.inertiaNoGoMatrixThree_positive_plane_pos
#print axioms Gtz.exists_chartGap_diagonal_nonneg
#print axioms Gtz.exists_one_le_fieldLeverage
#print axioms Gtz.trace_mul_fieldAtom
#print axioms Gtz.coParsevalPivotScalar
#print axioms Gtz.sum_coWeight_mul_coParsevalPivotScalar
#print axioms Gtz.coParsevalPivotValue
#print axioms Gtz.coParsevalPivotScalar_nonneg
#print axioms Gtz.coParsevalPivotScalar_eq_ofReal
#print axioms Gtz.sum_coWeight_mul_coParsevalPivotValue
#print axioms Gtz.erasureGap_eq
#print axioms Gtz.fieldDominates_erase_iff_coParsevalPivot_le_one
#print axioms Gtz.exists_coParsevalPivotValue_le_one
#print axioms Gtz.fieldGtzWeighted_corank_one
#print axioms Gtz.fieldAtom_mulVec
#print axioms Gtz.not_posDef_of_mulVec_eq_zero
#print axioms Gtz.not_posDef_erasureGap_of_coParsevalPivot_eq_one
#print axioms Gtz.forall_coParsevalPivotValue_eq_one_of_forall_fieldDominates
#print axioms Gtz.forall_erasure_exactlyTied_of_forall_fieldDominates
#print axioms Gtz.jensenRatio
#print axioms Gtz.jensenRatio_mul_coWeight
#print axioms Gtz.sum_jensenRatio_mul_coWeight
#print axioms Gtz.sum_jensenRatio_sub_weighted_corank_one
#print axioms Gtz.exists_jensenRatio_ge_weightedAverage
#print axioms Gtz.sum_erase_jensenRatio_le_one
#print axioms Gtz.jensenRatio_eq_inv_rank_iff_leverageIdentity
#print axioms Gtz.jensenRatio_eq_inv_rank_of_forall_eq
#print axioms Gtz.kernelNormSq_eq_one_sub_weighted_leverage
#print axioms Gtz.jensenRatio_eq_kernelNormSq_div_coWeight
#print axioms Gtz.JensenErasureCriterion
#print axioms Gtz.fieldSubsetSum_erase_degenerateSingleton
#print axioms Gtz.sum_erase_jensenRatio_degenerateSingleton
#print axioms Gtz.not_jensenErasureCriterion_at_singleton
#print axioms Gtz.jensenSum_eq_kernel_schur_quantity
#print axioms Gtz.card_erase_pair
#print axioms Gtz.pairErasureGap_eq
#print axioms Gtz.FieldCorankTwoReducesToRankTwo
#print axioms Gtz.complexFieldGtzWeighted_square
#print axioms Gtz.realFieldGtzWeighted_square
#print axioms Gtz.complexFieldGtzWeighted_corank_one
#print axioms Gtz.realFieldGtzWeighted_corank_one
#print axioms Gtz.fieldAtom_eq_complexAtom
#print axioms Gtz.ofComplexDesign
#print axioms Gtz.toComplexDesign
#print axioms Gtz.fieldDominates_iff_complexDominates
#print axioms Gtz.fieldGtzWeighted_iff_complexGtzWeighted
#print axioms Gtz.toRealDesign
#print axioms Gtz.fieldGtzWeighted_iff_gtzWeighted
#print axioms Gtz.rank_le_size_of_complexDesign
#print axioms Gtz.complexGtzWeighted_square
#print axioms Gtz.complexGtzWeighted_corank_one
#print axioms Gtz.complexGtzWeighted_rank_le_one
#print axioms Gtz.complexGtzWeighted_iff_size_le_rank_add_one
#print axioms Gtz.complexGtzWeighted_iff
#print axioms Gtz.forall_jensenRatio_eq_inv_rank_iff_isTie
#print axioms Gtz.gtzWeighted_corank_one_viaTraceBudget
#print axioms Gtz.gtzWeighted_square_viaCoParseval
#print axioms Gtz.complexifyMatrix
#print axioms Gtz.complexifyMatrix_apply
#print axioms Gtz.complexifyMatrix_mul
#print axioms Gtz.complexifyMatrix_one
#print axioms Gtz.inv_complexifyMatrix
#print axioms Gtz.complexifyDesign
#print axioms Gtz.complexifyDesign_weight
#print axioms Gtz.coParsevalOperator_complexifyDesign
#print axioms Gtz.coParsevalPivotValue_complexifyDesign
#print axioms Gtz.fieldDominates_erase_complexifyDesign_iff
#print axioms Gtz.complexDominates_toComplexDesign_iff
#print axioms Gtz.exists_realDesign_exactlyTied
#print axioms Gtz.exists_complexDesign_exactlyTied
#print axioms Gtz.fieldCorankTwoReducesToRankTwo_real
#print axioms Gtz.fieldCorankTwoReducesToRankTwo_complex

-- Gtz/Quantitative/CriticalQuadric.lean -- A2 from stationarity data: the quadric law,
-- the coverage law, the sharp interior exclusion, and the non-vacuity witnesses
#print axioms Gtz.eq_of_forall_mulVec_eq
#print axioms Gtz.subsetSum_bilinearForm_eq_sum_mul
#print axioms Gtz.eq_of_forall_dotProduct_eq
#print axioms Gtz.tightDirection_bilinearForm_eq_smul
#print axioms Gtz.IsQuadricStationaryData
#print axioms Gtz.IsQuadricStationaryData.activeWeight_nonneg
#print axioms Gtz.IsQuadricStationaryData.activeWeight_sum_one
#print axioms Gtz.IsQuadricStationaryData.activeSubset_card
#print axioms Gtz.IsQuadricStationaryData.tightDir_unit
#print axioms Gtz.IsQuadricStationaryData.tightDir_isEigenvector
#print axioms Gtz.IsQuadricStationaryData.atomStationarity
#print axioms Gtz.IsQuadricStationaryData.weightStationarity
#print axioms Gtz.activeSet_nonempty_of_isQuadricStationaryData
#print axioms Gtz.exists_pos_activeWeight_of_isQuadricStationaryData
#print axioms Gtz.value_nonneg_of_isQuadricStationaryData
#print axioms Gtz.contractedStationarity_of_isQuadricStationaryData
#print axioms Gtz.quadricLaw_of_isQuadricStationaryData
#print axioms Gtz.coverageLaw_of_isQuadricStationaryData
#print axioms Gtz.exists_mem_activeSubset_of_isQuadricStationaryData
#print axioms Gtz.size_le_rank_mul_card_activeSet_of_isQuadricStationaryData
#print axioms Gtz.multiplierMatrix_eq_of_isQuadricStationaryData
#print axioms Gtz.posSemidef_multiplierMatrix_of_isQuadricStationaryData
#print axioms Gtz.trace_multiplierMatrix_of_isQuadricStationaryData
#print axioms Gtz.tightOverlap_sum_eq_one_of_isQuadricStationaryData
#print axioms Gtz.exists_active_rayleighForm_ge_rank_of_isQuadricStationaryData
#print axioms Gtz.exists_rayleighProbe_ge_rank_of_isQuadricStationaryData
#print axioms Gtz.value_eq_rank_of_singleActive
#print axioms Gtz.value_eq_rank_of_constant_activeSubset
#print axioms Gtz.size_eq_rank_of_singleActive
#print axioms Gtz.not_isQuadricStationaryData_of_singleActive_of_rank_lt_size
#print axioms Gtz.not_isQuadricStationaryData_of_singleActive_of_value_ne_rank
#print axioms Gtz.not_isQuadricStationaryData_of_singleActive_of_value_lt_one
#print axioms Gtz.isotropicQuadric_iff_leverage_eq_rank
#print axioms Gtz.leverage_eq_rank_of_isotropicMultiplier
#print axioms Gtz.isCriticalMultiplierAt_of_singleActive_of_value_one
#print axioms Gtz.degenerateQuadricStationaryAtom
#print axioms Gtz.degenerateQuadricStationaryWeight
#print axioms Gtz.degenerateQuadricStationaryDesign
#print axioms Gtz.degenerateQuadricStationaryTightDir
#print axioms Gtz.degenerateQuadricStationaryDesign_isQuadricStationaryData
#print axioms Gtz.exists_isQuadricStationaryData_singleActive_value_ne_rank
#print axioms Gtz.not_dominates_degenerateQuadricStationaryActiveSubset
#print axioms Gtz.posDef_gap_degenerateQuadricStationaryDesign
#print axioms Gtz.inv_sqrt_three_mul_self_eq_third
#print axioms Gtz.rainbowSevenUnitTightDir
#print axioms Gtz.rainbowSevenMultiplier_marginal_vector
#print axioms Gtz.splitSevenDesign_isQuadricStationaryData
#print axioms Gtz.exists_isQuadricStationaryData_value_ne_zero

-- Gtz/Design/VolumeSamplingAverage.lean + Gtz/Quantitative/ExpectedCharPolynomial.lean
-- the volume-sampling average dominates, and the expected characteristic polynomial
#print axioms Gtz.sq_weightedMean_le_weightedMean_sq
#print axioms Gtz.sq_weightedMean_le_weightedMean_sq_design
#print axioms Gtz.sum_weight_mul_atomOverlap_sq
#print axioms Gtz.atomOverlap_sq_le_leverage_mul_normSq
#print axioms Gtz.leverageWeightedAtomSum
#print axioms Gtz.leverageWeightedAtomSum_transpose
#print axioms Gtz.leverageWeightedAtomSum_isHermitian
#print axioms Gtz.leverageWeightedAtomSum_form
#print axioms Gtz.trace_leverageWeightedAtomSum
#print axioms Gtz.normSq_mul_leverageWeightedAtomSum_form_ge
#print axioms Gtz.normSq_le_leverageWeightedAtomSum_form
#print axioms Gtz.posSemidef_leverageWeightedAtomSum_sub_one
#print axioms Gtz.rank_le_sum_weight_mul_leverage_sq
#print axioms Gtz.lt_leverageWeightedAtomSum_form_of_transverseAtom
#print axioms Gtz.expectedSubsetSum
#print axioms Gtz.IsProjectionOnePointMarginal
#print axioms Gtz.expectedSubsetSum_eq_leverageWeightedAtomSum
#print axioms Gtz.sqrtWeightDiagonal_mul_self
#print axioms Gtz.sqrtWeightCongruence_gap_eq_sub_weightDiagonal
#print axioms Gtz.subsetSum_singleton_apply
#print axioms Gtz.dominates_singleton_iff_one_le_leverage
#print axioms Gtz.pos_of_weightedDesign
#print axioms Gtz.gtzWeighted_rank_one
#print axioms Gtz.expectedElementary
#print axioms Gtz.shadowDeterminant_empty
#print axioms Gtz.expectedElementary_zero
#print axioms Gtz.shadowDeterminant_singleton
#print axioms Gtz.expectedElementary_one
#print axioms Gtz.sq_rank_le_expectedElementary_one
#print axioms Gtz.sq_rank_le_sum_weight_mul_leverage_sq
#print axioms Gtz.trace_subsetSum
#print axioms Gtz.expectedSubsetTrace
#print axioms Gtz.coeff_mixedCharPoly_pred_rank
#print axioms Gtz.expectedSubsetTrace_eq_expectedElementary_one_of_marginal
#print axioms Gtz.coeff_mixedCharPoly_pred_rank_of_marginal
#print axioms Gtz.coeff_mixedCharPoly_two_le_neg_nine_of_marginal
#print axioms Gtz.nonneg_of_elementarySymmetric_nonneg
#print axioms Gtz.IsRealRootedCubic
#print axioms Gtz.eval_one_of_splitCubic
#print axioms Gtz.eval_one_derivative_of_splitCubic
#print axioms Gtz.eval_one_secondDerivative_of_splitCubic
#print axioms Gtz.isRoot_of_splitCubic_first
#print axioms Gtz.taylorSigns_of_forall_root_one_le
#print axioms Gtz.forall_root_one_le_of_taylorSigns
#print axioms Gtz.forall_root_one_le_iff_taylorSigns
#print axioms Gtz.IsTotalTieSupported
#print axioms Gtz.mixedCharPoly_eval_one_eq_zero_of_totalTieSupported
#print axioms Gtz.not_posDef_gap_of_shadowDeterminant_eq_zero
#print axioms Gtz.det_scalarOne_sub_subsetSum_neg_of_posDef
#print axioms Gtz.not_posDef_gap_of_totalTieSupported
#print axioms Gtz.subsetSum_tetraDesign_of_card_three
#print axioms Gtz.mixedCharPoly_tetraDesign
#print axioms Gtz.mixedCharPoly_tetraDesign_expanded
#print axioms Gtz.expectedElementary_one_tetraDesign
#print axioms Gtz.isRealRootedCubic_mixedCharPoly_tetraDesign
#print axioms Gtz.mixedCharPoly_tetraDesign_taylorAtOne
#print axioms Gtz.forall_root_tetraDesign_one_le
#print axioms Gtz.isTotalTieSupported_tetraDesign
#print axioms Gtz.tiltedMixture
#print axioms Gtz.tiltedMixture_one
#print axioms Gtz.EcpStar
#print axioms Gtz.exists_root_tiltedMixture_one_rootKillDesign_lt_one
#print axioms Gtz.not_uniformTilt_witnesses_ecpStar_sixThree
#print axioms Gtz.ChartPoint
#print axioms Gtz.chartPointGap
#print axioms Gtz.chartPointGap_transpose
#print axioms Gtz.ChartDominates
#print axioms Gtz.ChartGtz
#print axioms Gtz.chartPoint_apply_comm
#print axioms Gtz.chartPointColumn
#print axioms Gtz.chartPoint_mulVec_column
#print axioms Gtz.chartPointColumn_dotProduct_self
#print axioms Gtz.chartPointColumn_dotProduct
#print axioms Gtz.chartPoint_diag_nonneg
#print axioms Gtz.chartPointColumn_eq_zero_of_diag_eq_zero
#print axioms Gtz.matrix_mul_vecMulVec
#print axioms Gtz.vecMulVec_mul_matrix
#print axioms Gtz.dotProduct_vecMulVec_mulVec
#print axioms Gtz.deflatedChartMatrix
#print axioms Gtz.deflatedChartMatrix_transpose
#print axioms Gtz.rankOneDeflation_mul_self
#print axioms Gtz.deflatedChartMatrix_mul_self
#print axioms Gtz.deflatedChartMatrix_column_eq_zero
#print axioms Gtz.trace_deflatedChartMatrix
#print axioms Gtz.deflatePoint
#print axioms Gtz.dotProduct_chartPointGap_eq_deflated_add_pivot
#print axioms Gtz.sum_weight_succAbove
#print axioms Gtz.submatrix_mul_self_of_column_eq_zero
#print axioms Gtz.trace_submatrix_succAbove
#print axioms Gtz.dotProduct_mulVec_submatrix_succAbove
#print axioms Gtz.chartPointDelete
#print axioms Gtz.chartDominates_image_of_chartPointDelete
#print axioms Gtz.dotProduct_mulVec_add_spike
#print axioms Gtz.chartDominates_insert_of_deflate
#print axioms Gtz.chartDominates_singleton
#print axioms Gtz.exists_chartDominates_of_weight_eq_zero
#print axioms Gtz.weight_pos_of_forall_not_chartDominates
#print axioms Gtz.compressPoint
#print axioms Gtz.CompressionLiftClaim
#print axioms Gtz.compressionLiftClaim_of_weight_eq_zero
#print axioms Gtz.liftFailureChart
#print axioms Gtz.liftFailureChart_transpose
#print axioms Gtz.liftFailureChart_mul_self
#print axioms Gtz.trace_liftFailureChart
#print axioms Gtz.liftFailurePointAt
#print axioms Gtz.liftFailurePointAt_weight_pivot
#print axioms Gtz.liftFailurePointAt_pivot_pos
#print axioms Gtz.liftFailure_succAbove
#print axioms Gtz.liftFailurePointAt_compressedGap_eq_zero
#print axioms Gtz.not_chartDominates_liftFailurePointAt
#print axioms Gtz.liftFailurePoint
#print axioms Gtz.liftFailure_pivot_pos
#print axioms Gtz.liftFailure_weight_lt_one
#print axioms Gtz.liftFailure_isAllHeavy
#print axioms Gtz.liftFailure_compressedGap_eq_zero
#print axioms Gtz.not_chartDominates_liftFailure
#print axioms Gtz.not_compressionLiftClaim
#print axioms Gtz.EventualCompressionLiftClaim
#print axioms Gtz.not_eventualCompressionLiftClaim
#print axioms Gtz.selectionInjection
#print axioms Gtz.transpose_selectionInjection_mul
#print axioms Gtz.submatrix_mul_selectionInjection
#print axioms Gtz.mulVec_dotProduct_transpose
#print axioms Gtz.dotProduct_selectionInjection_mulVec
#print axioms Gtz.selectionInjection_mulVec_eq_zero_of_notMem
#print axioms Gtz.eq_selectionInjection_mulVec_of_support
#print axioms Gtz.chartDominates_iff_posSemidef_submatrix
#print axioms Gtz.chartPointOfDesign
#print axioms Gtz.chartPointGap_submatrix_chartPointOfDesign
#print axioms Gtz.dominates_iff_chartDominates
#print axioms Gtz.gtzWeighted_of_chartGtz
#print axioms Gtz.ChartGtzInterior
#print axioms Gtz.chartGtz_of_smaller_of_interior
#print axioms Gtz.chartGtz_size_zero
#print axioms Gtz.chartGtz_rank_zero
#print axioms Gtz.chartGtz_of_interior
#print axioms Gtz.gtzWeighted_of_interior
#print axioms Gtz.size_pos_of_chartPoint
#print axioms Gtz.relaxedChartPoint
#print axioms Gtz.dotProduct_gap_relaxedChartPoint
#print axioms Gtz.chartGtz_of_chartGtzInterior
#print axioms Gtz.gtzWeighted_of_chartGtzInterior
#print axioms Gtz.ChartPointHasDesign
#print axioms Gtz.chartGtzInterior_of_gtzWeighted
#print axioms Gtz.ChartPoint.chart
#print axioms Gtz.ChartPoint.weight
#print axioms Gtz.ChartPoint.isSymmetric
#print axioms Gtz.ChartPoint.isIdempotent
#print axioms Gtz.ChartPoint.hasTraceRank
#print axioms Gtz.ChartPoint.weight_nonneg
#print axioms Gtz.ChartPoint.weight_sum_one
#print axioms Gtz.multiplierForm_eq_of_isQuadricStationaryData
#print axioms Gtz.one_le_leverage_of_isQuadricStationaryData
#print axioms Gtz.weight_mul_value_le_one_of_isQuadricStationaryData
#print axioms Gtz.value_le_size_of_isQuadricStationaryData
#print axioms Gtz.rankOneScale_eq_value_of_isQuadricStationaryData
#print axioms Gtz.rankOneForm_eq
#print axioms Gtz.tightOverlap_probe_eq_of_rankOneMultiplier
#print axioms Gtz.exists_tightDir_eq_smul_of_rankOneMultiplier
#print axioms Gtz.value_eq_rank_of_rankOneMultiplier
#print axioms Gtz.not_isQuadricStationaryData_of_rankOneMultiplier_of_value_lt_one
#print axioms Gtz.weightedMultiplierImage_eq_of_isQuadricStationaryData
#print axioms Gtz.tightCombination_eq_zero_of_isQuadricStationaryData
#print axioms Gtz.HasIndependentTightSupport
#print axioms Gtz.weight_mul_value_eq_one_of_independentTightSupport
#print axioms Gtz.value_eq_size_of_independentTightSupport
#print axioms Gtz.not_isQuadricStationaryData_of_independentTightSupport_of_value_lt_one
#print axioms Gtz.not_hasIndependentTightSupport_of_value_lt_one
#print axioms Gtz.card_eq_rank_of_mem_activeSubsetImage
#print axioms Gtz.size_le_rank_mul_card_activeSubsetImage
#print axioms Gtz.two_le_card_activeSubsetImage_of_rank_lt_size
#print axioms Gtz.disjoint_union_of_card_activeSubsetImage_eq_two
#print axioms Gtz.weight_mul_value_eq_one_of_saturatedAtom
#print axioms Gtz.one_le_value_of_saturatedAtom
#print axioms Gtz.exists_activeSubset_not_mem_of_value_lt_one
#print axioms Gtz.activeWeight_blockMass_eq_weight_blockMass
#print axioms Gtz.three_le_card_activeSubsetImage_or_dependentPartition_sixThree
#print axioms Gtz.rootTwo
#print axioms Gtz.rootTwo_mul_self
#print axioms Gtz.rootTwo_pos
#print axioms Gtz.rootTwo_lt_two
#print axioms Gtz.one_lt_rootTwo
#print axioms Gtz.rootTwo_sq
#print axioms Gtz.rootTwo_cube
#print axioms Gtz.rootTwo_pow_four
#print axioms Gtz.inv_four_add_two_rootTwo
#print axioms Gtz.inv_four_sub_two_rootTwo
#print axioms Gtz.belowOneAtom
#print axioms Gtz.belowOneWeight
#print axioms Gtz.belowOneDesign
#print axioms Gtz.belowOneValue
#print axioms Gtz.belowOneRawTightDir
#print axioms Gtz.belowOneTightNormSq
#print axioms Gtz.belowOneSubset
#print axioms Gtz.belowOneTightNormSq_pos
#print axioms Gtz.belowOneRawTightDir_dot_self
#print axioms Gtz.belowOneRawTightDir_isEigenvector
#print axioms Gtz.belowOneTightDir
#print axioms Gtz.belowOneTightScale_mul_self
#print axioms Gtz.belowOneTightDir_unit
#print axioms Gtz.belowOneTightDir_isEigenvector
#print axioms Gtz.belowOneTightDir_pairing_smul
#print axioms Gtz.belowOneTightScaleSq
#print axioms Gtz.belowOneTightNormSq_inv_eq
#print axioms Gtz.belowOneMultiplier
#print axioms Gtz.belowOneMultiplierMatrix
#print axioms Gtz.belowOneAtomStationarity_term
#print axioms Gtz.belowOneQuadric
#print axioms Gtz.belowOneDesign_isQuadricStationaryData
#print axioms Gtz.belowOneValue_pos
#print axioms Gtz.belowOneValue_lt_one
#print axioms Gtz.subsetSum_belowOneDesign_orthogonalPair
#print axioms Gtz.dominates_belowOneDesign_orthogonalPair
#print axioms Gtz.exists_dominating_belowOneDesign
#print axioms Gtz.exists_isQuadricStationaryData_value_lt_one
#print axioms Gtz.not_forall_one_le_value_of_isQuadricStationaryData
#print axioms Gtz.IsArgmaxDominated
#print axioms Gtz.one_le_value_of_isArgmaxDominated
#print axioms Gtz.not_gtzWeighted_of_isArgmaxDominated_of_value_lt_one
#print axioms Gtz.not_isArgmaxDominated_belowOneDesign

-- Coverage sweep: every `theorem`/`lemma` enumerated from `Gtz/` that was
-- absent from the list above.  Gtz/Ties/DiamondTie.lean is deliberately
-- excluded: it is imported by nothing and duplicates
-- Gtz/Design/DiamondPrimitive.lean.

-- Gtz.Complex.SharpConstantLedger
#print axioms Gtz.trineDesign_atom

-- Gtz.Design.DiamondPrimitive
#print axioms Gtz.diamondGraph_isGroundConnected
#print axioms Gtz.diamondDrop_eq_grounded
#print axioms Gtz.diamondGap_form
#print axioms Gtz.diamondGap_form_indicator
#print axioms Gtz.diamondGap_not_posDef_of_direction
#print axioms Gtz.diamondWitness_ne_zero
#print axioms Gtz.diamondDesign_dominates_spine
#print axioms Gtz.diamondDesign_no_strictDominator
#print axioms Gtz.diamondDesign_isTie

-- Gtz.Design.NearPencilStrictDomination
#print axioms Gtz.nearPencilPlaneDesign_atom

-- Gtz.Design.NearPencilTransport
#print axioms Gtz.rescaledPlanarDesign_atom

-- Gtz.Quantitative.DecisionAtlasSevenThree
#print axioms Gtz.splitSevenDesign_atom

-- Gtz.Quantitative.FlooredSpreadRegion
#print axioms Gtz.hasWeightFloor_mono
#print axioms Gtz.leverageOf_nonneg
#print axioms Gtz.hasSpreadAtLeast_mono
#print axioms Gtz.isFlooredSpreadDesign_mono
#print axioms Gtz.pairDefect_comm
#print axioms Gtz.symmetricLegs_nonneg_of_dominantPairingTriangle
#print axioms Gtz.flooredSpreadCovering_of_symmetricCovering
#print axioms Gtz.flooredSpreadCovering_mono
#print axioms Gtz.flooredSpreadCovering_of_alwaysDominantPairingTriangle
#print axioms Gtz.icosaAtom_leverageOf
#print axioms Gtz.icosaDesign_hasSpreadAtLeast
#print axioms Gtz.icosaDesign_hasWeightFloor
#print axioms Gtz.icosaDesign_isFlooredSpreadDesign
#print axioms Gtz.splitTetraAtom_two_eq_three
#print axioms Gtz.splitTetraDesign_not_hasSpreadAtLeast
#print axioms Gtz.splitTetraDesign_balanced_hasWeightFloor

-- Gtz.Quantitative.PhaseFreeNoGo
#print axioms Gtz.phaseFreeOfDesign_weight
#print axioms Gtz.phaseFreeOfDesign_excess
#print axioms Gtz.phaseFreeOfDesign_pairing
#print axioms Gtz.phaseFreeOfDesign_triangle
#print axioms Gtz.trinePoint_triangle
#print axioms Gtz.trinePoint_weight
#print axioms Gtz.trinePoint_excess
#print axioms Gtz.trinePoint_pairing

-- Gtz.Quantitative.ProjectionChartLegs
#print axioms Gtz.chartEntry_comm
#print axioms Gtz.chartEntry_eq
#print axioms Gtz.chartEntry_self
#print axioms Gtz.chartEntry_sq
#print axioms Gtz.chartEntry_triangle
#print axioms Gtz.chartGapDiagonal_eq
#print axioms Gtz.chartGapMatrix_eq
#print axioms Gtz.chartTie_eq
#print axioms Gtz.chartMinorSum_eq
#print axioms Gtz.weightProduct_pos
#print axioms Gtz.chartTie_nonneg_iff
#print axioms Gtz.chartMinorSum_nonneg_iff
#print axioms Gtz.chartSpread_iff

-- Gtz.Quantitative.RealnessEngine
#print axioms Gtz.icosaDesign_atom

-- Gtz.Reduction.BranchTransferConstants
#print axioms Gtz.sum_atomMatrix_conj
#print axioms Gtz.conjugatedFamily_form_at_preimage
#print axioms Gtz.preimage_length_eq_defect_form
#print axioms Gtz.whitenedPullback_form_ge
#print axioms Gtz.mergeFrameDefect_eq
#print axioms Gtz.mergeFrameDefect_eq_zero_of_atoms_eq
#print axioms Gtz.mergeFrameDefect_form_le
#print axioms Gtz.exists_parallelAtoms_with_positive_mergeFrameDefect
#print axioms Gtz.merge_pullback_form_ge
#print axioms Gtz.sum_atomShare_eq_rank
#print axioms Gtz.exists_atomShare_le_rank_div_size
#print axioms Gtz.dropFrameDefect_form_le
#print axioms Gtz.drop_pullback_form_ge
#print axioms Gtz.dropWeight_sum_one
#print axioms Gtz.dropWhitened_parseval

-- Gtz.Reduction.BranchTwoRational
#print axioms Gtz.RatDesign.dot_cast

-- Gtz.Reduction.Compression
#print axioms Gtz.compressedDesign_atom

-- Gtz.Ties.NonTetrahedralTie
#print axioms Gtz.sharpDesign_atom

-- Gtz.Ties.SplitTetrahedronTie
#print axioms Gtz.splitTetraDesign_atom
#print axioms Gtz.splitTetraDesign_weight

-- Gtz.Ties.TetrahedronCertifiedTie
#print axioms Gtz.tetraDesign_atom

-- Gtz/Quantitative/ChartStationary.lean -- the CHART stationarity system as a
-- hypothesis bundle: the forced diagonal, the weight floor, the dual bound, strictness,
-- and the tetrahedron and octahedron witnesses
#print axioms Gtz.dotProduct_mulVec_eq_image_dotProduct_self
#print axioms Gtz.diagonal_eq_inv_size_iff_diagonal_constant
#print axioms Gtz.chartStationaryGap
#print axioms Gtz.chartStationaryGap_transpose
#print axioms Gtz.chartMultiplierAssembly
#print axioms Gtz.chartMultiplierAssembly_apply
#print axioms Gtz.chartMultiplierAssembly_diagonal
#print axioms Gtz.IsChartStationaryData
#print axioms Gtz.IsChartStationaryData.isSymmetric
#print axioms Gtz.IsChartStationaryData.isIdempotent
#print axioms Gtz.IsChartStationaryData.hasTraceRank
#print axioms Gtz.IsChartStationaryData.weight_pos
#print axioms Gtz.IsChartStationaryData.weight_sum_one
#print axioms Gtz.IsChartStationaryData.activeWeight_nonneg
#print axioms Gtz.IsChartStationaryData.activeWeight_sum_one
#print axioms Gtz.IsChartStationaryData.activeSubset_card
#print axioms Gtz.IsChartStationaryData.tightDir_unit
#print axioms Gtz.IsChartStationaryData.tightDir_support
#print axioms Gtz.IsChartStationaryData.tightDir_isTight
#print axioms Gtz.IsChartStationaryData.assembly_diagonal
#print axioms Gtz.IsChartStationaryData.assembly_commutes
#print axioms Gtz.size_pos_of_isChartStationaryData
#print axioms Gtz.size_cast_pos_of_isChartStationaryData
#print axioms Gtz.activeSet_nonempty_of_isChartStationaryData
#print axioms Gtz.exists_pos_activeWeight_of_isChartStationaryData
#print axioms Gtz.trace_chartMultiplierAssembly_of_isChartStationaryData
#print axioms Gtz.assembly_diagonal_iff_constant_of_isChartStationaryData
#print axioms Gtz.posSemidef_chartMultiplierAssembly_of_isChartStationaryData
#print axioms Gtz.transpose_chartMultiplierAssembly_of_isChartStationaryData
#print axioms Gtz.trace_chartStationaryGap_of_isChartStationaryData
#print axioms Gtz.exists_mem_activeSubset_of_isChartStationaryData
#print axioms Gtz.size_le_rank_mul_card_activeSet_of_isChartStationaryData
#print axioms Gtz.projection_mulVec_tightDir_of_mem
#print axioms Gtz.diagonal_projection_mul_atomMatrix_of_isChartStationaryData
#print axioms Gtz.diagonal_projection_mul_multiplier_of_isChartStationaryData
#print axioms Gtz.trace_projection_mul_multiplier_of_isChartStationaryData
#print axioms Gtz.projection_mul_multiplier_eq_sandwich_of_isChartStationaryData
#print axioms Gtz.posSemidef_projection_mul_multiplier_of_isChartStationaryData
#print axioms Gtz.weight_ge_neg_value_of_isChartStationaryData
#print axioms Gtz.neg_inv_size_le_value_of_isChartStationaryData
#print axioms Gtz.value_le_one_sub_weight_of_isChartStationaryData
#print axioms Gtz.value_lt_one_of_isChartStationaryData
#print axioms Gtz.IsChartArgmaxValue
#print axioms Gtz.weight_eq_inv_size_of_value_eq_neg_inv_size
#print axioms Gtz.not_isChartStationaryData_of_value_eq_neg_inv_size
#print axioms Gtz.neg_inv_size_lt_value_of_isChartStationaryData
#print axioms Gtz.chartTetraProjection
#print axioms Gtz.chartTetraWeight
#print axioms Gtz.chartTetraSubset
#print axioms Gtz.chartTetraMultiplierWeight
#print axioms Gtz.chartTetraSupport
#print axioms Gtz.chartTetraTightDir
#print axioms Gtz.chartTetraMultiplier
#print axioms Gtz.chartTetraProjection_transpose
#print axioms Gtz.chartTetraProjection_mul_self
#print axioms Gtz.chartTetraGap_apply
#print axioms Gtz.chartTetraSupport_dotProduct_self
#print axioms Gtz.chartTetraGap_mulVec_support
#print axioms Gtz.chartTetraMultiplierAssembly_eq
#print axioms Gtz.chartTetraProjection_isChartStationaryData
#print axioms Gtz.exists_isChartStationaryData_value_eq_zero
#print axioms Gtz.chartOctaAxis
#print axioms Gtz.chartOctaProjection
#print axioms Gtz.chartOctaWeight
#print axioms Gtz.chartOctaSubset
#print axioms Gtz.chartOctaMultiplierWeight
#print axioms Gtz.chartOctaTightDir
#print axioms Gtz.chartOctaProjection_transpose
#print axioms Gtz.chartOctaProjection_mul_self
#print axioms Gtz.chartOctaMultiplierAssembly_eq
#print axioms Gtz.chartOctaProjection_isChartStationaryData
#print axioms Gtz.exists_isChartStationaryData
#print axioms Gtz.not_forall_value_le_inv_size_of_isChartStationaryData

-- Gtz/Quantitative/ChartMultiplierSplit.lean -- the range/kernel multiplier split, its
-- converse, and the bridge to the design-side quadric law at chart value zero
#print axioms Gtz.diagonal_frameCongruence_eq_rowForm
#print axioms Gtz.IsChartFramePair
#print axioms Gtz.IsChartFramePair.rangeFrame_isIsometry
#print axioms Gtz.IsChartFramePair.rangeFrame_spansRange
#print axioms Gtz.IsChartFramePair.kernelFrame_isIsometry
#print axioms Gtz.IsChartFramePair.kernelFrame_spansKernel
#print axioms Gtz.projection_transpose_of_isChartFramePair
#print axioms Gtz.projection_mul_self_of_isChartFramePair
#print axioms Gtz.trace_projection_of_isChartFramePair
#print axioms Gtz.corank_cast_eq_of_isChartFramePair
#print axioms Gtz.transpose_rangeFrame_mul_kernelFrame_of_isChartFramePair
#print axioms Gtz.transpose_kernelFrame_mul_rangeFrame_of_isChartFramePair
#print axioms Gtz.projection_mul_rangeFrame_of_isChartFramePair
#print axioms Gtz.projection_mul_kernelFrame_of_isChartFramePair
#print axioms Gtz.chartRangeMultiplier
#print axioms Gtz.chartKernelMultiplier
#print axioms Gtz.posSemidef_chartRangeMultiplier
#print axioms Gtz.posSemidef_chartKernelMultiplier
#print axioms Gtz.rangeFrame_mul_chartRangeMultiplier_mul_transpose
#print axioms Gtz.kernelFrame_mul_chartKernelMultiplier_mul_transpose
#print axioms Gtz.complementProjection_mul_multiplier_eq_sandwich_of_isChartStationaryData
#print axioms Gtz.rangeForm_chartRangeMultiplier_of_isChartStationaryData
#print axioms Gtz.kernelForm_chartKernelMultiplier_of_isChartStationaryData
#print axioms Gtz.trace_chartRangeMultiplier_of_isChartStationaryData
#print axioms Gtz.trace_chartKernelMultiplier_of_isChartStationaryData
#print axioms Gtz.chartMultiplierAssembly_eq_frameSplit_of_isChartStationaryData
#print axioms Gtz.exists_chartMultiplierSplit_of_isChartStationaryData
#print axioms Gtz.chartAssembledMultiplier
#print axioms Gtz.IsChartStationaryAssembly
#print axioms Gtz.isChartStationaryAssembly_of_isChartStationaryData
#print axioms Gtz.diagonal_chartAssembledMultiplier_eq_inv_size
#print axioms Gtz.projection_mul_chartAssembledMultiplier_of_isChartFramePair
#print axioms Gtz.chartAssembledMultiplier_mul_projection_of_isChartFramePair
#print axioms Gtz.commutes_chartAssembledMultiplier_of_isChartFramePair
#print axioms Gtz.posSemidef_chartAssembledMultiplier
#print axioms Gtz.isChartStationaryAssembly_of_chartMultiplierSplit
#print axioms Gtz.chartQuadricMultiplier
#print axioms Gtz.scaledAtomRows_mul_transpose
#print axioms Gtz.quadricLaw_of_chartQuadricMultiplier_of_value_zero
#print axioms Gtz.trace_chartQuadricMultiplier_of_value_zero
#print axioms Gtz.posSemidef_chartQuadricMultiplier
#print axioms Gtz.quadricForm_chartQuadricMultiplier_eq_of_isQuadricStationaryData_value_one
#print axioms Gtz.trace_chartQuadricMultiplier_eq_of_isQuadricStationaryData_value_one
#print axioms Gtz.leverage_eq_rank_of_isotropic_chartQuadricMultiplier
#print axioms Gtz.trace_mul_gap_of_chartQuadricMultiplier
#print axioms Gtz.chartSplitTetraKernelFrame
#print axioms Gtz.sqrt_tetraDesign_weight
#print axioms Gtz.scaledAtomRows_tetraDesign_apply
#print axioms Gtz.projectionOfDesign_tetraDesign_eq
#print axioms Gtz.tetraDesign_weight_eq
#print axioms Gtz.chartSplitTetraIsChartFramePair
#print axioms Gtz.chartSplitTetraRangeMultiplier_eq
#print axioms Gtz.chartSplitTetraKernelMultiplier_eq
#print axioms Gtz.chartSplitTetraQuadricMultiplier_eq
#print axioms Gtz.exists_isChartStationaryData_value_zero_chartQuadricMultiplier_eq

-- Gtz/Quantitative/ChartHadamard.lean -- the unconditional chart identities: the trace,
-- the Hadamard row sums, the obstruction row and total sums, and the shifted minor sums
#print axioms Gtz.trace_sub_weightDiagonal_eq_rank_sub_one
#print axioms Gtz.trace_projectionOfDesign_sub_weightDiagonal
#print axioms Gtz.projection_apply_comm
#print axioms Gtz.sum_sq_projectionRow_eq_diagonal
#print axioms Gtz.sum_sq_projectionEntry_eq_trace
#print axioms Gtz.sum_sq_projectionOfDesign_row_eq_weight_mul_leverage
#print axioms Gtz.sum_sq_projectionOfDesign_entry_eq_rank
#print axioms Gtz.sq_projectionOfDesign_apply
#print axioms Gtz.dotProduct_atomMatrix_mulVec_self
#print axioms Gtz.sum_weight_mul_sq_atomPairing
#print axioms Gtz.sum_weight_mul_leverage_sub_one
#print axioms Gtz.chartObstruction
#print axioms Gtz.chartObstruction_comm
#print axioms Gtz.weight_mul_chartObstruction_eq
#print axioms Gtz.sum_weight_mul_chartObstruction
#print axioms Gtz.sum_weight_mul_weight_mul_chartObstruction
#print axioms Gtz.chartGapPairMinor
#print axioms Gtz.det_chartGapPair_eq
#print axioms Gtz.chartGapPairMinorSum
#print axioms Gtz.sum_offDiag_eq_sum_sub_diagonal
#print axioms Gtz.sum_powersetCard_three_offDiag
#print axioms Gtz.sum_offDiag_chartGapPairMinor
#print axioms Gtz.sum_chartGapPairMinorSum_powersetCard_three
#print axioms Gtz.sum_chartGapPairMinorSum_powersetCard_three_of_design
#print axioms Gtz.sum_chartGapPairMinorSum_powersetCard_three_pos_of_allHeavy
#print axioms Gtz.exists_pos_chartGapPairMinorSum_of_allHeavy
#print axioms Gtz.coeff_one_add_C_mul_X_pow
#print axioms Gtz.map_eval_one_add_X_smul
#print axioms Gtz.det_one_add_X_smul_shifted
#print axioms Gtz.sum_det_shiftedChartMinors_eq
#print axioms Gtz.sum_det_shiftedChartMinors_sixThree
#print axioms Gtz.size_pos_of_design
#print axioms Gtz.det_mul_transpose_sub_one_comm
#print axioms Gtz.det_shiftedChartBlock_eq_det_subsetSum_sub_one
#print axioms Gtz.sum_det_subsetSum_sub_one_uniform
#print axioms Gtz.sum_det_subsetSum_sub_one_sixThree

-- Gtz/Quantitative/ChartTwoBlock.lean -- the two-block branch: a complementary active
-- pair with distinct weights pins the chart value, with both witnesses
#print axioms Gtz.offDiagonal_eq_zero_of_commute_diagonal
#print axioms Gtz.IsChartTwoBlockFamily
#print axioms Gtz.isChartTwoBlockFamily_compl
#print axioms Gtz.HasDistinctWeightsOn
#print axioms Gtz.chartMultiplierAssembly_apply_comm
#print axioms Gtz.chartMultiplierAssembly_apply_eq_zero_of_crossBlock
#print axioms Gtz.projection_mul_multiplier_apply_of_split
#print axioms Gtz.projection_mul_multiplier_apply_of_sameBlock
#print axioms Gtz.multiplier_mul_weightDiagonal_comm
#print axioms Gtz.chartMultiplierAssembly_apply_eq_zero_of_ne_of_mem
#print axioms Gtz.projection_apply_of_mem_block
#print axioms Gtz.chartStationaryGap_apply_of_mem_block
#print axioms Gtz.chartMultiplierAssembly_eq_smul_one
#print axioms Gtz.projection_diagonal_eq_value_add_weight
#print axioms Gtz.value_eq_rank_sub_one_div_size_of_isChartTwoBlockFamily
#print axioms Gtz.rank_pos_of_isChartStationaryData
#print axioms Gtz.card_eq_rank_of_isChartTwoBlockFamily
#print axioms Gtz.size_eq_two_mul_rank_of_isChartTwoBlockFamily
#print axioms Gtz.value_eq_of_isChartTwoBlockFamily
#print axioms Gtz.zero_le_value_of_isChartTwoBlockFamily
#print axioms Gtz.chartTwoBlockSplitProjection
#print axioms Gtz.chartTwoBlockSplitWeight
#print axioms Gtz.chartTwoBlockSplitSubset
#print axioms Gtz.chartTwoBlockSplitMultiplierWeight
#print axioms Gtz.chartTwoBlockSplitTightDir
#print axioms Gtz.chartTwoBlockSplitProjection_transpose
#print axioms Gtz.chartTwoBlockSplitProjection_mul_self
#print axioms Gtz.chartTwoBlockSplitGap_apply
#print axioms Gtz.chartTwoBlockSplitMultiplierAssembly_eq
#print axioms Gtz.chartTwoBlockSplitProjection_isChartStationaryData
#print axioms Gtz.chartTwoBlockSplit_isChartTwoBlockFamily
#print axioms Gtz.chartTwoBlockSplitWeight_hasDistinctWeightsOn
#print axioms Gtz.chartTwoBlockSplitWeight_hasDistinctWeightsOn_compl
#print axioms Gtz.exists_isChartStationaryData_isChartTwoBlockFamily
#print axioms Gtz.chartTwoBlockSplit_isChartArgmaxValue
#print axioms Gtz.chartTwoBlockPairAxis
#print axioms Gtz.chartTwoBlockUniformProjection
#print axioms Gtz.chartTwoBlockUniformWeight
#print axioms Gtz.chartTwoBlockUniformSubset
#print axioms Gtz.chartTwoBlockUniformMultiplierWeight
#print axioms Gtz.chartTwoBlockUniformSupport
#print axioms Gtz.chartTwoBlockUniformTightDir
#print axioms Gtz.chartTwoBlockUniformMultiplier
#print axioms Gtz.chartTwoBlockUniformProjection_transpose
#print axioms Gtz.chartTwoBlockUniformProjection_mul_self
#print axioms Gtz.chartTwoBlockUniformGap_apply
#print axioms Gtz.chartTwoBlockUniformAxis_of_mem
#print axioms Gtz.chartTwoBlockUniformAxis_ne_of_notMem
#print axioms Gtz.chartTwoBlockUniformSupport_dotProduct_self
#print axioms Gtz.chartTwoBlockUniformGap_mulVec_support
#print axioms Gtz.chartTwoBlockUniformMultiplierAssembly_eq
#print axioms Gtz.chartTwoBlockUniformProjection_isChartStationaryData
#print axioms Gtz.chartTwoBlockUniform_isChartTwoBlockFamily
#print axioms Gtz.exists_isChartStationaryData_value_eq_neg_inv_size
#print axioms Gtz.not_forall_zero_le_value_of_isChartTwoBlockFamily

-- Gtz/Quantitative/ChartInstances.lean -- the chart stationarity bundle is inhabited: at a
-- certified tie, at non-uniform rational weights, and at the open cell (6,3)
#print axioms Gtz.tetraDesign_isChartStationaryData
#print axioms Gtz.exists_isTie_and_isChartStationaryData
#print axioms Gtz.chartCorankOneKernel
#print axioms Gtz.chartCorankOneProjection
#print axioms Gtz.chartCorankOneWeight
#print axioms Gtz.chartCorankOneMultiplierWeight
#print axioms Gtz.chartCorankOneReciprocal
#print axioms Gtz.chartCorankOneSupport
#print axioms Gtz.chartCorankOneNormSq
#print axioms Gtz.chartCorankOneTightDir
#print axioms Gtz.chartCorankOneMultiplier
#print axioms Gtz.chartCorankOneNormSq_pos
#print axioms Gtz.chartCorankOneProjection_transpose
#print axioms Gtz.chartCorankOneProjection_mul_self
#print axioms Gtz.chartCorankOneGap_apply
#print axioms Gtz.chartCorankOneSupport_dotProduct_self
#print axioms Gtz.chartCorankOneGap_mulVec_support
#print axioms Gtz.chartCorankOneMultiplierAssembly_eq
#print axioms Gtz.chartCorankOneProjection_isChartStationaryData
#print axioms Gtz.exists_isChartStationaryData_weight_ne
#print axioms Gtz.chartSplitSixDesign
#print axioms Gtz.chartSplitSixWeight
#print axioms Gtz.chartSplitSixRoot
#print axioms Gtz.chartSplitSixWeight_pos
#print axioms Gtz.chartSplitSixDesign_weight_eq
#print axioms Gtz.sqrt_chartSplitSixWeight
#print axioms Gtz.chartSplitSixPairing
#print axioms Gtz.chartSplitSixDesign_atom_dotProduct
#print axioms Gtz.chartSplitSixProjection
#print axioms Gtz.projectionOfDesign_chartSplitSixDesign_eq
#print axioms Gtz.chartSplitSixGap_apply
#print axioms Gtz.chartSplitSixSubset
#print axioms Gtz.chartSplitSixMultiplierWeight
#print axioms Gtz.chartSplitSixScale
#print axioms Gtz.chartSplitSixSupport
#print axioms Gtz.chartSplitSixNormSq
#print axioms Gtz.chartSplitSixTightDir
#print axioms Gtz.chartSplitSixNormSq_pos
#print axioms Gtz.chartSplitSixSupport_dotProduct_self
#print axioms Gtz.chartSplitSixScale_mul_root
#print axioms Gtz.chartSplitSixWeight_eq_root_mul_root
#print axioms Gtz.chartSplitSixGap_mul_scale
#print axioms Gtz.chartSplitSixPairingSum
#print axioms Gtz.chartSplitSixGap_mulVec_support
#print axioms Gtz.chartSplitSixMultiplier
#print axioms Gtz.chartSplitSixMultiplierAssembly_eq
#print axioms Gtz.chartSplitSixProjection_apply
#print axioms Gtz.chartSplitSixProjection_mul_multiplier_comm
#print axioms Gtz.chartSplitSixProjection_isChartStationaryData
#print axioms Gtz.chartSplitSixDesign_isChartStationaryData
#print axioms Gtz.chartSplitSixDesign_isTie
#print axioms Gtz.exists_isTie_and_isChartStationaryData_sixThree
#print axioms Gtz.chartSplitSixDesignMultiplierWeight
#print axioms Gtz.chartSplitSixDesignMultiplier_assembly_diagonal
#print axioms Gtz.not_isChartStationaryData_of_designSideMultiplier

-- Gtz/Quantitative/ChartStrongStationary.lean -- the chart stationarity system quantified
-- over EVERY tight selection: the tangent directions, the algebraic equivalence between
-- balance and the two stationarity equations, the Gordan descent lemma with its converse,
-- the reduction that makes the two systems coincide at simple multiplicity, and the
-- tetrahedron witness
#print axioms Gtz.gordan_alternative_finsetFamily
#print axioms Gtz.IsChartTangent
#print axioms Gtz.IsChartTangent.isSymmetric
#print axioms Gtz.IsChartTangent.rangeBlock_eq_zero
#print axioms Gtz.IsChartTangent.kernelBlock_eq_zero
#print axioms Gtz.IsChartTangent.weight_sum_zero
#print axioms Gtz.chartOffBlockDirection
#print axioms Gtz.chartCenteredWeight
#print axioms Gtz.sum_chartCenteredWeight_eq_zero
#print axioms Gtz.isChartTangent_weightDifference
#print axioms Gtz.isChartTangent_chartOffBlockDirection
#print axioms Gtz.chartOffBlockDirection_eq_self_of_isChartTangent
#print axioms Gtz.chartCenteredWeight_eq_self_of_sum_eq_zero
#print axioms Gtz.chartTangentSlope
#print axioms Gtz.chartTangentSlope_eq_sub
#print axioms Gtz.chartTangentSlope_smul
#print axioms Gtz.trace_atomMatrix_mul_of_symmetric
#print axioms Gtz.transpose_chartMultiplierAssembly
#print axioms Gtz.trace_chartMultiplierAssembly_eq_sum
#print axioms Gtz.trace_chartMultiplierAssembly_eq_one
#print axioms Gtz.sum_multiplier_chartTangentSlope_eq
#print axioms Gtz.trace_mul_eq_zero_of_commutes_of_isChartTangent
#print axioms Gtz.trace_mul_chartOffBlockDirection_eq
#print axioms Gtz.trace_mul_transpose_self_eq_sum_sq
#print axioms Gtz.commutes_of_offBlock_eq_zero
#print axioms Gtz.offBlock_chartMultiplierAssembly_apply
#print axioms Gtz.IsChartBalancedMultiplier
#print axioms Gtz.HasBalancedMultiplier
#print axioms Gtz.isChartBalancedMultiplier_iff
#print axioms Gtz.sum_multiplier_sq_eq_inv_size_of_isChartBalancedMultiplier
#print axioms Gtz.IsChartTightDirection
#print axioms Gtz.IsChartTightDirection.isUnit
#print axioms Gtz.IsChartTightDirection.hasSupport
#print axioms Gtz.IsChartTightDirection.isTight
#print axioms Gtz.IsChartStrongStationaryData
#print axioms Gtz.IsChartStrongStationaryData.isSymmetric
#print axioms Gtz.IsChartStrongStationaryData.isIdempotent
#print axioms Gtz.IsChartStrongStationaryData.hasTraceRank
#print axioms Gtz.IsChartStrongStationaryData.weight_pos
#print axioms Gtz.IsChartStrongStationaryData.weight_sum_one
#print axioms Gtz.IsChartStrongStationaryData.activeSubset_card
#print axioms Gtz.IsChartStrongStationaryData.exists_tightDir
#print axioms Gtz.IsChartStrongStationaryData.hasBalancedMultiplier_of_isChartTightSelection
#print axioms Gtz.size_pos_of_isChartStrongStationaryData
#print axioms Gtz.exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
#print axioms Gtz.exists_isChartStationaryData_of_isChartStrongStationaryData
#print axioms Gtz.chartTangentRiesz
#print axioms Gtz.dotProduct_mulVec_eq_sum_sum
#print axioms Gtz.dotProduct_chartOffBlockDirection_mulVec
#print axioms Gtz.sum_chartTangentRiesz_mul_eq_chartTangentSlope
#print axioms Gtz.exists_isChartTangent_forall_chartTangentSlope_neg
#print axioms Gtz.not_hasBalancedMultiplier_of_forall_chartTangentSlope_neg
#print axioms Gtz.hasBalancedMultiplier_iff_not_exists_descent
#print axioms Gtz.IsChartInactiveStrict
#print axioms Gtz.exists_eq_activeSubset_of_isChartInactiveStrict
#print axioms Gtz.isChartStrongStationaryData_of_isChartStationaryData_of_simpleTightBlocks
#print axioms Gtz.isChartStrongStationaryData_iff_of_simpleTightBlocks
#print axioms Gtz.exists_mem_activeSubset_of_isChartStrongStationaryData
#print axioms Gtz.neg_inv_size_le_value_of_isChartStrongStationaryData
#print axioms Gtz.chartTetraGap_mulVec_apply
#print axioms Gtz.isChartTightDirection_chartTetraTightDir
#print axioms Gtz.chartTetraTight_eq_smul_chartTetraTightDir
#print axioms Gtz.chartTetraProjection_isChartStrongStationaryData
#print axioms Gtz.exists_isChartStrongStationaryData

-- Gtz/Quantitative/ChartCovering.lean -- the covering form of that system: the tight
-- eigenspace as a subspace, the closed convex cone of each active block, the quantifier
-- exchange against the universal-selection condition, the halfspace case at simple
-- multiplicity, and the tetrahedron witness
#print axioms Gtz.ChartDirection
#print axioms Gtz.IsChartTightVector
#print axioms Gtz.IsChartTightVector.hasSupport
#print axioms Gtz.IsChartTightVector.isTight
#print axioms Gtz.isChartTightVector_of_isChartTightDirection
#print axioms Gtz.isChartTightVector_zero
#print axioms Gtz.isChartTightVector_add
#print axioms Gtz.isChartTightVector_smul
#print axioms Gtz.chartTightSubspace
#print axioms Gtz.mem_chartTightSubspace_iff
#print axioms Gtz.exists_pos_isChartTightDirection_smul_of_isChartTightVector
#print axioms Gtz.chartTangentSlope_eq_double_sum
#print axioms Gtz.chartTangentSlope_eq_subset_double_sum
#print axioms Gtz.chartStationaryGap_add
#print axioms Gtz.chartStationaryGap_smul
#print axioms Gtz.chartTangentSlope_add_direction
#print axioms Gtz.chartTangentSlope_smul_direction
#print axioms Gtz.chartTangentSlope_zero_vector
#print axioms Gtz.chartTangentSlope_zero_direction
#print axioms Gtz.chartTangentSlopeFunctional
#print axioms Gtz.chartTangentSlopeFunctional_apply
#print axioms Gtz.isChartTangent_zero
#print axioms Gtz.isChartTangent_add
#print axioms Gtz.isChartTangent_smul
#print axioms Gtz.chartTangentSubmodule
#print axioms Gtz.mem_chartTangentSubmodule_iff
#print axioms Gtz.isClosed_chartTangentSubmodule
#print axioms Gtz.chartTightCone
#print axioms Gtz.mem_chartTightCone_iff
#print axioms Gtz.chartTightCone_coe_subset_chartTangentSubmodule
#print axioms Gtz.pointed_chartTightCone
#print axioms Gtz.convex_chartTightCone
#print axioms Gtz.isClosed_chartTightCone
#print axioms Gtz.mem_chartTightCone_iff_forall_isChartTightDirection
#print axioms Gtz.IsChartTightCovering
#print axioms Gtz.isChartTightCovering_iff_iUnion_eq
#print axioms Gtz.isChartTightCovering_of_forall_isChartTightVector_eq_zero
#print axioms Gtz.forall_hasBalancedMultiplier_of_isChartTightCovering
#print axioms Gtz.isChartTightCovering_of_forall_hasBalancedMultiplier
#print axioms Gtz.isChartTightCovering_iff_forall_hasBalancedMultiplier
#print axioms Gtz.iUnion_chartTightCone_eq_iff_forall_hasBalancedMultiplier
#print axioms Gtz.isChartTightCovering_of_isChartStrongStationaryData
#print axioms Gtz.size_pos_of_weight_sum_eq_one
#print axioms Gtz.isChartStrongStationaryData_of_isChartTightCovering
#print axioms Gtz.isChartStrongStationaryData_iff_isChartTightCovering
#print axioms Gtz.exists_smul_of_isChartTightVector_of_simple
#print axioms Gtz.mem_chartTightCone_iff_of_simple
#print axioms Gtz.chartTightCone_coe_eq_inter_of_simple
#print axioms Gtz.isChartTightCovering_iff_hasBalancedMultiplier_of_simple
#print axioms Gtz.chartTetraProjection_isChartTightCovering
#print axioms Gtz.exists_isChartTightCovering

-- Gtz/Quantitative/RankTwoRealnessCount.lean -- the dimension count the rank-two
-- adjugate-pairing step consumes: the pairing identity at every dimension, with the
-- size of the moment operator visible as 2n where the shipped proof writes a literal 4,
-- the budget 2n <= k^2 and the sign it buys, the traceless self-adjoint dimension over
-- each field, the three instances -- equality at (R,2), deficit two at (C,2), deficit
-- exactly one at (R,3) -- and the complex-SIC Bloch moment, where the paired trace is
-- -128/27
#print axioms Gtz.adjugatePairingForm
#print axioms Gtz.trace_mul_vecMulVec
#print axioms Gtz.trace_adjugate_mul_adjugatePairingForm
#print axioms Gtz.trace_adjugate_mul_adjugatePairingForm_atDimensionTwo
#print axioms Gtz.IsWithinAdjugatePairingBudget
#print axioms Gtz.trace_adjugate_mul_adjugatePairingForm_nonneg_of_isWithinAdjugatePairingBudget
#print axioms Gtz.symmetricSubmodule
#print axioms Gtz.hermitianSubmodule
#print axioms Gtz.symmetricTracelessSubmodule
#print axioms Gtz.hermitianTracelessSubmodule
#print axioms Gtz.mem_symmetricSubmodule_iff
#print axioms Gtz.mem_hermitianSubmodule_iff
#print axioms Gtz.mem_symmetricTracelessSubmodule_iff
#print axioms Gtz.mem_hermitianTracelessSubmodule_iff
#print axioms Gtz.sub_smul_one_mem_symmetricTracelessSubmodule
#print axioms Gtz.ofReal_re_trace_eq_trace_of_hermitian
#print axioms Gtz.sub_smul_one_mem_hermitianTracelessSubmodule
#print axioms Gtz.atomMatrix_sub_smul_one_mem_symmetricTracelessSubmodule
#print axioms Gtz.conjTranspose_complexAtom
#print axioms Gtz.complexAtom_sub_smul_one_mem_hermitianTracelessSubmodule
#print axioms Gtz.upperTriangleIndex
#print axioms Gtz.two_mul_card_upperTriangleIndex
#print axioms Gtz.symmetrizeUpperTriangle
#print axioms Gtz.symmetrizeUpperTriangle_apply
#print axioms Gtz.injective_symmetrizeUpperTriangle
#print axioms Gtz.range_symmetrizeUpperTriangle_eq_symmetricSubmodule
#print axioms Gtz.two_mul_finrank_symmetricSubmodule
#print axioms Gtz.finrank_skewAdjoint_eq_finrank_selfAdjoint
#print axioms Gtz.finrank_hermitianSubmodule
#print axioms Gtz.sup_span_one_symmetricTracelessSubmodule
#print axioms Gtz.sup_span_one_hermitianTracelessSubmodule
#print axioms Gtz.two_mul_finrank_symmetricTracelessSubmodule_add_two
#print axioms Gtz.finrank_hermitianTracelessSubmodule_add_one
#print axioms Gtz.finrank_symmetricTracelessSubmodule
#print axioms Gtz.finrank_hermitianTracelessSubmodule
#print axioms Gtz.finrank_symmetricTracelessSubmodule_atRankTwo
#print axioms Gtz.finrank_hermitianTracelessSubmodule_atRankTwo
#print axioms Gtz.finrank_symmetricTracelessSubmodule_atRankThree
#print axioms Gtz.twiceFinrank_symmetricTracelessSubmodule_eq_sq_atRankTwo
#print axioms Gtz.twiceFinrank_hermitianTracelessSubmodule_eq_sq_add_two_atRankTwo
#print axioms Gtz.twiceFinrank_symmetricTracelessSubmodule_eq_sq_add_one_atRankThree
#print axioms Gtz.isWithinAdjugatePairingBudget_symmetricTracelessSubmodule_atRankTwo
#print axioms Gtz.not_isWithinAdjugatePairingBudget_hermitianTracelessSubmodule_atRankTwo
#print axioms Gtz.not_isWithinAdjugatePairingBudget_symmetricTracelessSubmodule_atRankThree
#print axioms Gtz.isWithinAdjugatePairingBudget_symmetricTracelessSubmodule_iff
#print axioms Gtz.isWithinAdjugatePairingBudget_hermitianTracelessSubmodule_iff
#print axioms Gtz.complexSicBlochMoment
#print axioms Gtz.det_complexSicBlochMoment
#print axioms Gtz.trace_complexSicBlochMoment
#print axioms Gtz.trace_adjugate_mul_adjugatePairingForm_complexSicBlochMoment
#print axioms Gtz.trace_adjugate_mul_adjugatePairingForm_complexSicBlochMoment_neg

-- Gtz/Quantitative/VolumeSelectionFailure.lean -- the maximal-volume rule does not
-- select a dominating subset: the two readings of the score and their identification
-- with the volume-sampling probability at selection size exactly the rank, the rank-two
-- pair kit, the general-weight (3,2) witness at corank one where the weighting is
-- innocent and the determinant is what fails, the uniform-weight (4,2) witness that
-- answers the standing-apart question of prob:effective NO, and the rule refuted in the
-- shape a rule has
#print axioms Gtz.volumeScore
#print axioms Gtz.weightScaledVolumeScore
#print axioms Gtz.IsStrictVolumeMaximiser
#print axioms Gtz.IsStrictWeightScaledVolumeMaximiser
#print axioms Gtz.weightScaledVolumeScore_eq_shadowDeterminant
#print axioms Gtz.weightScaledVolumeScore_eq_shadowDeterminant_ofCard
#print axioms Gtz.subsetSum_pair
#print axioms Gtz.volumeScore_pair
#print axioms Gtz.weightScaledVolumeScore_pair
#print axioms Gtz.not_dominates_pair_of_negativeDirection
#print axioms Gtz.dominates_pair_of_coercive
#print axioms Gtz.finset_card_two_cases_atSizeThree
#print axioms Gtz.finset_card_two_cases_atSizeFour
#print axioms Gtz.corankOneVolumeRuleAtom
#print axioms Gtz.corankOneVolumeRuleDesign
#print axioms Gtz.corankOneVolumeRuleDesign_volumeScore_zeroOne
#print axioms Gtz.corankOneVolumeRuleDesign_volumeScore_zeroTwo
#print axioms Gtz.corankOneVolumeRuleDesign_volumeScore_oneTwo
#print axioms Gtz.corankOneVolumeRuleDesign_isStrictVolumeMaximiser
#print axioms Gtz.corankOneVolumeRuleDesign_not_dominates_oneTwo
#print axioms Gtz.corankOneVolumeRuleDesign_dominates_zeroTwo
#print axioms Gtz.corankOneVolumeRuleDesign_weightScaledVolumeScore_zeroOne
#print axioms Gtz.corankOneVolumeRuleDesign_weightScaledVolumeScore_zeroTwo
#print axioms Gtz.corankOneVolumeRuleDesign_weightScaledVolumeScore_oneTwo
#print axioms Gtz.corankOneVolumeRuleDesign_isStrictWeightScaledVolumeMaximiser
#print axioms Gtz.corankOneVolumeRuleDesign_weightScaledVolumeMaximiser_dominates
#print axioms Gtz.uniformVolumeRuleAtom
#print axioms Gtz.uniformVolumeRuleDesign
#print axioms Gtz.uniformVolumeRuleDesign_weight_eq
#print axioms Gtz.uniformVolumeRuleDesign_volumeScore_zeroOne
#print axioms Gtz.uniformVolumeRuleDesign_volumeScore_zeroTwo
#print axioms Gtz.uniformVolumeRuleDesign_volumeScore_zeroThree
#print axioms Gtz.uniformVolumeRuleDesign_volumeScore_oneTwo
#print axioms Gtz.uniformVolumeRuleDesign_volumeScore_oneThree
#print axioms Gtz.uniformVolumeRuleDesign_volumeScore_twoThree
#print axioms Gtz.uniformVolumeRuleDesign_isStrictVolumeMaximiser
#print axioms Gtz.uniformVolumeRuleDesign_weightScaledVolumeScore_eq
#print axioms Gtz.uniformVolumeRuleDesign_isStrictWeightScaledVolumeMaximiser
#print axioms Gtz.uniformVolumeRuleDesign_not_dominates_zeroOne
#print axioms Gtz.uniformVolumeRuleDesign_dominates_zeroThree
#print axioms Gtz.uniformVolumeRuleDesign_dominates_oneTwo
#print axioms Gtz.volumeMaximiser_can_fail_to_dominate
#print axioms Gtz.volumeMaximiser_can_fail_to_dominate_atUniformWeights
#print axioms Gtz.shadowDeterminantMaximiser_can_fail_to_dominate_atUniformWeights
#print axioms Gtz.not_forall_strictVolumeMaximiser_dominates_atSizeThree
#print axioms Gtz.not_forall_strictVolumeMaximiser_dominates_atSizeFour

-- Gtz/Quantitative/ChartEmptinessCertificate.lean -- the exact certificate that empties the
-- two-block class on the floored negative window: the eliminant cubic and its rational
-- factorisation, the four-coefficient positive Handelman identity and the sharp margin
-- 1711/2000 it yields on [-3/20, 0], the root set {-1/6, 1/3, 5/6} and its coincidence with
-- three shipped chart landmarks, the theorem that interval positivity FAILS on the shipped
-- window [-1/6, 0] so the improved floor is load-bearing rather than cosmetic, and the
-- closure of the negative-value branch CONDITIONAL on the named hypothesis
-- EliminatesChartTwoBlockValue, which this development does not discharge
#print axioms Gtz.twoBlockEliminantCubic
#print axioms Gtz.twoBlockEliminantCubic_eq_prod
#print axioms Gtz.twoBlockEliminantCubic_eq_handelmanCombination
#print axioms Gtz.twoBlockEliminantCubic_nonneg_of_mem_flooredWindow
#print axioms Gtz.twoBlockEliminantCubic_sub_margin_eq_prod
#print axioms Gtz.handelmanMargin_le_twoBlockEliminantCubic
#print axioms Gtz.twoBlockEliminantCubic_pos_of_mem_flooredWindow
#print axioms Gtz.twoBlockEliminantCubic_ne_zero_of_flooredNegativeValue
#print axioms Gtz.not_exists_flooredNegativeValue_root_twoBlockEliminantCubic
#print axioms Gtz.twoBlockEliminantCubic_eq_zero_iff
#print axioms Gtz.twoBlockEliminantCubic_eq_zero_iff_of_negativeValue
#print axioms Gtz.twoBlockEliminantCubic_eq_zero_iff_chartLandmark
#print axioms Gtz.not_flooredWindow_neg_inv_six
#print axioms Gtz.not_forall_pos_twoBlockEliminantCubic_on_shippedWindow
#print axioms Gtz.not_hasDistinctWeightsOn_both_of_negativeValue_of_isChartTwoBlockFamily
#print axioms Gtz.EliminatesChartTwoBlockValue
#print axioms Gtz.zero_le_value_of_isChartTwoBlockFamily_of_eliminates
#print axioms Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_flooredNegativeValue

-- Gtz/Quantitative/ComplexRankThreeFloor.lean -- the rank-three floor 1/3 is sharp for the
-- MAXIMAL-VOLUME SELECTION RULE, over both fields: the two-parameter (4,3) family and its
-- Parseval, the twenty-four row determinants with the apex bound that makes the leading
-- triple the unique volume maximizer, the all-ones probe capping the level that triple
-- certifies at the diagonal scale squared, the parameters driving that scale to 1/3, and
-- the same obstruction coerced to C -- with the honesty guard that the family itself
-- SATISFIES GTZ, so only the selection rule is closed and alpha_3 is untouched
#print axioms Gtz.maximalVolumeSharpOffset
#print axioms Gtz.maximalVolumeSharpRow
#print axioms Gtz.sum_maximalVolumeSharpRow_lead
#print axioms Gtz.abs_det_maximalVolumeSharpTriple_le
#print axioms Gtz.abs_det_maximalVolumeSharpTriple_le_apex
#print axioms Gtz.det_maximalVolumeSharpTriple_lead
#print axioms Gtz.IsMaximalVolumeSharpParameter
#print axioms Gtz.IsMaximalVolumeSharpParameter.isAxisPositive
#print axioms Gtz.IsMaximalVolumeSharpParameter.rankInverse_lt_diagonalSq
#print axioms Gtz.maximalVolumeSharpApex
#print axioms Gtz.maximalVolumeSharpApex_nonneg
#print axioms Gtz.maximalVolumeSharpApex_sq
#print axioms Gtz.maximalVolumeSharpApex_lt_diagonal
#print axioms Gtz.maximalVolumeSharpAtom
#print axioms Gtz.maximalVolumeSharpWeight
#print axioms Gtz.maximalVolumeSharpDesign
#print axioms Gtz.maximalVolumeSharpDesign_atom
#print axioms Gtz.maximalVolumeSharpDesign_weight
#print axioms Gtz.leadingTriplePick
#print axioms Gtz.leadingTriplePick_injective
#print axioms Gtz.image_leadingTriplePick
#print axioms Gtz.selectedFrameRows_maximalVolumeSharp
#print axioms Gtz.det_selectedFrameRows_leadingTriplePick
#print axioms Gtz.isMaximalVolume_leadingTriplePick
#print axioms Gtz.det_selectedFrameRows_leadingTriplePick_ne_zero
#print axioms Gtz.abs_det_selectedFrameRows_lt_of_takes_apex
#print axioms Gtz.image_eq_leadingTriple_of_isMaximalVolume
#print axioms Gtz.sum_entries_subsetSum_maximalVolumeSharpDesign
#print axioms Gtz.dotProduct_subsetSum_maximalVolumeSharpDesign_ones
#print axioms Gtz.not_posSemidef_subsetSum_maximalVolumeSharpDesign_sub_smul_one
#print axioms Gtz.maximalVolumeSharpDesign_hasDominatingSubset
#print axioms Gtz.isMaximalVolumeSharpParameter_ofGap
#print axioms Gtz.exists_design_maximalVolumePick_not_posSemidef
#print axioms Gtz.exists_design_forall_maximalVolumePick_not_posSemidef
#print axioms Gtz.not_forall_maximalVolumePick_posSemidef_sub_smul_one
#print axioms Gtz.fieldSelectedAtomRows
#print axioms Gtz.fieldSelectedAtomRows_complexifyDesign
#print axioms Gtz.det_complexifyMatrix
#print axioms Gtz.fieldSubsetSum_complexifyDesign
#print axioms Gtz.complexMaximalVolumeSharpDesign
#print axioms Gtz.norm_det_fieldSelectedAtomRows_complexMaximalVolumeSharpDesign
#print axioms Gtz.isMaximalVolume_leadingTriplePick_complex
#print axioms Gtz.not_posSemidef_fieldSubsetSum_complexMaximalVolumeSharpDesign_sub_smul_one
#print axioms Gtz.exists_design_forall_maximalVolumePick_not_posSemidef_complex
#print axioms Gtz.not_forall_maximalVolumePick_posSemidef_sub_smul_one_complex

-- Gtz/Quantitative/ExtremalBasisActivity.lean -- which subsets are active at an extremal
-- design: the parallel splitting of an ARBITRARY base and its activity law -- a subset
-- dominates upstairs exactly when it is class-injective and its image dominates
-- downstairs -- the tie transfer that needs no induction, the corank-one corollary that
-- activity is basis membership at every size and every weight vector, the shipped
-- split-class family as an instance of it, the diamond's eight spanning-tree certificates
-- and two triangle refutations that make it the repository's first TOTAL tie at corank
-- two, and the (6,3) and (7,3) diamond classes with the proof that the (6,3) one is a
-- splitting of no corank-one design
#print axioms Gtz.IsParallelSplitting
#print axioms Gtz.sum_weight_eq_one_of_isParallelSplitting
#print axioms Gtz.surjective_classOf_of_isParallelSplitting
#print axioms Gtz.parallelSplitDesign
#print axioms Gtz.parallelSplitDesign_atom
#print axioms Gtz.parallelSplitDesign_weight
#print axioms Gtz.subsetSum_parallelSplitDesign_of_injOn
#print axioms Gtz.dominates_parallelSplitDesign_iff_of_injOn
#print axioms Gtz.exists_repeated_class_of_not_injOn
#print axioms Gtz.not_dominates_parallelSplitDesign_of_not_injOn
#print axioms Gtz.dominates_parallelSplitDesign_iff
#print axioms Gtz.exists_injOn_preimage_of_surjective
#print axioms Gtz.parallelSplitDesign_isTie
#print axioms Gtz.det_subsetRowMatrix_parallelSplitDesign_eq_zero_of_not_injOn
#print axioms Gtz.dominates_parallelSplitDesign_of_injOn_of_corankOne
#print axioms Gtz.dominates_parallelSplitDesign_iff_det_ne_zero_of_corankOne
#print axioms Gtz.exactlyTied_parallelSplitDesign_of_det_ne_zero_of_corankOne
#print axioms Gtz.splitClass_isParallelSplitting
#print axioms Gtz.splitClassDesign_eq_parallelSplitDesign
#print axioms Gtz.splitClassDesign_dominates_of_injOn
#print axioms Gtz.splitClassDesign_dominates_iff_det_ne_zero
#print axioms Gtz.splitClassDesign_exactlyTied_of_injOn
#print axioms Gtz.diamond_dominates_of_nonneg
#print axioms Gtz.diamond_not_dominates_of_negative
#print axioms Gtz.diamond_dominates_congr
#print axioms Gtz.diamondDesign_dominates_014
#print axioms Gtz.diamondDesign_dominates_023
#print axioms Gtz.diamondDesign_dominates_034
#print axioms Gtz.diamondDesign_dominates_123
#print axioms Gtz.diamondDesign_dominates_124
#print axioms Gtz.diamondDesign_dominates_134
#print axioms Gtz.diamondDesign_dominates_234
#print axioms Gtz.diamondDesign_not_dominates_013
#print axioms Gtz.diamondDesign_not_dominates_024
#print axioms Gtz.diamondDesign_dominates_of_ne_circuits
#print axioms Gtz.diamondDesign_dominates_iff
#print axioms Gtz.not_isGroundConnected_diamond_013
#print axioms Gtz.not_isGroundConnected_diamond_024
#print axioms Gtz.diamondDesign_dominates_iff_isSpanningTree
#print axioms Gtz.diamondDesign_isTotalTie
#print axioms Gtz.diamondDesign_weight
#print axioms Gtz.sixIntoFiveDiamond
#print axioms Gtz.sixSplitDiamondWeight
#print axioms Gtz.sixSplitDiamond_isParallelSplitting
#print axioms Gtz.sixSplitDiamondDesign
#print axioms Gtz.sixSplitDiamondDesign_isTie
#print axioms Gtz.sixSplitDiamondDesign_dominates_iff
#print axioms Gtz.sevenIntoFiveDiamond
#print axioms Gtz.sevenSplitDiamondWeight
#print axioms Gtz.sevenSplitDiamond_isParallelSplitting
#print axioms Gtz.sevenSplitDiamondDesign
#print axioms Gtz.sevenSplitDiamondDesign_isTie
#print axioms Gtz.sevenSplitDiamondDesign_dominates_iff
#print axioms Gtz.exists_injOn_not_dominates_sixSplitDiamondDesign
#print axioms Gtz.sixSplitDiamondDesign_atom_castSucc
#print axioms Gtz.not_eq_parallelSplitDesign_corankOne_sixSplitDiamondDesign

-- Gtz/Quantitative/CauchyBinetValueFloor.lean -- FLOOR-CB, the Cauchy-Binet floor
-- -(1/size)(1 - 1/C(size - 1, rank - 1)) on the value of an admissible chart stationarity
-- datum: the contraction step putting a block determinant below every Rayleigh quotient, the
-- per-subset cap det P[C] <= max over the subset of (weight + value), which needs neither the
-- weight floor nor any sign condition, the double count against Cauchy-Binet that turns that
-- cap into the floor, the improvement over the shipped -1/size recorded as the exact positive
-- identity 1/(size * C(size - 1, rank - 1)) so that no cell merely reproduces the old floor,
-- the six cell values -3/20, -2/15, -5/42, -3/28, -3/20 and -19/140, and the DISCHARGE of the
-- numeric floor hypothesis of
-- not_isChartStationaryData_of_isChartTwoBlockFamily_of_flooredNegativeValue -- one of that
-- theorem's two undischarged hypotheses, EliminatesChartTwoBlockValue remaining
#print axioms Gtz.sum_eq_sum_of_vanishes_offSubset
#print axioms Gtz.sum_selected_eq_sum_pick
#print axioms Gtz.eigenvalue_le_one_of_posSemidef_one_sub
#print axioms Gtz.det_le_eigenvalue_of_posSemidef_of_posSemidef_one_sub
#print axioms Gtz.det_le_dotProduct_mulVec_of_posSemidef_of_posSemidef_one_sub
#print axioms Gtz.posSemidef_projectionOfDesign
#print axioms Gtz.posSemidef_one_sub_projectionOfDesign
#print axioms Gtz.shadowDeterminant_le_dotProduct_mulVec_of_pick
#print axioms Gtz.shadowDeterminant_le_dotProduct_mulVec_of_support
#print axioms Gtz.rank_pos_of_isChartArgmaxValue
#print axioms Gtz.shadowDeterminant_le_of_isChartArgmaxValue
#print axioms Gtz.shadowDeterminant_le_sup'_weight_add_value_of_isChartArgmaxValue
#print axioms Gtz.sum_powersetCard_sum_mem_eq_choose_mul_sum
#print axioms Gtz.cauchyBinetValueFloor
#print axioms Gtz.one_le_choose_mul_one_add_size_mul_value_of_isChartArgmaxValue
#print axioms Gtz.cauchyBinetValueFloor_le_value_of_isChartArgmaxValue
#print axioms Gtz.cauchyBinetValueFloor_le_value_of_isChartStationaryData
#print axioms Gtz.cauchyBinetValueFloor_sub_neg_inv_size_eq
#print axioms Gtz.neg_inv_size_lt_cauchyBinetValueFloor
#print axioms Gtz.cauchyBinetValueFloor_sixThree
#print axioms Gtz.cauchyBinetValueFloor_sevenThree
#print axioms Gtz.cauchyBinetValueFloor_eightThree
#print axioms Gtz.cauchyBinetValueFloor_nineThree
#print axioms Gtz.cauchyBinetValueFloor_sixFour
#print axioms Gtz.cauchyBinetValueFloor_sevenFour
#print axioms Gtz.neg_three_div_twenty_le_value_of_isChartStationaryData
#print axioms Gtz.neg_two_div_fifteen_le_value_of_isChartStationaryData
#print axioms Gtz.zero_le_value_of_isChartTwoBlockFamily_of_eliminates_of_design
#print axioms Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_negativeValue

-- Gtz/Quantitative/VolumeAverageLaw.lean -- THE VOLUME-AVERAGE LAW IS FALSE: the campaign
-- premise that the projection determinantal average of the least eigenvalue clears the
-- domination threshold, stated existentially through IsBelowSubsetSpectrum so that no
-- eigenvalue machinery, no spectral theorem and no surd is needed; the implication the law
-- was for, that an average never exceeds a maximum and so the law would give GTZ outright;
-- the tetrahedron, where all four triples dominate and the law holds with EQUALITY, so the
-- refutation is about the functional and not about a vacuous statement; and TWO exactly
-- rational (3,2) witnesses refuting it, the second with every leverage strictly above one so
-- the all-heavy retreat is closed too -- both exhibiting a dominating 2-subset, so
-- GtzWeighted is untouched, and at the first the MATRIX average is verified above the
-- identity by hand, separating the two functionals on one design.  Then the
-- elementary-symmetric bound det S_C >= 1/e_rank(t), sharp at the tetrahedron, with the
-- degenerate division form named in the statement rather than left to Lean's x/0 = 0
#print axioms Gtz.IsBelowSubsetSpectrum
#print axioms Gtz.isBelowSubsetSpectrum_form_le
#print axioms Gtz.isBelowSubsetSpectrum_zero
#print axioms Gtz.dominates_of_one_le_isBelowSubsetSpectrum
#print axioms Gtz.volumeSamplingAverage
#print axioms Gtz.HasDominatingVolumeSamplingAverage
#print axioms Gtz.exists_dominates_of_hasDominatingVolumeSamplingAverage
#print axioms Gtz.posSemidef_expectedSubsetSum_sub_volumeSamplingAverage_smul_one
#print axioms Gtz.hasDominatingVolumeSamplingAverage_of_forall_dominates
#print axioms Gtz.leverageOf_tetraAtom
#print axioms Gtz.tetraDesign_dominates_of_card_three
#print axioms Gtz.tetraDesign_hasDominatingVolumeSamplingAverage
#print axioms Gtz.volumeAverageKillAtom
#print axioms Gtz.volumeAverageKillDesign
#print axioms Gtz.volumeAverageKillDesign_leverage_eq
#print axioms Gtz.volumeAverageKillDesign_shadowDeterminant_zeroOne
#print axioms Gtz.volumeAverageKillDesign_shadowDeterminant_zeroTwo
#print axioms Gtz.volumeAverageKillDesign_shadowDeterminant_oneTwo
#print axioms Gtz.volumeAverageKillDesign_shadowDeterminant_sum
#print axioms Gtz.isBelowSubsetSpectrum_pair_form_le
#print axioms Gtz.volumeAverageKillDesign_isBelowSubsetSpectrum_zeroOne_le
#print axioms Gtz.volumeAverageKillDesign_isBelowSubsetSpectrum_zeroTwo_le
#print axioms Gtz.volumeAverageKillDesign_isBelowSubsetSpectrum_oneTwo_le
#print axioms Gtz.volumeSamplingAverage_atSizeThreeRankTwo
#print axioms Gtz.volumeAverageKillDesign_volumeSamplingAverage_le
#print axioms Gtz.volumeAverageKillDesign_not_hasDominatingVolumeSamplingAverage
#print axioms Gtz.volumeAverageKillDesign_dominates_zeroTwo
#print axioms Gtz.not_forall_hasDominatingVolumeSamplingAverage
#print axioms Gtz.exists_design_failing_volumeSamplingAverage_law_with_dominator
#print axioms Gtz.volumeAverageKillDesign_expectedSubsetSum_eq
#print axioms Gtz.volumeAverageKillDesign_posSemidef_expectedSubsetSum_sub_one
#print axioms Gtz.heavyVolumeAverageKillAtom
#print axioms Gtz.heavyVolumeAverageKillDesign
#print axioms Gtz.heavyVolumeAverageKillDesign_allHeavy
#print axioms Gtz.heavyVolumeAverageKillDesign_shadowDeterminant_zeroOne
#print axioms Gtz.heavyVolumeAverageKillDesign_shadowDeterminant_zeroTwo
#print axioms Gtz.heavyVolumeAverageKillDesign_shadowDeterminant_oneTwo
#print axioms Gtz.heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_zeroOne_le
#print axioms Gtz.heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_zeroTwo_le
#print axioms Gtz.heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_oneTwo_le
#print axioms Gtz.heavyVolumeAverageKillDesign_volumeSamplingAverage_le
#print axioms Gtz.heavyVolumeAverageKillDesign_not_hasDominatingVolumeSamplingAverage
#print axioms Gtz.heavyVolumeAverageKillDesign_dominates_oneTwo
#print axioms Gtz.exists_allHeavy_design_failing_volumeSamplingAverage_law
#print axioms Gtz.weightElementary
#print axioms Gtz.subsetWeightProduct_pos
#print axioms Gtz.weightElementary_pos
#print axioms Gtz.exists_detSubsetSum_ge_inv_weightElementary
#print axioms Gtz.weightElementary_of_uniformWeight
#print axioms Gtz.exists_detSubsetSum_ge_pow_div_choose
#print axioms Gtz.sum_shadowDeterminant_div_detSubsetSum_eq_independentWeightProduct
#print axioms Gtz.sum_independentWeightProduct_le_weightElementary
#print axioms Gtz.sum_independentWeightProduct_lt_weightElementary_of_dependentSubset
#print axioms Gtz.subsetSum_triple
#print axioms Gtz.finset_card_three_cases_atSizeFour
#print axioms Gtz.tetraDesign_detSubsetSum_eq
#print axioms Gtz.tetraDesign_weightElementary_three
#print axioms Gtz.tetraDesign_detSubsetSum_eq_inv_weightElementary

-- Gtz/Quantitative/ProjectionOnePointMarginal.lean -- C7, the projection one-point marginal
-- DISCHARGED: the rank-subsets containing a fixed atom carry exactly the chart's diagonal
-- entry there, sum over |C| = rank with c in C of det P_C = P_cc = t_c * l_c, for every
-- weighted design and with no side condition.  So Gtz.IsProjectionOnePointMarginal -- a
-- def ... : Prop that was never discharged and that four shipped theorems carried as a
-- hypothesis -- is now the theorem Gtz.isProjectionOnePointMarginal and can be supplied at
-- every call site.  The erased chart (1 - E_cc) P is P with one row zeroed, so its principal
-- minors are exactly the chart minors AVOIDING that atom; Weinstein-Aronszajn moves its
-- generating function to size rank as 1 + X (1 - v_c v_c^T), where every principal block is
-- again a rank-one gap and det(1 - u u^T) = 1 - <u,u>, so the level-minors of the gap sum to
-- C(rank, level) - C(rank - 1, level - 1) P_cc by the shipped double count.  That is C7-A,
-- det(1 + X (1 - E_cc) P) = (1 + X)^(rank - 1) (1 + (1 - P_cc) X), by Pascal's rule and in ONE
-- polynomial variable -- the construction plan recorded on the Prop asks for a bivariate
-- argument and is unnecessary.  Subtracting the avoiding minors from the shipped total gives
-- the marginal at every subset size, and one exchange of summation over the incidence
-- B subset C gives the count FLOOR-E2 consumes, (size - rank)(rank - 1) P_cc + rank.  The
-- hypotheses are sharp and stated: 0 < level (the identity is false at level 0 under Nat
-- subtraction), 1 <= rank for C7-A (at rank 0 the two sides are 1 and 1 + X), 2 <= rank for
-- the e_{rank-1} count; the discharge itself carries nothing beyond the design, rank 0
-- included.  Closes no covering class and moves no cell
#print axioms Gtz.det_one_sub_vecMulVec
#print axioms Gtz.erasedRowChart
#print axioms Gtz.erasedRowChart_apply
#print axioms Gtz.erasedRowChart_eq_erasedFrame_mul_transpose
#print axioms Gtz.transpose_mul_erasedScaledAtomRows
#print axioms Gtz.det_one_add_X_smul_erasedRowChart_eq_rankGap
#print axioms Gtz.projectionOfDesign_diagonal_eq_sum_sq
#print axioms Gtz.det_submatrix_erasedRowChart
#print axioms Gtz.det_submatrix_one_sub_vecMulVec
#print axioms Gtz.sum_det_submatrix_one_sub_vecMulVec
#print axioms Gtz.det_one_add_X_smul_erasedRow_projectionOfDesign
#print axioms Gtz.sum_shadowDeterminant_eq_choose
#print axioms Gtz.sum_shadowDeterminant_notMem_eq
#print axioms Gtz.sum_shadowDeterminant_mem_eq_diag_mul_choose
#print axioms Gtz.sum_shadowDeterminant_mem_eq_diag
#print axioms Gtz.isProjectionOnePointMarginal
#print axioms Gtz.powersetCard_eq_filter_subset
#print axioms Gtz.card_filter_powersetCard_superset_mem
#print axioms Gtz.sum_esym_shadowDeterminant_mem_eq

-- Gtz/Quantitative/ElementaryValueFloor.lean -- FLOOR-E2, the elementary-symmetric floor
-- -(1/size)(1 - 1/((size - rank)(rank - 1) + rank)) on the value of an admissible chart
-- stationarity datum: -4/27 at (6,3) and -10/77 at (7,3), against FLOOR-CB's -3/20 and -2/15.
-- FLOOR-CB reads det P[C] as lambda_min times the other eigenvalues and caps that factor by
-- one, which needs P[C] <= 1; E2 caps it by e_{rank-1}(P[C]) instead, of which it is one
-- nonnegative term, so the contraction hypothesis gets WEAKER -- the spectral step assumes
-- only positive semidefiniteness.  Its ingredients: the minor-side spectral dictionary that
-- the level-minors of a Hermitian matrix sum to e_level of its spectrum, read off one charpoly
-- coefficient two ways; the per-matrix step det A <= <u, A u> e_{n-1}(A) at a unit probe; the
-- block bridge putting e_{rank-1}(P[C]) as a sum of chart minors, with no esymm and no block
-- in the statement; E2-A, the per-subset cap against an arbitrary cap exactly as FLOOR-CB's
-- C1-A; and the sum against Cauchy-Binet through the shipped count
-- Gtz.sum_esym_shadowDeterminant_mem_eq and the leverage bound P_cc <= 1.  FLOOR-E2 proper
-- carries 2 <= rank, which is that count's hypothesis and not caution about the edges; the
-- COMBINED floor, at the count min(C(size - 1, rank - 1), (size - rank)(rank - 1) + rank),
-- carries no rank hypothesis at all -- rank 1 makes both counts one and dispatches to
-- FLOOR-CB, and rank 0 is unreachable by Gtz.rank_pos_of_isChartArgmaxValue -- so the kernel
-- holds one floor at least as good as either parent with no cell excluded at either edge.
-- The two counts cross between (5,3), where the binomial still wins at 6 against 7, and
-- (6,3), where E2 wins at 9 against 10.  Then C8-a, the tightened Handelman certificate
-- 64 E(g) = 18603(-g)^3 + 196101(g + 4/27)(-g)^2 + 269001(g + 4/27)^2(-g) + 98415(g + 4/27)^3,
-- all four coefficients positive integers, giving the margin 689/729 <= E on [-4/27, 0]
-- against the 1711/2000 the shipped certificate gives on the wider window; E(-1/6) = 0 and
-- -1/6 < -4/27, so the original -1/size window does contain a root of the eliminant and the
-- floor is load-bearing rather than cosmetic.  Closes no covering class and discharges
-- nothing: that arc's numeric hypothesis was already discharged at -3/20 by FLOOR-CB, so this
-- supplies margin, and Gtz.EliminatesChartTwoBlockValue remains undischarged
#print axioms Gtz.dotProduct_self_pick_eq_of_support
#print axioms Gtz.dotProduct_mulVec_submatrix_pick_eq_of_support
#print axioms Gtz.dotProduct_mulVec_le_of_admissibleProbe
#print axioms Gtz.sum_det_principalMinors_eq_sum_prod_eigenvalues
#print axioms Gtz.codimOneMinorSum
#print axioms Gtz.codimOneMinorSum_nonneg
#print axioms Gtz.det_le_eigenvalue_mul_codimOneMinorSum
#print axioms Gtz.det_le_dotProduct_mulVec_mul_codimOneMinorSum
#print axioms Gtz.mappedSubsetEquiv
#print axioms Gtz.shadowDeterminant_map_eq_det_blockMinor
#print axioms Gtz.sum_shadowDeterminant_powersetCard_eq_sum_det_blockMinors
#print axioms Gtz.codimOneMinorSum_submatrix_eq_sum_shadowDeterminant
#print axioms Gtz.shadowDeterminant_le_mul_sum_shadowDeterminant_of_isChartArgmaxValue
#print axioms Gtz.elementaryCount
#print axioms Gtz.combinedCount
#print axioms Gtz.valueFloorOfCount
#print axioms Gtz.elementaryValueFloor
#print axioms Gtz.combinedValueFloor
#print axioms Gtz.cauchyBinetValueFloor_eq
#print axioms Gtz.valueFloorOfCount_le_valueFloorOfCount_of_count_le
#print axioms Gtz.valueFloorOfCount_le_value_of_one_le_mul
#print axioms Gtz.sum_powersetCard_sum_mem_mul_eq
#print axioms Gtz.one_le_elementaryCount_mul_one_add_size_mul_value_of_isChartArgmaxValue
#print axioms Gtz.elementaryCount_pos
#print axioms Gtz.cauchyBinetCount_pos
#print axioms Gtz.combinedCount_pos
#print axioms Gtz.elementaryValueFloor_le_value_of_isChartArgmaxValue
#print axioms Gtz.elementaryValueFloor_le_value_of_isChartStationaryData
#print axioms Gtz.combinedValueFloor_le_value_of_isChartArgmaxValue
#print axioms Gtz.combinedValueFloor_le_value_of_isChartStationaryData
#print axioms Gtz.cauchyBinetValueFloor_le_combinedValueFloor
#print axioms Gtz.elementaryValueFloor_le_combinedValueFloor
#print axioms Gtz.elementaryCount_lt_choose_sixThree
#print axioms Gtz.choose_lt_elementaryCount_fiveThree
#print axioms Gtz.elementaryCount_sixThree
#print axioms Gtz.elementaryCount_sevenThree
#print axioms Gtz.elementaryValueFloor_sixThree
#print axioms Gtz.elementaryValueFloor_sevenThree
#print axioms Gtz.combinedCount_sixThree
#print axioms Gtz.combinedCount_sevenThree
#print axioms Gtz.combinedValueFloor_sixThree
#print axioms Gtz.combinedValueFloor_sevenThree
#print axioms Gtz.neg_four_div_twentySeven_le_value_of_isChartStationaryData
#print axioms Gtz.neg_ten_div_seventySeven_le_value_of_isChartStationaryData
#print axioms Gtz.twoBlockEliminantCubic_eq_tightenedHandelmanCombination
#print axioms Gtz.twoBlockEliminantCubic_nonneg_of_mem_tightenedWindow
#print axioms Gtz.twoBlockEliminantCubic_sub_tightenedMargin_eq_prod
#print axioms Gtz.tightenedHandelmanMargin_le_twoBlockEliminantCubic
#print axioms Gtz.twoBlockEliminantCubic_pos_of_mem_tightenedWindow
#print axioms Gtz.twoBlockEliminantCubic_ne_zero_of_tightenedNegativeValue
#print axioms Gtz.twoBlockEliminantCubic_neg_inv_six_eq_zero
#print axioms Gtz.not_tightenedWindow_neg_inv_six
#print axioms Gtz.neg_three_div_twenty_lt_neg_four_div_twentySeven

-- Gtz/Quantitative/SubsetDeterminantBound.lean -- two independent things, and the first is a
-- completion rather than a construction.  C2, the elementary-symmetric bound
-- det S_C >= 1/e_rank(t), was ALREADY SHIPPED in Gtz.Quantitative.VolumeAverageLaw together
-- with its uniform-weight form, its tetrahedron sharpness triple and the degenerate division
-- form; none of that is restated.  What is added is the division-free primitive -- a uniform
-- cap on the subset determinants forces 1 <= cap * e_rank(t), stated against an arbitrary cap,
-- so no maximum, no positivity of e_rank(t) and no nonempty family are needed -- the
-- supersession over the binomial pigeonhole MEASURED as exactly the factor C(size, rank), with
-- no Maclaurin inequality anywhere; the three uniform-weight numerals 16 at (4,3), 54/5 at
-- (6,3) and 49/5 at (7,3), which need no Maclaurin because at uniform weights e_rank(t) is an
-- exact evaluation; and the weight-free form at arbitrary weights CONDITIONAL on Maclaurin's
-- inequality, which Mathlib does not carry and which is an explicit hypothesis, not a proof.
-- Then C4, the determinant-trace floor: AM-GM in natural-power form, absent from Mathlib in
-- that shape, gives (dim - 1)^(dim - 1) det A <= lambda_j(A) tr(A)^(dim - 1) at EVERY
-- eigenvalue index and with no case split on the dimension, solved for the eigenvalue as
-- detTraceFloor and restated in the Loewner form the repository speaks.  It is landed as
-- matrix analysis and NOT as a route: the (det, tr) = (27/2, 9) fibre in dimension three
-- carries positive semidefinite forms on both sides of the domination threshold -- spectra
-- (6, 3/2, 3/2) and (3 - 3 sqrt2/2, 3, 3 + 3 sqrt2/2) -- so EVERY function of the pair that
-- floors the spectrum is at most 3 - 3 sqrt2/2 < 1 there and can never certify S_C >= 1.  The
-- two witnesses are diagonal representatives of those spectra; that the sixteen independent
-- triples of the D_3 root design realise exactly them is NOT asserted here.  C4's own value on
-- that fibre is 2/3, strictly below the ceiling, so it is not sharp for its own method either.
-- Finally the C6 companion: E_pi[S_C] >= 1 for every weighted design UNCONDITIONALLY, which is
-- the shipped leverage-weighted statement plus the one-point marginal, now that the marginal
-- is a theorem rather than an assumed Prop; and the derandomisation gap in design-free form, a
-- two-member positive semidefinite family whose uniform average is exactly the identity while
-- NO member admits any positive Loewner floor.  Closes no cell and excludes no covering class
#print axioms Gtz.one_le_capValue_mul_weightElementary
#print axioms Gtz.exists_one_le_detSubsetSum_mul_weightElementary
#print axioms Gtz.exists_inv_choose_le_weightElementary_mul_detSubsetSum
#print axioms Gtz.exists_detSubsetSum_ge_pow_div_choose_of_maclaurin
#print axioms Gtz.exists_detSubsetSum_ge_sixteen_of_uniformWeight
#print axioms Gtz.exists_detSubsetSum_ge_fiftyFour_div_five_of_uniformWeight
#print axioms Gtz.exists_detSubsetSum_ge_fortyNine_div_five_of_uniformWeight
#print axioms Gtz.prod_le_pow_sum_div_card
#print axioms Gtz.pow_card_mul_prod_le_pow_sum
#print axioms Gtz.pow_pred_mul_det_le_eigenvalue_mul_trace_pow
#print axioms Gtz.detTraceFloor
#print axioms Gtz.detTraceFloor_le_eigenvalue_of_posSemidef
#print axioms Gtz.posSemidef_sub_detTraceFloor_smul_one
#print axioms Gtz.diagonal_sub_smul_one
#print axioms Gtz.sqrt_two_sq
#print axioms Gtz.sqrt_two_lt_two
#print axioms Gtz.four_div_three_lt_sqrt_two
#print axioms Gtz.dominatingFibreForm
#print axioms Gtz.slackFibreForm
#print axioms Gtz.posSemidef_dominatingFibreForm
#print axioms Gtz.det_dominatingFibreForm
#print axioms Gtz.trace_dominatingFibreForm
#print axioms Gtz.posSemidef_dominatingFibreForm_sub_one
#print axioms Gtz.posSemidef_slackFibreForm
#print axioms Gtz.det_slackFibreForm
#print axioms Gtz.trace_slackFibreForm
#print axioms Gtz.slackFibreLeast_lt_one
#print axioms Gtz.not_posSemidef_slackFibreForm_sub_one
#print axioms Gtz.exists_pair_on_detTraceFibre_separated_by_domination
#print axioms Gtz.detTraceFloorFunction_le_slackFibreLeast
#print axioms Gtz.detTraceFloorFunction_lt_one
#print axioms Gtz.detTraceFloor_rankThreeFibre
#print axioms Gtz.detTraceFloor_rankThreeFibre_lt_slackFibreLeast
#print axioms Gtz.posSemidef_expectedSubsetSum_sub_one
#print axioms Gtz.averageGapForm
#print axioms Gtz.posSemidef_averageGapForm
#print axioms Gtz.averageGapForm_floor_nonpos
#print axioms Gtz.half_smul_averageGapForm_add
#print axioms Gtz.exists_family_flooring_average_without_flooring_member

-- Gtz/Quantitative/OddRankDeterminantUpgrade.lean -- the odd-rank value at zero, with a
-- constant: q(0) <= -1/e_rank(t) at every real weighted design of odd rank and with no side
-- condition.  That strictly strengthens the shipped Gtz.mixedCharPoly_eval_zero_nonpos_of_odd,
-- recovered here in one step, and removes the nonsingular-subset witness that
-- Gtz.mixedCharPoly_eval_zero_neg_of_odd consumes for strictness; neither shipped theorem is
-- modified.  Two shipped identities and one classical inequality, with no new analysis: (I1)
-- reads each volume-sampling mass as det P_C = (product of weights on C) det S_C, which turns
-- the rank-level coefficient into the volume-sampling average of det S_C and gives
-- q(0) = (-1)^rank E_pi[det S_C]; Cauchy-Schwarz in Engel form against the masses and their
-- weight products has numerator C(rank, level)^2 by the shipped total, which Cauchy-Binet
-- makes 1 at level = rank; and the parity sign is the only place the rank being odd is spent.
-- The level-parametric Engel bound is stated because it is free -- its level-one instance IS
-- the shipped Gtz.sq_rank_le_expectedElementary_one, which is therefore NOT restated -- and the
-- even-rank companion is recorded for completeness of the parity split, consumed by nothing.
-- ATTAINED exactly at the regular tetrahedron, where e_3(t) = 1/16 and q(0) = -16, so no
-- strengthening of the Cauchy-Schwarz step could lower the constant.  At uniform weights the
-- constant is -54/5 at (6,3) and -49/5 at (7,3), recorded against the two rank-three
-- witnesses; their true values at zero are MEASURED elsewhere and proved neither here nor
-- anywhere in the repository.  It bounds no ROOT -- the refutations
-- Gtz.not_mixedRootAtLeastOne_sixThree and Gtz.not_mixedRootAtLeastOne_sevenThree turn on the
-- value at 1, which this leaves untouched -- exhibits no subset, since a floor on an average
-- names none, closes no covering class and decides no cell
#print axioms Gtz.expectedElementary_rank_eq_volumeSamplingAverage_detSubsetSum
#print axioms Gtz.expectedElementary_rank_eq_sum_weightProduct_mul_detSubsetSum_sq
#print axioms Gtz.mixedCharPoly_eval_zero_eq_neg_one_pow_mul_expectedElementary
#print axioms Gtz.weightElementary_one
#print axioms Gtz.sq_choose_div_weightElementary_le_expectedElementary
#print axioms Gtz.inv_weightElementary_le_expectedElementary_rank
#print axioms Gtz.inv_weightElementary_le_volumeSamplingAverage_detSubsetSum
#print axioms Gtz.neg_inv_weightElementary_lt_zero
#print axioms Gtz.mixedCharPoly_eval_zero_le_neg_inv_weightElementary_of_odd
#print axioms Gtz.mixedCharPoly_eval_zero_nonpos_of_odd_from_upgrade
#print axioms Gtz.mixedCharPoly_eval_zero_lt_zero_of_odd
#print axioms Gtz.inv_weightElementary_le_mixedCharPoly_eval_zero_of_even
#print axioms Gtz.tetraDesign_attains_neg_inv_weightElementary_floor
#print axioms Gtz.rootKillDesign_weightElementary_three
#print axioms Gtz.mixedCharPoly_rootKillDesign_eval_zero_le
#print axioms Gtz.axisKillDesign_weightElementary_three
#print axioms Gtz.mixedCharPoly_axisKillDesign_eval_zero_le

-- Gtz/Quantitative/TwoBlockEliminationCertificate.lean -- THE ELIMINATION STEP, DISCHARGED.
-- Gtz.EliminatesChartTwoBlockValue 3 -- asserted and never proved since the header of
-- Gtz.Quantitative.ChartEmptinessCertificate -- is now the theorem
-- Gtz.eliminatesChartTwoBlockValue_three, so the two-block partition class of the (6,3)
-- covering census becomes the FIRST class this project closes carrying no class-specific
-- hypothesis.  It is a corollary of something stronger and simpler than an elimination: a chart
-- stationarity datum whose active family is two complementary blocks and whose value is
-- NEGATIVE has value = -1/size EXACTLY, at every size and every rank.  The value is PINNED, not
-- merely confined to the root set of a cubic, and the proof is a trace argument with no case
-- split, no Groebner basis and no admissibility.  Write Xi for the assembly and Q for the
-- orthogonal projection onto its range.  The BLOCK-DIAGONAL TRUNCATION of the chart acts on Xi
-- exactly as N = value + diag t -- the global identity P Xi = N Xi is FALSE, its cross-block
-- entries need not vanish, and the truncation is what repairs it; the chart commutes with Xi
-- hence with Q, the block indicator commutes with Xi so Q is block diagonal, and the truncation
-- minus N annihilates Xi hence Q, which together give tr(P Q) = sum_c (value + t_c) Q_cc.  Then
-- tr Xi = 1 forces Xi nonzero so tr Q >= 1; a symmetric idempotent has diagonal in [0,1] and
-- the weights sum to one, so sum_c t_c Q_cc <= 1; and value < 0 gives tr(P Q) <= value + 1 < 1.
-- INTEGRALITY IS THE CRUX: P Q is a symmetric idempotent, a NONZERO one has trace at least one
-- by one discrete Cauchy-Schwarz, so P Q = 0, so P Xi = 0, and the shipped forced diagonal
-- tr(P Xi) = value + 1/size pins the value.  Read against Xi itself the same trace gives only
-- the shipped floor value + 1/size >= 0, which is exactly why the range projection is built.
-- WHAT IS NOT USED, recorded because the sibling header says otherwise: ADMISSIBILITY --
-- Gtz.IsChartArgmaxValue is bound and discarded, and the (4,2) witness cited to justify it is
-- vacuous at rank three, where two occupied blocks force size = 2 * rank = 6; THE RANK, the
-- value theorem holding at every (size, rank); BLOCK NONEMPTINESS, chosenSubset and its
-- complement partitioning the atoms either way; and THE CAUCHY-BINET VALUE FLOOR -3/20, since
-- the SHIPPED strict floor at -1/size finishes it.  Negativity is used exactly once and has no
-- substitute -- at value = 1/3 with distinct weights the same bound reads 3 = 6/3 + 1 and is
-- TIGHT.  So Gtz.zero_le_value_of_isChartTwoBlockFamily_of_design and its non-existence form
-- are the shipped pair with heliminates and hrank BOTH removed.  The exact RATIONAL (6,3)
-- witness at value = -1/6, uniform weights and assembly 1/6 inside the blocks, makes the
-- discharged statement one about a NONEMPTY class; it is INADMISSIBLE by one completed square
-- on the triple {0,1,5}, where the gap's least eigenvalue is +1/6, so it contradicts no shipped
-- floor, and it is the exact form of the numerical note in the header of
-- Gtz.Quantitative.ChartTwoBlock.  The two cofactor identities are CORROBORATION OF THE
-- ELIMINANT ONLY, and NO SATURATION IS PERFORMED ANYWHERE: neither divides by anything, carries
-- a g^N multiplier or invokes a nonvanishing side polynomial, which matters because the total
-- multiplier mass sum_c tau_c = 1 + 6 value IS the factor 6 value + 1 whose root is the value
-- landed on.  Neither identity is the discharge and no cofactor list could be -- the
-- elimination step has a SIGN antecedent no ideal membership sees, and they cover only the
-- rank-one-multiplier branch.  ONE class of the 2069; the other 2068 are untouched
#print axioms Gtz.diagonal_eq_sum_sq_of_symmetricIdempotent
#print axioms Gtz.zero_le_diagonal_of_symmetricIdempotent
#print axioms Gtz.diagonal_le_one_of_symmetricIdempotent
#print axioms Gtz.trace_eq_sum_sq_of_symmetricIdempotent
#print axioms Gtz.one_le_trace_of_symmetricIdempotent_of_ne_zero
#print axioms Gtz.orthogonalConjugate_mul_orthogonalConjugate
#print axioms Gtz.orthogonalConjugate_orthogonalConjugate_symm
#print axioms Gtz.eq_of_orthogonalConjugate_eq
#print axioms Gtz.commute_diagonalConjugate_of_commute
#print axioms Gtz.mul_diagonalConjugate_eq_zero_of_mul_eq_zero
#print axioms Gtz.spectralIndicator
#print axioms Gtz.rangeProjection
#print axioms Gtz.transpose_mul_eigenvectorUnitary_self
#print axioms Gtz.eigenvectorUnitary_mul_transpose_self
#print axioms Gtz.eq_eigenvectorUnitary_mul_diagonal_mul_transpose
#print axioms Gtz.spectralIndicator_mul_self
#print axioms Gtz.spectralIndicator_mul_eigenvalue
#print axioms Gtz.eigenvalues_ne_of_spectralIndicator_ne
#print axioms Gtz.spectralIndicator_eq_zero_of_eigenvalue_eq_zero
#print axioms Gtz.rangeProjection_transpose
#print axioms Gtz.rangeProjection_mul_self
#print axioms Gtz.rangeProjection_mul_eq_self
#print axioms Gtz.trace_rangeProjection_eq_sum_spectralIndicator
#print axioms Gtz.one_le_trace_rangeProjection_of_trace_ne_zero
#print axioms Gtz.commute_rangeProjection_of_commute
#print axioms Gtz.mul_rangeProjection_eq_zero_of_mul_eq_zero
#print axioms Gtz.chartBlockDiagonalPart
#print axioms Gtz.chartBlockDiagonalPart_apply_of_sameBlock
#print axioms Gtz.chartBlockDiagonalPart_apply_of_crossBlock
#print axioms Gtz.chartMultiplierAssembly_apply_eq_zero_of_notSameBlock
#print axioms Gtz.chartShiftedWeightDiagonal
#print axioms Gtz.chartBlockDiagonalPart_mul_multiplier
#print axioms Gtz.chartBlockIndicator
#print axioms Gtz.chartBlockIndicator_ne_of_notSameBlock
#print axioms Gtz.blockIndicator_mul_multiplier_comm
#print axioms Gtz.isHermitian_chartMultiplierAssembly_of_isChartStationaryData
#print axioms Gtz.rangeProjection_apply_eq_zero_of_notSameBlock
#print axioms Gtz.trace_projection_mul_rangeProjection
#print axioms Gtz.value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue
#print axioms Gtz.eliminatesChartTwoBlockValue_three
#print axioms Gtz.zero_le_value_of_isChartTwoBlockFamily_of_design
#print axioms Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue
#print axioms Gtz.twoBlockEliminantCubic_eq_coreCofactorCombination
#print axioms Gtz.twoBlockEliminantCubic_eq_couplingCofactorCombination
#print axioms Gtz.blockLevelSum_cubic_eq_idempotentCombination
#print axioms Gtz.twoBlockEliminantCubic_eq_levelSum_cubic
#print axioms Gtz.chartTwoBlockTripleAxis
#print axioms Gtz.chartTwoBlockTripleSign
#print axioms Gtz.chartTwoBlockTripleProjection
#print axioms Gtz.chartTwoBlockTripleWeight
#print axioms Gtz.chartTwoBlockTripleSubset
#print axioms Gtz.chartTwoBlockTripleMultiplierWeight
#print axioms Gtz.chartTwoBlockTripleSupport
#print axioms Gtz.chartTwoBlockTripleTightDir
#print axioms Gtz.chartTwoBlockTripleMultiplier
#print axioms Gtz.chartTwoBlockTripleProjection_transpose
#print axioms Gtz.chartTwoBlockTripleProjection_mul_self
#print axioms Gtz.chartTwoBlockTripleSupport_dotProduct_self
#print axioms Gtz.chartTwoBlockTripleAxis_of_mem
#print axioms Gtz.chartTwoBlockTripleAxis_ne_of_notMem
#print axioms Gtz.chartTwoBlockTripleGap_mulVec_support
#print axioms Gtz.chartTwoBlockTripleMultiplierAssembly_eq
#print axioms Gtz.chartTwoBlockTripleProjection_isChartStationaryData
#print axioms Gtz.chartTwoBlockTriple_isChartTwoBlockFamily
#print axioms Gtz.exists_isChartStationaryData_isChartTwoBlockFamily_rankThree_negativeValue
#print axioms Gtz.not_chartTwoBlockTriple_isChartArgmaxValue

-- Gtz/Quantitative/ClassRouteCost.lean -- A SECOND ELIMINANT, AND THE PROOF THAT THE
-- CLASS-BY-CLASS ROUTE CANNOT BE FINISHED.  Two halves, and the second is the load-bearing one.
-- THE MACHINE STILL WORKS one class up.  Gtz.threeMemberEliminant is the degree-seven
-- E3(g) = 3888 g^7 - 9072 g^6 + 7560 g^5 - 2520 g^4 + 147 g^3 + 77 g^2 - 10 g, factored by ring
-- as g(2g-1)(3g-2)(3g-1)(6g-5)(6g-1)(6g+1), equivalently (1/72) prod_{j=-1}^{5} (6g - j), whose
-- seven roots are exactly the seven sixths -1/6, 0, 1/6, 1/3, 1/2, 2/3, 5/6.  It is STRICTLY
-- POSITIVE on [-4/27, 0), read off the rewriting E3 = (-g)(1-2g)(2-3g)(1-3g)(5-6g)(1-6g)(6g+1)
-- in which six factors are positive because g < 0 and the seventh because -4/27 > -1/6 -- and
-- THAT LAST INEQUALITY IS THE WHOLE REASON EVERY ELIMINANT COMPUTED SO FAR CLOSES, there being
-- no sixth in the window at all.  So the floor's improvement from -1/6 to -4/27 is what makes
-- them close, which is NOT a floor closing a class: the floor is class-INDEPENDENT, it narrows
-- the window for all 2069 and excludes none.  Two census-surviving classes are closed by it,
-- {{0,1,2},{0,4,5},{1,2,3}} and {{0,1,5},{0,2,4},{1,2,3}}, each CONDITIONAL on its own instance
-- of the new hypothesis Gtz.EliminatesThreeMemberValue -- TWO NEW CITABLE HOLES BOUGHT TWO NEW
-- CONDITIONAL CLOSURES, and neither has the strength of the unconditional two-block closure.
-- That hypothesis carries the RANK-ONE BRANCH restriction IN THE STATEMENT, which is what the
-- outside computation covered and which the bundle does not force, and it is deliberately
-- admissibility-FREE because what was eliminated is the stationarity ideal.  No cofactor list
-- exists for E3: it is msolve output cross-checked over five primes and by a reversed variable
-- order, exactly the standing the two-block cubic had before a trace argument discharged it.
-- THE MACHINE CANNOT FINISH, and that is a theorem rather than a timing measurement.
-- Gtz.windowChartProjection_isChartStationaryData is an EXACT chart stationarity datum over
-- Q(sqrt 5) at value = (2 - sqrt 5)/6 = -0.0393446629..., STRICTLY INSIDE [-4/27, 0), on the
-- census-surviving four-member class {{0,3,5},{0,4,5},{1,2,3},{1,2,4}}.  Its chart is
-- (1/2) I + (sqrt 5/10) B for an explicit symmetric integer B of trace zero with B^2 = 5 I, so
-- every bundle field is discharged with no spectral decomposition and sqrt 5 enters in exactly
-- two places.  Hence Gtz.not_exists_windowRootFree_eliminatesWindowChartFamilyValue: NO real
-- function is both an eliminant for that class and nonvanishing on the window, for any
-- generator and at any cost, the obstruction being a POINT OF THE VARIETY rather than a
-- property of a generator.  The witness is INADMISSIBLE by one completed square on the triple
-- {1,3,4}, which is why it contradicts nothing shipped -- every value floor in the repository
-- carries Gtz.IsChartArgmaxValue -- and equally why it is fatal to a route that cannot see
-- admissibility at all.  It also refutes outright any "all chart-stationary values at (6,3) are
-- sixths" law.  It refutes the ROUTE and not the conjecture: GtzWeighted 6 3 is untouched.
-- Supporting combinatorics.  The SATURATED-ATOM FILTER, lifted from the shipped leg-side
-- Gtz.one_le_value_of_saturatedAtom to family vocabulary, with five decide audits: the star
-- {{0,1,4},{0,1,5},{0,2,3}} and the double star {{0,1,2},{0,1,3},{0,1,4},{0,1,5}} ARE saturated
-- and so were already dead before their 0.78 s and 750 s eliminations were run, while the two
-- closed classes and the window class survive it, so any future class selection must apply that
-- filter FIRST.  And the double count sum_c deg(c) = rank * |family|, whose (6,3) reading is
-- that a covering family of triples has every atom of degree one IF AND ONLY IF it has exactly
-- two members -- so the one class closed unconditionally was the only one of its structural
-- kind and its cheapness extrapolates to nothing.  The filter is stated on the LEG side, where
-- it is true; the chart bundle has no analogue and none is claimed.  Nothing here corrects the
-- census counts 2102, 2069, 2068, which are right.  Three classes of 2069 is three classes,
-- and (6,3) is not closed
#print axioms Gtz.threeMemberEliminant
#print axioms Gtz.threeMemberEliminant_eq_prod
#print axioms Gtz.threeMemberEliminant_eq_sixthProduct
#print axioms Gtz.threeMemberEliminant_eq_windowPositiveProduct
#print axioms Gtz.neg_inv_six_lt_neg_four_div_twentySeven
#print axioms Gtz.threeMemberEliminant_pos_of_mem_flooredWindow
#print axioms Gtz.threeMemberEliminant_ne_zero_of_flooredNegativeValue
#print axioms Gtz.not_exists_flooredNegativeValue_root_threeMemberEliminant
#print axioms Gtz.threeMemberEliminant_eq_zero_iff
#print axioms Gtz.IsActiveFamily
#print axioms Gtz.HasSimpleActiveSubsets
#print axioms Gtz.HasSaturatedAtom
#print axioms Gtz.mem_of_isActiveFamily
#print axioms Gtz.one_le_value_of_hasSaturatedAtom_of_isActiveFamily
#print axioms Gtz.activeFamilyDegree
#print axioms Gtz.sum_activeFamilyDegree_eq_rank_mul_card
#print axioms Gtz.forall_activeFamilyDegree_eq_one_iff_card_eq_two
#print axioms Gtz.chartTripleSharedEdgeFamily
#print axioms Gtz.chartTriplePairwiseMeetFamily
#print axioms Gtz.chartTripleStarFamily
#print axioms Gtz.chartTripleDoubleStarFamily
#print axioms Gtz.hasSaturatedAtom_chartTripleStarFamily
#print axioms Gtz.hasSaturatedAtom_chartTripleDoubleStarFamily
#print axioms Gtz.not_hasSaturatedAtom_chartTripleSharedEdgeFamily
#print axioms Gtz.not_hasSaturatedAtom_chartTriplePairwiseMeetFamily
#print axioms Gtz.EliminatesThreeMemberValue
#print axioms Gtz.zero_le_value_of_eliminatesThreeMemberValue
#print axioms Gtz.not_isChartStationaryData_of_eliminatesThreeMemberValue_of_negativeValue
#print axioms Gtz.zero_le_value_of_chartTripleSharedEdgeFamily_of_eliminates
#print axioms Gtz.zero_le_value_of_chartTriplePairwiseMeetFamily_of_eliminates
#print axioms Gtz.halfCoreShift
#print axioms Gtz.halfCoreShift_transpose
#print axioms Gtz.halfCoreShift_trace
#print axioms Gtz.halfCoreShift_mul_self
#print axioms Gtz.halfCoreShift_mulVec
#print axioms Gtz.halfCoreShift_mul_smul_comm
#print axioms Gtz.sqrt_five_sq
#print axioms Gtz.two_lt_sqrt_five
#print axioms Gtz.sqrt_five_lt_nine_div_four
#print axioms Gtz.windowChartCore
#print axioms Gtz.windowChartCore_transpose
#print axioms Gtz.windowChartCore_mul_self
#print axioms Gtz.windowChartCore_trace
#print axioms Gtz.windowChartProjection
#print axioms Gtz.windowChartProjection_transpose
#print axioms Gtz.windowChartProjection_mul_self
#print axioms Gtz.windowChartProjection_trace
#print axioms Gtz.windowChartWeight
#print axioms Gtz.windowChartValue
#print axioms Gtz.windowChartValue_neg
#print axioms Gtz.neg_four_div_twentySeven_lt_windowChartValue
#print axioms Gtz.windowChartValue_mem_flooredWindow
#print axioms Gtz.windowChartSubset
#print axioms Gtz.windowChartFamily
#print axioms Gtz.windowChartSign
#print axioms Gtz.windowChartTightDir
#print axioms Gtz.windowChartMultiplierWeight
#print axioms Gtz.windowChartMultiplierCore
#print axioms Gtz.windowChartCore_mul_multiplierCore_comm
#print axioms Gtz.windowChartLevel
#print axioms Gtz.windowChartCore_mulVec_sign
#print axioms Gtz.windowChartWeight_level_eq_value
#print axioms Gtz.windowChartGap_mulVec
#print axioms Gtz.windowChartGap_mulVec_sign
#print axioms Gtz.windowChartMultiplierAssembly_eq
#print axioms Gtz.windowChartProjection_isChartStationaryData
#print axioms Gtz.windowChart_isActiveFamily
#print axioms Gtz.windowChart_hasSimpleActiveSubsets
#print axioms Gtz.not_hasSaturatedAtom_windowChartFamily
#print axioms Gtz.windowChartFamily_activeFamilyDegree_eq_two
#print axioms Gtz.windowChartQuadraticForm
#print axioms Gtz.not_windowChartProjection_isChartArgmaxValue
#print axioms Gtz.eq_zero_at_windowChartValue_of_eliminatesWindowChartFamilyValue
#print axioms Gtz.not_exists_windowRootFree_eliminatesWindowChartFamilyValue
#print axioms Gtz.exists_isChartStationaryData_value_mem_flooredWindow

-- Gtz/Reduction/ChartAttainment.lean -- S1, ATTAINMENT.  The closed chart domain is
-- COMPACT and the chart objective attains its minimum on it.  Gtz.chartDomain carries the
-- domain on the RAW configuration space and cuts it out by five NON-STRICT SCALAR
-- conditions, so Gtz.isClosed_chartDomain is five isClosed_eq / isClosed_le steps with no
-- matrix-valued separation axiom; boundedness is the one inequality
-- Gtz.abs_chartEntry_le_one_of_mem_chartDomain, symmetry plus idempotency giving
-- sum_r P_rc^2 = P_cc at every column, so Gtz.isCompact_chartDomain is Heine-Borel in a
-- finite-dimensional space and holds at EVERY (size, rank) with no hypothesis at all.  No
-- manifold, no Grassmannian and no spectral factorisation appears, and the chart is never
-- factorised as V V^T, so this module is independent of the leaf S2 discharges.  Continuity
-- of the objective is the shipped Weyl bound Gtz.lipschitzWith_lambdaMinCLM through
-- Gtz.continuous_lambdaMinMat, closed under a finite sup'; attainment is then the extreme
-- value theorem, and Gtz.exists_chartObjective_isMin carries exactly [Nonempty (Fin rank)]
-- and ONE witness chart point.  The threshold dictionary
-- Gtz.zero_le_chartObjective_iff_exists_chartDominates reads 0 <= G as domination by some
-- rank-subset, at threshold ZERO because this is the CHART objective; the OBJECTIVE
-- MISMATCH recorded in Gtz.Reduction.CompactnessReduction stands undisturbed, since the
-- chart and design objectives share a threshold but not their minimisers, being related by
-- the non-uniform congruence diagonal(sqrt t_C), and nothing here transports a minimiser
-- across it.  The consumable form is Gtz.exists_interior_minimiser_of_not_chartGtz, which
-- composes with the shipped boundary dichotomy Gtz.weight_pos_of_forall_not_chartDominates
-- -- until now consumed by NOTHING, its own docstring naming it the packaging "a
-- compactness argument consumes" -- to produce one minimiser with all weights strictly
-- positive, strictly negative value, and no dominating subset.  Two guards keep the file
-- from vacuity at the shipped (4,2) witness.  It closes NO cell and supplies no
-- stationarity, no multiplier and no tangent direction: the minimiser is NOT proved to be a
-- critical point of anything, this repository carrying no subdifferential calculus
#print axioms Gtz.zero_le_lambdaMinMat_iff_forall
#print axioms Gtz.zero_le_lambdaMinMat_iff_posSemidef
#print axioms Gtz.chartDomain
#print axioms Gtz.chartConfig_mem_chartDomain
#print axioms Gtz.chartPointOfMem
#print axioms Gtz.abs_chartEntry_le_one_of_mem_chartDomain
#print axioms Gtz.chartPoint_diag_le_one
#print axioms Gtz.rank_le_size_of_chartPoint
#print axioms Gtz.isClosed_chartDomain
#print axioms Gtz.isCompact_chartDomain
#print axioms Gtz.chartGapRaw
#print axioms Gtz.chartGapRaw_chartConfig
#print axioms Gtz.continuous_chartGapRaw
#print axioms Gtz.chartBlockValue
#print axioms Gtz.chartCandidates
#print axioms Gtz.mem_chartCandidates_iff
#print axioms Gtz.chartCandidates_nonempty
#print axioms Gtz.chartObjectiveRaw
#print axioms Gtz.chartObjective
#print axioms Gtz.chartObjective_eq_chartObjectiveRaw
#print axioms Gtz.chartObjective_chartPointOfMem
#print axioms Gtz.continuous_chartBlockValue
#print axioms Gtz.continuous_chartObjectiveRaw
#print axioms Gtz.isHermitian_chartPointGap_submatrix
#print axioms Gtz.chartBlockValue_chartConfig
#print axioms Gtz.zero_le_chartBlockValue_iff_chartDominates
#print axioms Gtz.zero_le_chartObjective_iff_exists_chartDominates
#print axioms Gtz.exists_isMinOn_chartObjectiveRaw
#print axioms Gtz.exists_chartObjective_isMin
#print axioms Gtz.chartGtz_of_isMin_of_nonneg
#print axioms Gtz.gtzWeighted_of_isMin_of_nonneg
#print axioms Gtz.exists_minimiser_of_not_chartGtz
#print axioms Gtz.exists_interior_minimiser_of_not_chartGtz
#print axioms Gtz.exists_interior_minimiser_of_not_gtzWeighted
#print axioms Gtz.exists_chartObjective_isMin_fourTwo
#print axioms Gtz.chartBlockValue_liftFailure_neg

-- Gtz/Reduction/ChartPointFactorisation.lean -- S2, THE CHART-TO-DESIGN FACTORISATION,
-- DISCHARGED.  Gtz.ChartPointHasDesign (Gtz/Reduction/CompactnessReduction.lean:1527) was
-- an explicitly named UNPROVED LEAF whose own header called it "the SOLE obstruction to
-- feeding the already kernel-checked small rungs into any chart-side assembly"; it is now
-- the theorem Gtz.chartPointHasDesign, whose printed statement is
-- "forall (size rank : Nat), Gtz.ChartPointHasDesign size rank" -- NO hypothesis whatever,
-- at every cell.  So Gtz.chartGtzInterior_of_gtzWeighted_unconditional drops the hfactors
-- hypothesis, and Gtz.chartGtzInterior_iff_gtzWeighted and Gtz.chartGtz_iff_gtzWeighted are
-- plain equivalences carrying nothing: the chart route is an EQUIVALENCE at the top rather
-- than a strictly stronger hypothesis.  ENGINEERING, not research.  The content is the real
-- spectral theorem, which Mathlib carries and which this repository ALREADY had in
-- transpose form as Gtz.eq_eigenvectorUnitary_mul_diagonal_mul_transpose and its two
-- orthogonality companions -- shipped in Gtz/Quantitative/TwoBlockEliminationCertificate.lean,
-- which is why a Gtz/Reduction/ module imports a Gtz/Quantitative/ one.  That LAYERING DEBT
-- is recorded rather than repaired: the triple is generic linear algebra with no two-block
-- content and belongs in Gtz/LinAlg/.  Idempotency forces the eigenvalues into {0,1} by
-- conjugating, the trace counts the ones, and the frame is the corresponding block of
-- columns; no rank theory and no eigenvector reasoning is used.  THE POSITIVITY OF THE
-- WEIGHTS ENTERS IN EXACTLY ONE PLACE, the division by sqrt(weight c), which is why the
-- discharged statement is the INTERIOR one -- and the restriction is not an artifact:
-- Gtz.not_exists_design_of_weight_eq_zero shows a boundary chart point is the chart of NO
-- weighted design at all, so the boundary version of the leaf is FALSE, not open.  A second
-- honesty claim falls out for free: Gtz/LinAlg/ProjectionForm.lean:403-405 says of
-- Gtz.gtzOriginal_of_projectionCovering that it runs "one direction only" because the
-- surjectivity of A |-> A A^T onto the symmetric idempotents of trace k "is the spectral
-- factorization this repo does not have"; that surjectivity is step 1, so
-- Gtz.gtzOriginal_iff_projectionCovering upgrades the one-way statement to an iff, under
-- 0 < atoms and nothing else.  Gtz.ChartGtzInterior stays an unproved leaf and is NOT
-- weakened -- LEAD 1 of that module shows it is not weaker than the target -- and nothing
-- here bears on Gtz.GtzWeighted 6 3 or Gtz.GtzWeighted 7 3
#print axioms Gtz.exists_orthonormalFrame_of_symmetric_idempotent
#print axioms Gtz.designOfOrthonormalFrame
#print axioms Gtz.scaledAtomRows_designOfOrthonormalFrame
#print axioms Gtz.projectionOfDesign_designOfOrthonormalFrame
#print axioms Gtz.chartPoint_eq_of_chart_eq_of_weight_eq
#print axioms Gtz.chartPointHasDesign
#print axioms Gtz.not_exists_design_of_weight_eq_zero
#print axioms Gtz.chartGtzInterior_of_gtzWeighted_unconditional
#print axioms Gtz.chartGtzInterior_iff_gtzWeighted
#print axioms Gtz.chartGtz_iff_gtzWeighted
#print axioms Gtz.projectionCovering_of_frameProjectionCovering
#print axioms Gtz.projectionCovering_iff_frameProjectionCovering
#print axioms Gtz.gtzOriginal_iff_projectionCovering

-- Gtz/Quantitative/ChartDescentFromMinimality.lean -- S3, THE FIRST-ORDER SYSTEM DERIVED
-- FROM MINIMALITY.  Gtz.Quantitative.ChartStationary, ChartStrongStationary and
-- ChartCovering all take their datum as a HYPOTHESIS; the passage from "this point
-- minimises the chart objective" to "this datum holds" lived outside Lean, and honesty (a)
-- of ChartStrongStationary named the three ingredients it needed.  ALL THREE ARE SUPPLIED
-- HERE, and one of them was not needed.  (i) THE CURVE is the CAYLEY transform
-- Q(s) = (1 + sK)(1 - sK)^-1 at the skew K = (1/2)[Pdot, P]: orthogonal and RATIONAL in the
-- step, with no matrix exponential, and Gtz.chartCayleyProjection is a symmetric idempotent
-- of the same trace at EVERY step, so the constraint set is preserved exactly and not to
-- first order.  The smallness hypothesis is DELETED from the transform itself --
-- Gtz.coercive_chartCayleyDenominator makes 1 - sK invertible at every real step, since
-- <x, Kx> = 0 for skew K -- and smallness enters only in keeping the weights positive,
-- meeting the closeness radius, and beating the remainder.  (ii) THE EXPANSION is
-- Gtz.abs_chartCayleyProjection_form_sub_le, a FROZEN unit probe's Rayleigh quotient along
-- the curve equal to the base quotient plus 2s <v, [K,P] v> with error at most
-- 8 s^2 ||K||_F^2: Cauchy-Schwarz, the shipped resolvent contraction, and the fact that an
-- orthogonal projection contracts.  No operator norm, no eigenvalue, no derivative and no
-- differentiability API appears anywhere in the file.  (iii) WEYL IS NOT CONSUMED, contrary
-- to what honesty (a) predicted: Gtz.IsChartInactiveStrict hands back a PROBE rather than an
-- eigenvalue, so the same frozen-probe estimate covers the inactive blocks and uniformity is
-- a Finset minimum of finitely many positive slacks.  Gtz.chartTangentSkew_commutator is
-- [K, P] = (1/2) Pdot exactly when the direction's two diagonal blocks vanish, which IS
-- Gtz.IsChartTangent, so the curve realises the prescribed direction and the first-order
-- term is the SHIPPED Gtz.chartTangentSlope.  The descent lemma
-- Gtz.exists_chartTangentCurve_descent then lands
-- Gtz.isChartTightCovering_of_localMinimum -- LOCAL minimality suffices, by the entrywise
-- Lipschitz estimate Gtz.sq_chartCayleyProjection_sub_entry_le -- with the global form its
-- corollary, exactly on the shipped Gtz.IsChartTightCovering, which the shipped Gordan
-- exchange already turns into the strong multiplier bundle.  ADMISSIBILITY IS DERIVED:
-- Gtz.isChartArgmaxValue_of_isChartInactiveStrict gives Gtz.IsChartArgmaxValue -- the
-- hypothesis every exclusion, both value floors and every class closure in this layer
-- consumes -- from the inactive side condition plus one tight direction per active block,
-- and Gtz.chartTetraProjection_isChartArgmaxValue proves the shipped (4,3) tetrahedron
-- ADMISSIBLE outright, which the note at Gtz/Quantitative/ChartInstances.lean:95-96 says of
-- none of its three witnesses.  THREE THINGS ARE NOT ESTABLISHED AND MUST NOT BE READ IN.
-- (1) exists_tightDir -- a tight eigenvector at a block where lambda_min(W[C]) EQUALS the
-- value, which is the spectral theorem on a subblock -- is CARRIED AS A HYPOTHESIS, visible
-- in the printed statement of
-- Gtz.exists_isChartStationaryData_and_isChartArgmaxValue_of_globalMinimum as a per-active-
-- block existential standing beside Gtz.IsChartInactiveStrict; the honest reading of that
-- theorem is minimality PLUS those two.  (2) ATTAINMENT is not proved here; it is S1, in
-- Gtz.Reduction.ChartAttainment, and NO COMPOSITION THEOREM CHAINS THE TWO -- this module
-- does not import that one, S1 speaks of Gtz.chartObjective on Gtz.ChartPoint while S3's
-- minimality hypothesis is Gtz.HasChartDominatingSubsetAtValue on raw moved charts, and
-- nothing in the repository identifies the two.  The chain is three separate links and the
-- missing weld is named here rather than papered over.  (3) NO CLAIM ABOUT ANY PAPER-SIDE
-- conditional theorem is made or implied.  IT CLOSES NO CELL, and the reason is structural:
-- the condition derived is Gtz.IsChartTightCovering, which honesty (c) of
-- ChartStrongStationary records HOLDS at the (4,2) SIC, the (6,3) trine and the (9,3) Hesse
-- configuration, where every active tight eigenvalue is SIMPLE.  A necessary condition MUST
-- accept genuine minima; that is correct behaviour and not a defect.  What it means is that
-- this file contains no realness ingredient, cannot separate the fields, and must never be
-- advertised as a route to (6,3) or (7,3)
#print axioms Gtz.chartFrobeniusSquare
#print axioms Gtz.chartFrobeniusSquare_nonneg
#print axioms Gtz.mulVec_dotProduct_self_le_chartFrobeniusSquare
#print axioms Gtz.abs_le_of_sq_le_sq_of_nonneg
#print axioms Gtz.dotProduct_mulVec_skew_self_eq_zero
#print axioms Gtz.dotProduct_mulVec_nonneg_of_symmetricIdempotent
#print axioms Gtz.dotProduct_mulVec_le_self_of_symmetricIdempotent
#print axioms Gtz.mulVec_dotProduct_self_le_of_symmetricIdempotent
#print axioms Gtz.chartCayleyDenominator
#print axioms Gtz.transpose_chartCayleyDenominator
#print axioms Gtz.chartCayleyDenominator_mulVec
#print axioms Gtz.coercive_chartCayleyDenominator
#print axioms Gtz.isUnit_det_chartCayleyDenominator
#print axioms Gtz.inverse_chartCayleyDenominator_contraction
#print axioms Gtz.chartCayley
#print axioms Gtz.chartCayleyDenominator_mul_chartCayleyDenominator
#print axioms Gtz.chartCayleyDenominator_mul_comm
#print axioms Gtz.inverse_chartCayleyDenominator_mul_comm
#print axioms Gtz.transpose_chartCayley
#print axioms Gtz.chartCayley_transpose_mul_self
#print axioms Gtz.chartCayley_mul_transpose_self
#print axioms Gtz.transpose_chartCayley_eq_two_smul_inverse_sub_one
#print axioms Gtz.chartCayleyProjection
#print axioms Gtz.transpose_chartCayleyProjection
#print axioms Gtz.chartCayleyProjection_mul_self
#print axioms Gtz.trace_chartCayleyProjection
#print axioms Gtz.smul_mulVec_eq_smul_mulVec
#print axioms Gtz.dotProduct_mulVec_comm_of_symmetric
#print axioms Gtz.dotProduct_mulVec_commutator_eq
#print axioms Gtz.chartCayleyPull
#print axioms Gtz.chartCayleyPull_dotProduct_self_le
#print axioms Gtz.chartCayleyPull_sub_eq
#print axioms Gtz.chartCayleyOffset
#print axioms Gtz.chartCayleyOffset_eq
#print axioms Gtz.neg_smul_dotProduct_self
#print axioms Gtz.chartCayleyProjection_form_eq
#print axioms Gtz.abs_chartCayleyProjection_form_sub_le
#print axioms Gtz.chartCayley_mulVec_dotProduct_self
#print axioms Gtz.chartCayleyOffset_dotProduct_self_le
#print axioms Gtz.add_dotProduct_self_le_two_mul
#print axioms Gtz.chartCayleyProjection_sub_mulVec
#print axioms Gtz.sq_chartCayleyProjection_sub_entry_le
#print axioms Gtz.chartTangentSkew
#print axioms Gtz.transpose_chartTangentSkew
#print axioms Gtz.chartTangentSkew_commutator
#print axioms Gtz.chartTangentCurve
#print axioms Gtz.chartCayleyWeight
#print axioms Gtz.sum_chartCayleyWeight_eq
#print axioms Gtz.dotProduct_chartStationaryGap_mulVec_eq
#print axioms Gtz.abs_chartTangentCurve_gap_form_sub_le
#print axioms Gtz.ChartBlockDominatesAtValue
#print axioms Gtz.HasChartDominatingSubsetAtValue
#print axioms Gtz.not_chartBlockDominatesAtValue_of_probe
#print axioms Gtz.dotProduct_chartStationaryGap_mulVec_of_isChartTightVector
#print axioms Gtz.exists_pos_le_forall_mem
#print axioms Gtz.abs_le_one_add_of_sq_le
#print axioms Gtz.chartWeightCap
#print axioms Gtz.chartWeightCap_nonneg
#print axioms Gtz.abs_directionWeight_le_chartWeightCap
#print axioms Gtz.chartSlopeCap
#print axioms Gtz.chartSlopeCap_nonneg
#print axioms Gtz.abs_chartTangentSlope_le_chartSlopeCap
#print axioms Gtz.exists_chartTangentCurve_descent
#print axioms Gtz.isChartArgmaxValue_of_isChartInactiveStrict
#print axioms Gtz.isChartTightCovering_of_localMinimum
#print axioms Gtz.isChartTightCovering_of_globalMinimum
#print axioms Gtz.isChartStrongStationaryData_of_globalMinimum
#print axioms Gtz.exists_isChartStationaryData_and_isChartArgmaxValue_of_globalMinimum
#print axioms Gtz.chartCayley_zero
#print axioms Gtz.chartCayleyProjection_zero
#print axioms Gtz.chartTangentCurve_zero
#print axioms Gtz.chartCayleyWeight_zero
#print axioms Gtz.chartTetraProjection_isChartInactiveStrict
#print axioms Gtz.chartTetraProjection_isChartArgmaxValue

-- THE SECOND-ORDER STRENGTHENING OF THE CHART LAYER IS FIELD-GENERIC AND CLOSES NO CELL.
-- Recorded here, in the ledger, because it is the verdict on a route this layer's three
-- honesty blocks invite and it must not be rediscovered an eighth time.  It is PROSE, it is
-- a statement about work done OUTSIDE Lean, and nothing below it is mechanized.  No
-- Prop-valued second-order condition exists in this repository and none should be added
-- while this note stands.
--
-- THE ROUTE.  Honesty (c) of Gtz.Quantitative.ChartStrongStationary observes that the
-- FIRST-order strengthening cannot separate the fields, since at the (4,2) SIC, the (6,3)
-- trine and the (9,3) Hesse configuration every active tight eigenvalue is simple and the
-- strong system holds exactly when the weak one does.  The natural next hypothesis is
-- SECOND-order minimality: minimise G = max_C lambda_min(W[C]) over the symmetric
-- idempotents of trace rank crossed with the simplex, along the Cayley curve S3 builds, and
-- ask whether the multiplier-weighted second variation restricted to the critical cone can
-- exclude a negative value at (6,3).  The rotation algebra is so(m) over R and u(m) over C,
-- 15 against 36 dimensions at m = 6, so second order is the first place in this project
-- where a condition COULD see the field.
--
-- IT DOES NOT.  [MEASURED, outside Lean, not mechanized; 60-digit mpmath from the
-- repository's own Gtz.Complex.SharpConstantLedger data, with the balanced multiplier
-- SOLVED rather than assumed.]  At the (6,3) complex trine the chart is Hermitian idempotent
-- of trace 3 to residual 1.6e-61; G over all 20 triples equals the chart value to 2.0e-61,
-- so the admissibility defect is EXACTLY ZERO; 18 triples are active, every active tight
-- eigenvalue is SIMPLE with gap sqrt5/6, and the uniform 1/18 multiplier is balanced to
-- 6.5e-62.  The shipped Gtz.trace_projection_mul_multiplier_of_isChartStationaryData holds
-- there VERBATIM over C.  The second-variation form has inertia (0 negative, 5 zero, 5
-- positive) on the whole 10-dimensional critical cone, robustly across the balanced-
-- multiplier polytope -- so it is POSITIVE SEMIDEFINITE, and a PSD form restricts to a PSD
-- form on every subspace, whence no direction is load-bearing for acceptance and nothing
-- lacking a real analogue is consumed.  The trine is moreover a LOCAL MINIMUM of the complex
-- chart objective [MEASURED: 4000 random unit tangent rays at five step sizes give
-- min(G(moved) - value) = +3.5e-4 > 0, and 40 descents seeded at the trine do not leave it],
-- so adding local minimality does not dodge the obstruction.  The same form is PSD at the
-- (4,2) SIC, inertia (0,3,3).
--
-- THE KILL, stated as the package it refutes.  Every ingredient of
-- {admissibility, chart stationarity with a balanced multiplier, tightness, all-simple
-- active blocks, the -1/size, FLOOR-CB and FLOOR-E2 value floors, the second variation
-- positive semidefinite on the critical cone, local minimality} is FIELD-GENERIC -- the
-- second-variation formula contains only squared moduli, no argument, no cycle and no
-- Bargmann invariant -- and the package is SATISFIED at the complex trine at chart value
-- (2 - sqrt5)/6, the root of 36 v^2 - 24 v - 1 [DERIVED, exact], which is Gtz.windowChartValue
-- and lies strictly inside both (-1/6, 0) and the floored window (-4/27, 0).  So any proof
-- of the (6,3) interior exclusion from that package would prove the same statement over C,
-- where it is FALSE.  The route retires the last unused hypothesis in this layer.
--
-- THE TWO ESCAPES, both closed.  (1) Imposing the COMPLEX condition at a REAL point IS
-- field-sensitive and does bite [MEASURED: at the real (6,3) split tetrahedron the real
-- critical cone has dimension 5 with the form identically zero, while the complex cone has
-- dimension 14 = 5 + 9 with four strictly negative eigenvalues, the nine extra directions
-- being the imaginary Grassmannian block].  But it is not NECESSARY for a real
-- counterexample: a real minimiser of G over the real domain need not be a complex local
-- minimum, and Gtz.not_complexGtzWeighted_of_rank_add_two_le_size proves real ties never
-- are.  (2) Restricting to tight multiplicity greater than one is VACUOUS at the all-simple
-- trine, so it passes the complex gate only by being silent there, and for exactly that
-- reason cannot touch an all-simple real candidate -- which is where the shipped window
-- witness Gtz.windowChartProjection and any generic counterexample live.  It would close
-- only the multiplicity stratum, which the shipped strong first-order system already closes.
--
-- WHAT IS ALSO REFUTED, so that no one re-derives it.  The brief-level intuition that the
-- complex Grassmannian's extra curvature directions make a minimum EASIER to sustain points
-- the wrong way for a NECESSARY condition: more tangent directions means more critical
-- directions to test and more balance equations, so the complex condition is strictly
-- STRONGER, which is what the real split tetrahedron measures.  The hope that the shipped
-- second-order flexibility of the (7,3) tie stratum
-- (Gtz.Ties.StratumFirstOrder) is a non-degeneracy the operator can exploit is dead: the form
-- is IDENTICALLY ZERO on the 6-dimensional critical cone at splitSevenDesign, as it is at the
-- (4,3) tetrahedron and at the (6,3) split tetrahedron at four weight splits, for EVERY
-- balanced multiplier -- extremal ties are second-order PLATEAUX, so the tie gate passes with
-- exact equality and NO strict or uniform second-order margin bound can exist.  Finally: the
-- CONCAVITY TERM of that second variation is ALREADY SHIPPED, in
-- Gtz/Reduction/StrengthenedInductionHypothesis.lean, as the "rate of a positive semidefinite
-- form along a direction" section -- the scalar solution . direction at any solution of
-- form *v solution = direction, which that section's own header calls "direction^T W^+
-- direction without a pseudo-inverse".  Gtz.solutionRate_unique is its well-definedness and
-- Gtz.solutionRate_nonneg its sign, and Gtz.rankOneForm_le_of_solutionRate_le is advertised
-- as needing "no inverse, no pseudo-inverse, no eigenvalues, and no positive-definiteness" --
-- exactly the resolvent-free quadratic rate the second-order derivations re-derived twice in
-- one campaign.  There is NO declaration named Gtz.solutionRate: the object is a scalar and
-- the kit is the Gtz.solutionRate_* family, which is why every grep for a resolvent or a
-- pseudo-inverse missed it.

-- Gtz/Quantitative/HeavyAtomDichotomy.lean -- THE TIE GATE BINDS AT EVERY LEVERAGE SCALE.
-- WHAT IS NOT HERE, first, because the file name invites the opposite reading:
-- Gtz.HeavyAtomCovering is NOT inhabited at any cap and NOT refuted at any cap, no cap is
-- stated, and nothing below discharges the hypothesis of
-- Gtz.discriminantCovering_of_heavyAtomCovering_of_capped or of
-- Gtz.rank_three_of_heavyAtomCovering_of_capped.  Both stay CONDITIONAL, the
-- compactification is not delivered, and Gtz.DiscriminantCovering 7 -- hence
-- Gtz.GtzWeightedAll 3, hence the 1997 statement at rank three -- is exactly as open after
-- this file as before it.
--
-- WHAT IS ESTABLISHED.  Load the shipped class-tie section Gtz.splitClassDesign at the
-- (2,2,2,1) partition Gtz.sevenIntoFourBalanced with spikeWeight on the singleton class and
-- the rest split evenly over the other six atoms.  The result is an exact Gtz.IsTie at every
-- admissible spikeWeight (Gtz.spikeClassTieDesign_isTie), all-heavy
-- (Gtz.spikeClassTieDesign_allHeavy), with the singleton atom's leverage equal to
-- (2 + spikeWeight)/(3*spikeWeight) (Gtz.spikeClassTieDesign_spike_leverage) -- which is cap
-- exactly at spikeWeight = 2/(3*cap - 1).  So for EVERY cap there is an all-heavy weighted
-- (7,3) design carrying an atom of leverage at least cap at which NO 3-subset dominates
-- STRICTLY (Gtz.exists_allHeavy_isTie_seven_with_leverage_ge).  The single computation
-- underneath is the shipped corank-one identity k*t*l = (k-1) + t solved for the leverage.
--
-- THE CONSEQUENCES, all of them constraints on how the brick could ever be proved.  Every
-- STRICT reading of the heavy-atom brick is false at every cap
-- (Gtz.not_heavyAtomStrictCovering), so no barrier, concentration, interlacing or strictly
-- positive Positivstellensatz argument can reach it; the same holds for the capped half at
-- every cap above three (Gtz.not_cappedStrictCovering_of_three_lt), so the zero-margin
-- burden sits on BOTH hypotheses of the corollary at once and compactifying MOVES the
-- tightness rather than removing it.  Gtz.heavyAtomCovering_of_heavyAtomStrictCovering
-- records which of the two is the stronger statement, so nobody proves the wrong one.
--
-- WHAT IS RETIRED.  The reading "the (7,3) ties this repository names top out at leverage
-- five, so the tie gate is vacuous at large cap" is a MEASUREMENT ON THE CATALOGUE, never a
-- fact about the stratum, and the curve above refutes it: the (7,3) tie stratum carries
-- UNBOUNDED leverage.  The tie gate is vacuous nowhere.  At spikeWeight = 1/4 every leverage
-- is exactly three (Gtz.spikeClassTieDesign_quarter_spike_leverage), the uniform point; that
-- it IS the split tetrahedron up to rotation and relabelling is NOT mechanized, the two
-- constructions coming from different sections, so the curve is stated on its own terms.
--
-- TWO ROUTES DELIBERATELY NOT TAKEN, because neither is true as stated.  The RESIDUE route
-- ("a spike of weight w -> 0 leaves the other six carrying weight -> 1, hence nearly a
-- design") fails because the residue of an atom of weighted leverage tau is I - tau*u u^T,
-- whose deficit is tau, and tau is free in (0,1] INDEPENDENTLY of the leverage -- a large cap
-- does not make the residue close to a design.  The DEFLATION route is circular at (7,3): its
-- heavy branch consumes Gtz.GtzWeighted 6 3, which is open.
#print axioms Gtz.simplexTieAtom_leverage_identity
#print axioms Gtz.one_lt_leverage_simplexTieAtom
#print axioms Gtz.leverage_simplexTieAtom_eq
#print axioms Gtz.spikeClassWeight
#print axioms Gtz.spikeClassWeight_zero
#print axioms Gtz.spikeClassWeight_apply
#print axioms Gtz.spikeClassWeight_pos
#print axioms Gtz.spikeClassWeight_sum
#print axioms Gtz.classTotalWeight_spikeClassWeight_zero
#print axioms Gtz.spikeClassTieDesign
#print axioms Gtz.spikeClassTieDesign_weight
#print axioms Gtz.spikeClassTieDesign_atom
#print axioms Gtz.spikeClassTieDesign_isTie
#print axioms Gtz.spikeClassTieDesign_allHeavy
#print axioms Gtz.spikeClassTieDesign_spike_leverage
#print axioms Gtz.exists_allHeavy_isTie_seven_with_leverage_ge
#print axioms Gtz.spikeClassTieDesign_quarter_spike_leverage
#print axioms Gtz.HeavyAtomStrictCovering
#print axioms Gtz.heavyAtomCovering_of_heavyAtomStrictCovering
#print axioms Gtz.not_heavyAtomStrictCovering
#print axioms Gtz.CappedStrictCovering
#print axioms Gtz.not_cappedStrictCovering_of_three_lt

-- Gtz/Quantitative/SignReadingCell.lean -- A DECISION CELL THAT SPENDS THE MAGNITUDE OF THE
-- ORIENTED PAIRING PRODUCT.  Gtz.Quantitative.GoodTripleGraph proves no certificate reading
-- only SQUARED pairings can close the covering: every such family lies inside the exact
-- closure Gtz.IsSignBlindGoodTriple, refuted at the frontier size, while
-- Gtz.icosaDesign_dominates_iff_pairingProduct shows the discarded verdict is carried by the
-- ORIENTATION of p_ab p_ac p_bc alone.  Gtz.dominates_of_coherentPairings reads that sign and
-- then throws the MAGNITUDE away, its second hypothesis being term for term 0 <= excessGap.
-- Gtz.dominates_of_productFloor spends the magnitude: two compatible pivot minors, a LOWER
-- bound productFloor*(u_p u_a u_b) on the oriented product, and a sign-blind aggregate
-- RELAXED by exactly twice that amount.  The determinant leg is then one addition, the trace
-- leg the sum of the two pivot minors.  Every multiplier has degree zero and no hypothesis is
-- strict, which is mandatory: (7,3) sits on the ceiling, so if the conjecture holds there it
-- holds with zero margin.  At productFloor = 0 the cell CONTAINS the shipped coherent-sign
-- cell (Gtz.isInCell_productFloorCell_zero_of_coherentPairings), so productFloor > 0 is a
-- genuine extension and not a re-parameterisation.
--
-- WHAT IT IS NOT, recorded as a theorem rather than as prose because two independent passes
-- of one campaign asserted the opposite.  It is NOT the first DecisionCell here --
-- Gtz.tautologicalCell and Gtz.tautologicalCell_discharges are shipped and audited.  It is
-- NOT the first shipped cell to read the sign of the pairing product and NOT the first to
-- reach excessGap < 0: Gtz.dominates_of_twoMomentGap_nonneg already does BOTH, since
-- twoMomentGap = 4*e3 + 4*e2 - e1^2 carries the oriented product inside e3 and imposes no
-- sign on excessGap at all.  Gtz.twoMomentCell_reaches_negative_excessGap is the six-scalar
-- witness: at leverages (4,4,4) and pairings (2,2,2) the shipped gap is +7 >= 0 with total
-- leverage 12 > 3, so the shipped cell FIRES while the sign-blind part of the tie leg is -9;
-- flipping one pairing to -2 sends the gap to -121, so that cell is genuinely sign-sensitive
-- too.  Three sentences die on that witness and none of them may be restated: that the union
-- of the shipped cells is {excessGap >= 0} intersect {tie >= 0}; that this file is the first
-- or only cell reaching excessGap < 0; that Gtz.dominates_of_coherentPairings is the only
-- shipped sign-reading cell.  What IS new is the particular trade, and that this is the first
-- NON-TAUTOLOGICAL cell family wrapped into the DecisionCell interface so that
-- Gtz.discriminantCovering_of_atlas can consume it
-- (Gtz.doesAtlasDischarge_of_forall_productFloorCell).
--
-- MEASURED COVERAGE -- A MEASUREMENT, NEVER A THEOREM, AND NOT A COVERING.  On two
-- optimiser-seeded pools of exactified all-heavy (7,3) designs the union of the shipped cell
-- library INCLUDING the two-moment cell covers 10311/10796 = 0.95508 of the first pool and
-- 10422/10800 = 0.96500 of the second; the product-floor family at the fixed rational grid
-- {1/8, 1/4, 3/8} covers 485/485 and 378/378 of the two residues.  Every number is a
-- measurement on a pool an optimiser produced from ONE basin, not a statement about the
-- parameter space.  DoesAtlasCover is untouched, no atlas built from this family is proved to
-- cover, and the true residue survives at exactly rational points: the (6,3) graphic design
-- of K4 and its (7,3) atom split have every leverage three, Gram entries in {3, +-3/2, 0},
-- strictly dominating triples, and NO shipped cell firing at any triple.  That census is not
-- mechanized here.  Gtz.isSignBlindGoodTriple_of_dominates_of_product_nonpos records the
-- complementary half in three lines: a dominating triple with NONPOSITIVE oriented product is
-- sign-blind-good outright, so every dominating triple the sign-blind family misses has a
-- strictly positive oriented product -- exactly the quantity the product floor bounds below.
#print axioms Gtz.dominates_of_productFloor
#print axioms Gtz.productFloorCell
#print axioms Gtz.isInCell_productFloorCell_iff
#print axioms Gtz.doesCellDischarge_productFloorCell
#print axioms Gtz.doesAtlasDischarge_of_forall_productFloorCell
#print axioms Gtz.isInCell_productFloorCell_zero_of_coherentPairings
#print axioms Gtz.isSignBlindGoodTriple_of_dominates_of_product_nonpos
#print axioms Gtz.twoMomentCell_reaches_negative_excessGap

-- The sign layer: obtuse sign forcing and the triangle product, the elliptope bracket read as
-- a closed interval in one coordinate, the rho normal form that turns domination of a triple
-- into a correlation matrix, the frame conservation law on unit atoms, the domination gates
-- built from orthogonal frames and Ramsey, and the sign-selected aggregate that spends five
-- atoms.  `Gtz.unitDirection` below is the vector-level normalisation from DominationGates;
-- RhoNormalForm's design-indexed specialisation is `Gtz.atomUnitDirection`, renamed at
-- integration because the two modules landed the same global name.

-- Gtz/LinAlg/SignForcing.lean
#print axioms Gtz.dotProduct_self_nonneg_fintype
#print axioms Gtz.eq_zero_of_dotProduct_self_eq_zero_fintype
#print axioms Gtz.IsPairwiseObtuse
#print axioms Gtz.forall_coef_nonpos_of_obtuseRelation
#print axioms Gtz.forall_coef_eq_zero_of_obtuseRelation
#print axioms Gtz.linearIndependent_of_isPairwiseObtuse_of_testVector
#print axioms Gtz.card_le_of_isPairwiseObtuse_of_testVector
#print axioms Gtz.card_le_succ_of_isPairwiseObtuse
#print axioms Gtz.card_le_succ_of_isPairwiseObtuse_on
#print axioms Gtz.tetraAtom_dotProduct_eq_neg_one_of_ne
#print axioms Gtz.isPairwiseObtuse_tetraAtom
#print axioms Gtz.dotProduct_constant
#print axioms Gtz.obtuseSimplexAtom
#print axioms Gtz.obtuseSimplexAtom_dotProduct_some_some
#print axioms Gtz.obtuseSimplexAtom_dotProduct_some_none
#print axioms Gtz.isPairwiseObtuse_obtuseSimplexAtom
#print axioms Gtz.triangleProduct
#print axioms Gtz.triangleProduct_comm_left
#print axioms Gtz.triangleProduct_smul
#print axioms Gtz.triangleProduct_smul_of_sq_eq_one
#print axioms Gtz.triangleProduct_smul_pos_iff
#print axioms Gtz.switchSign
#print axioms Gtz.switchSign_sq_eq_one
#print axioms Gtz.switchSign_ne_zero
#print axioms Gtz.switchSign_base
#print axioms Gtz.switchSign_mul_basePairing_neg
#print axioms Gtz.exists_pos_triangleProduct_of_card_ge
#print axioms Gtz.exists_nonneg_triangleProduct_of_card_ge
#print axioms Gtz.triangleProduct_tetraAtom_eq_neg_one
#print axioms Gtz.not_exists_pos_triangleProduct_tetraAtom
#print axioms Gtz.realifyComplexVector
#print axioms Gtz.dotProduct_realifyComplexVector
#print axioms Gtz.IsPairwiseObtuseComplex
#print axioms Gtz.card_le_two_mul_add_one_of_isPairwiseObtuseComplex
#print axioms Gtz.complexifyRealVector
#print axioms Gtz.realifyComplexVector_complexifyRealVector
#print axioms Gtz.isPairwiseObtuseComplex_complexifiedSimplex
#print axioms Gtz.exists_pos_realTriangleProduct_of_complex_card_ge
#print axioms Gtz.elliptopeBracket_nonneg_of_coherent_of_sq_le_half
#print axioms Gtz.exists_elliptopeBracket_neg_of_half_lt
#print axioms Gtz.normalizedPairing_sq_le_half_iff
#print axioms Gtz.dominates_of_coherentHalfBoxTriangle
#print axioms Gtz.icosaDesign_dominates_of_coherentPairings
#print axioms Gtz.exists_normalizedPairing_sq_gt_half_of_not_dominates
#print axioms Gtz.exists_pos_atomPairingProduct_of_five_atoms
#print axioms Gtz.exists_normalizedPairing_sq_gt_half_of_five_atoms
#print axioms Gtz.exists_abs_normalizedPairing_gt_of_five_atoms

-- Gtz/LinAlg/ElliptopeInterval.lean
#print axioms Gtz.elliptopeBracket_eq_completedSquare_third
#print axioms Gtz.elliptopeBracket_eq_completedSquare_first
#print axioms Gtz.elliptopeBracket_eq_completedSquare_second
#print axioms Gtz.elliptopeBracket_swap_firstSecond
#print axioms Gtz.elliptopeBracket_swap_secondThird
#print axioms Gtz.elliptopeBracket_swap_firstThird
#print axioms Gtz.elliptopeBracket_neg_firstSecond
#print axioms Gtz.elliptopeBracket_neg_firstThird
#print axioms Gtz.elliptopeBracket_neg_secondThird
#print axioms Gtz.elliptopeBracket_abs
#print axioms Gtz.elliptopeBracket_abs_of_coherent
#print axioms Gtz.elliptopeBracket_discriminant
#print axioms Gtz.rootUpper
#print axioms Gtz.rootLower
#print axioms Gtz.rootLower_add_rootUpper
#print axioms Gtz.rootLower_mul_rootUpper
#print axioms Gtz.rootLower_le_rootUpper
#print axioms Gtz.rootUpper_le_one
#print axioms Gtz.neg_one_le_rootLower
#print axioms Gtz.elliptopeBracket_eq_neg_mul_rootFactors
#print axioms Gtz.elliptopeBracket_nonneg_iff_mem_rootInterval
#print axioms Gtz.elliptopeBracket_pos_iff_mem_openRootInterval
#print axioms Gtz.elliptopeBracket_eq_zero_iff_eq_root
#print axioms Gtz.elliptopeBracket_rootUpper_eq_zero
#print axioms Gtz.elliptopeBracket_rootLower_eq_zero
#print axioms Gtz.IsCompatibleTriple
#print axioms Gtz.IsElliptopePoint
#print axioms Gtz.sq_le_one_of_two_and_bracket_nonneg
#print axioms Gtz.isElliptopePoint_iff_two_sq_le_one
#print axioms Gtz.isElliptopePoint_neg_firstSecond
#print axioms Gtz.isElliptopePoint_neg_firstThird
#print axioms Gtz.isElliptopePoint_neg_secondThird
#print axioms Gtz.isElliptopePoint_abs_iff_of_coherent
#print axioms Gtz.isElliptopePoint_iff_mem_rootInterval
#print axioms Gtz.isElliptopePoint_iff_sq_le_one_and_bracket_nonneg
#print axioms Gtz.elliptopeBracket_nonneg_of_sq_le_quarter
#print axioms Gtz.elliptopeBracket_nonneg_of_abs_le_half
#print axioms Gtz.isElliptopePoint_of_sq_le_quarter
#print axioms Gtz.exists_sq_gt_quarter_of_elliptopeBracket_neg
#print axioms Gtz.elliptopeBracket_eq_zero_iff_mercedes
#print axioms Gtz.elliptopeBracket_eq_zero_iff_mercedesPoint
#print axioms Gtz.elliptopeBracket_mercedes_allNegative
#print axioms Gtz.elliptopeBracket_mercedes_firstNegative
#print axioms Gtz.elliptopeBracket_mercedes_secondNegative
#print axioms Gtz.elliptopeBracket_mercedes_thirdNegative
#print axioms Gtz.elliptopeBracket_boxVertex_allPositive
#print axioms Gtz.elliptopeBracket_symmetricNegative
#print axioms Gtz.elliptopeBracket_neg_of_half_lt
#print axioms Gtz.elliptopeBracket_equilateral
#print axioms Gtz.elliptopeBracket_equilateral_nonneg_iff
#print axioms Gtz.isElliptopePoint_equilateral_iff
#print axioms Gtz.elliptopeBracket_of_sq_eq
#print axioms Gtz.elliptopeBracket_nonneg_iff_of_sq_eq
#print axioms Gtz.elliptopeBracket_threeHalves_eq_one
#print axioms Gtz.not_isElliptopePoint_threeHalves
#print axioms Gtz.IsWildTriple
#print axioms Gtz.IsCoherentFailingTriple
#print axioms Gtz.IsFrustratedFailingTriple
#print axioms Gtz.isWildTriple_iff_not_isCompatibleTriple
#print axioms Gtz.ElliptopeClass
#print axioms Gtz.HasElliptopeClass
#print axioms Gtz.not_isWildTriple_of_isElliptopePoint
#print axioms Gtz.not_isWildTriple_of_isCoherentFailingTriple
#print axioms Gtz.not_isWildTriple_of_isFrustratedFailingTriple
#print axioms Gtz.not_isCoherentFailingTriple_of_isElliptopePoint
#print axioms Gtz.not_isFrustratedFailingTriple_of_isElliptopePoint
#print axioms Gtz.not_isFrustratedFailingTriple_of_isCoherentFailingTriple
#print axioms Gtz.exists_hasElliptopeClass
#print axioms Gtz.hasElliptopeClass_unique
#print axioms Gtz.existsUnique_hasElliptopeClass
#print axioms Gtz.not_isElliptopePoint_iff_failingClass
#print axioms Gtz.sum_sq_gt_one_of_coherentFailure_of_least
#print axioms Gtz.coherentFailure_needs_least
#print axioms Gtz.exists_pairSumSq_gt_one_of_isCoherentFailingTriple
#print axioms Gtz.exists_sq_gt_half_of_isCoherentFailingTriple
#print axioms Gtz.exists_sq_gt_quarter_of_isFrustratedFailingTriple
#print axioms Gtz.lt_rootLower_of_failure_of_least
#print axioms Gtz.abs_lt_rootLower_of_isCoherentFailingTriple
#print axioms Gtz.coherentFailure_rootLower_needs_gauge
#print axioms Gtz.elliptopeBracket_zeroPair
#print axioms Gtz.elliptopeBracket_zeroPair_neg_iff
#print axioms Gtz.isCoherentFailingTriple_zeroPair
#print axioms Gtz.isFrustratedFailingTriple_equilateral
#print axioms Gtz.isCompatiblePair_iff_normalizedPairing_sq_le_one
#print axioms Gtz.isElliptopeGoodTriangle_iff_isElliptopePoint
#print axioms Gtz.dominates_triple_iff_isElliptopePoint
#print axioms Gtz.dominates_triple_iff_mem_rootInterval
#print axioms Gtz.exists_not_isBoxGoodPair_of_not_dominates
#print axioms Gtz.not_dominates_triple_iff_failingClass
#print axioms Gtz.exists_normalizedPairing_sq_gt_half_of_coherent_not_dominates

-- Gtz/Design/RhoNormalForm.lean
#print axioms Gtz.diagonalSqrtScaling
#print axioms Gtz.correlationOf
#print axioms Gtz.correlationOf_apply
#print axioms Gtz.correlationOf_diagonal_eq_one
#print axioms Gtz.correlationOf_transpose
#print axioms Gtz.diagonalSqrtScaling_transpose
#print axioms Gtz.isUnit_det_diagonalSqrtScaling
#print axioms Gtz.eq_congr_correlationOf
#print axioms Gtz.posSemidef_iff_posSemidef_correlationOf
#print axioms Gtz.posDef_iff_posDef_correlationOf
#print axioms Gtz.det_eq_prod_diagonal_mul_det_correlationOf
#print axioms Gtz.correlationMatrixThree
#print axioms Gtz.correlationMatrixThree_transpose
#print axioms Gtz.det_correlationMatrixThree
#print axioms Gtz.posSemidef_correlationMatrixThree_iff
#print axioms Gtz.elliptopeBracket_incompatible_boundary
#print axioms Gtz.not_posSemidef_correlationMatrixThree_of_incompatible_boundary
#print axioms Gtz.tripleGapMatrix
#print axioms Gtz.tripleGapMatrix_transpose
#print axioms Gtz.tripleGapMatrix_eq_gram_sub_one
#print axioms Gtz.det_tripleGapMatrix
#print axioms Gtz.det_subsetSum_sub_one_eq_discriminantTie
#print axioms Gtz.dominates_triple_iff_posSemidef_tripleGapMatrix
#print axioms Gtz.posDef_subsetSum_sub_one_iff_posDef_tripleGapMatrix
#print axioms Gtz.excessSqrtDiagonal
#print axioms Gtz.excessSqrtDiagonal_transpose
#print axioms Gtz.excessSqrtDiagonal_eq_diagonalSqrtScaling
#print axioms Gtz.correlationOf_tripleGapMatrix
#print axioms Gtz.tripleGapMatrix_diagonal_pos
#print axioms Gtz.tripleGapMatrix_eq_congr_correlationMatrixThree
#print axioms Gtz.dominates_triple_iff_posSemidef_correlationMatrixThree
#print axioms Gtz.posDef_subsetSum_sub_one_iff_posDef_correlationMatrixThree
#print axioms Gtz.dominates_triple_iff_isCompatibleTriangle_and_elliptopeBracket_nonneg
#print axioms Gtz.atomUnitDirection
#print axioms Gtz.directionCosine
#print axioms Gtz.amplification
#print axioms Gtz.leverage_eq_heavyExcess_add_one
#print axioms Gtz.leverage_pos_of_heavyExcess_pos
#print axioms Gtz.amplification_sq
#print axioms Gtz.amplification_sq_eq_one_add_inv_heavyExcess
#print axioms Gtz.one_lt_amplification
#print axioms Gtz.amplification_eq_sqrt_div
#print axioms Gtz.atomUnitDirection_dotProduct_self
#print axioms Gtz.atomUnitDirection_dotProduct
#print axioms Gtz.abs_directionCosine_le_one
#print axioms Gtz.normalizedPairing_eq_amplification_mul_directionCosine
#print axioms Gtz.abs_directionCosine_le_abs_normalizedPairing
#print axioms Gtz.abs_normalizedPairing_le_amplification_product
#print axioms Gtz.normalizedPairing_eq_amplification_product_of_atom_eq
#print axioms Gtz.tetraDesign_share
#print axioms Gtz.tetraDesign_amplification_sq
#print axioms Gtz.tetraDesign_directionCosine_zeroOne
#print axioms Gtz.tetraDesign_normalizedPairing_zeroOne
#print axioms Gtz.tetraDesign_normalizedPairing_zeroTwo
#print axioms Gtz.tetraDesign_normalizedPairing_oneTwo
#print axioms Gtz.tetraDesign_correlationMatrixThree
#print axioms Gtz.tetraDesign_elliptopeBracket_eq_zero
#print axioms Gtz.tetraDesign_posSemidef_correlationMatrixThree
#print axioms Gtz.tetraDesign_not_posDef_correlationMatrixThree
#print axioms Gtz.IsTiedTriple
#print axioms Gtz.isTiedTriple_iff_dominates_and_discriminantTie_eq_zero
#print axioms Gtz.isTiedTriple_iff_isCompatibleTriangle_and_elliptopeBracket_eq_zero
#print axioms Gtz.isTiedTriple_of_isTie
#print axioms Gtz.elliptopeBracket_eq_zero_of_isTie_of_dominates
#print axioms Gtz.tetraDesign_isTiedTriple

-- Gtz/Design/FrameConservation.lean
#print axioms Gtz.leverageOf_smul
#print axioms Gtz.eq_zero_of_leverageOf_eq_zero
#print axioms Gtz.atomMatrix_eq_zero_of_leverageOf_eq_zero
#print axioms Gtz.sum_coefficient_mul_atomOverlap_mul_atomOverlap
#print axioms Gtz.parseval_weighted_bilinear
#print axioms Gtz.sum_weight_mul_atomPairing_mul_atomPairing
#print axioms Gtz.unitAtom
#print axioms Gtz.atomMatrix_unitAtom
#print axioms Gtz.leverageOf_unitAtom
#print axioms Gtz.leverageOf_unitAtom_le_one
#print axioms Gtz.directionGram
#print axioms Gtz.directionGram_comm
#print axioms Gtz.directionGram_eq_scaled_atomPairing
#print axioms Gtz.directionGram_self
#print axioms Gtz.abs_directionGram_le_one
#print axioms Gtz.atomShare_smul_atomMatrix_unitAtom
#print axioms Gtz.sum_atomShare_smul_atomMatrix_unitAtom
#print axioms Gtz.frameLaw_bilinear
#print axioms Gtz.sum_atomShare_mul_one_sub_inv_leverage
#print axioms Gtz.leverageAmplification
#print axioms Gtz.leverageAmplification_sq
#print axioms Gtz.one_lt_leverageAmplification
#print axioms Gtz.inv_leverageAmplification_sq
#print axioms Gtz.sum_atomShare_mul_inv_leverageAmplification_sq
#print axioms Gtz.sum_atomShare_mul_inv_leverageAmplification_sq_three
#print axioms Gtz.sum_atomShare_mul_directionGram_mul_directionGram
#print axioms Gtz.directionGramMatrix
#print axioms Gtz.unitAtomRows
#print axioms Gtz.directionGramMatrix_eq_mul_transpose
#print axioms Gtz.posSemidef_directionGramMatrix
#print axioms Gtz.directionGramMatrix_mul_diagonal_atomShare_mul_self
#print axioms Gtz.sum_atomShare_mul_sq_directionGram
#print axioms Gtz.atomShare_add_sum_erase_atomShare_mul_sq_directionGram
#print axioms Gtz.sum_sdiff_atomShare_mul_directionGram_mul_directionGram
#print axioms Gtz.atomShare_pair_eq_one_or_directionGram_eq_zero
#print axioms Gtz.exists_directionGram_chain_ne_zero
#print axioms Gtz.atomPairing_eq_zero_of_atomShare_eq_one
#print axioms Gtz.atomShare_eq_one_iff_forall_atomPairing_eq_zero
#print axioms Gtz.rank_sub_one_sub_threshold_le_sum_atomShare
#print axioms Gtz.rank_sub_one_sub_threshold_le_sum_atomShare_filter
#print axioms Gtz.rank_sub_one_sub_threshold_le_card_heavySet
#print axioms Gtz.exists_excess_ge_of_lt_rank_sub_one
#print axioms Gtz.heavySet_nonempty_of_lt_rank_sub_one
#print axioms Gtz.sum_atomShare_le_one_of_light
#print axioms Gtz.HeavinessProfileAt
#print axioms Gtz.heavinessProfileAt_of_neg_one_le
#print axioms Gtz.not_heavinessProfileAt_of_lt_neg_one
#print axioms Gtz.rank_le_of_forall_leverage_le
#print axioms Gtz.le_rank_of_forall_le_leverage
#print axioms Gtz.forall_leverage_eq_rank_of_forall_rank_le
#print axioms Gtz.forall_leverage_eq_rank_of_forall_le_rank
#print axioms Gtz.forall_leverage_eq_three_of_forall_two_le_excess
#print axioms Gtz.exists_leverage_three_le
#print axioms Gtz.directionDesign
#print axioms Gtz.leverageOf_directionDesign_atom
#print axioms Gtz.leverageOf_tetraDesign_atom
#print axioms Gtz.atomShare_tetraDesign
#print axioms Gtz.leverageAmplification_sq_tetraDesign
#print axioms Gtz.sq_directionGram_tetraDesign_of_ne
#print axioms Gtz.sum_atomShare_mul_inv_leverageAmplification_sq_tetraDesign
#print axioms Gtz.forall_leverage_eq_three_tetraDesign

-- Gtz/Design/DominationGates.lean
#print axioms Gtz.sum_atomMatrix_eq_one_of_orthonormalFrame
#print axioms Gtz.card_image_of_injective_pick
#print axioms Gtz.unitDirection
#print axioms Gtz.unitDirection_dotProduct
#print axioms Gtz.unitDirection_dotProduct_self
#print axioms Gtz.unitDirection_dotProduct_eq_zero
#print axioms Gtz.leverage_smul_atomMatrix_unitDirection
#print axioms Gtz.subsetSum_image_sub_one_eq_sum_excess_smul
#print axioms Gtz.dominates_of_pairwiseOrthogonalPick
#print axioms Gtz.posDef_of_pairwiseOrthogonalPick
#print axioms Gtz.exists_dominating_of_pairwiseOrthogonalPick
#print axioms Gtz.dominates_of_orthogonalTriple_of_one_le
#print axioms Gtz.dotProduct_eq_zero_of_weightedLeverage_eq_one
#print axioms Gtz.weightedLeverage_eq_one_of_forall_dotProduct_eq_zero
#print axioms Gtz.weightedLeverage_eq_one_iff_forall_dotProduct_eq_zero
#print axioms Gtz.one_lt_leverage_of_weightedLeverage_eq_one
#print axioms Gtz.exists_planar_pair_explicitFloor
#print axioms Gtz.pos_of_collarExchange
#print axioms Gtz.exists_posDef_triple_of_collar
#print axioms Gtz.exists_dominating_triple_of_collar
#print axioms Gtz.exists_dominating_triple_of_collarRadius
#print axioms Gtz.exists_posDef_triple_of_weightedLeverage_eq_one
#print axioms Gtz.exists_dominating_triple_of_weightedLeverage_eq_one
#print axioms Gtz.boxGoodGraph
#print axioms Gtz.boxGoodGraph_adj
#print axioms Gtz.cliqueFree_boxGoodGraph_of_forall_not_dominates
#print axioms Gtz.card_edgeFinset_boxGoodGraph_le
#print axioms Gtz.card_edgeFinset_boxGoodGraph_le_six
#print axioms Gtz.card_edgeFinset_boxGoodGraph_le_seven
#print axioms Gtz.card_edgeFinset_compl_boxGoodGraph_ge
#print axioms Gtz.boxGoodGraph_icosaDesign_eq_bot
#print axioms Gtz.eq_of_ne_of_ne_bool
#print axioms Gtz.exists_equalTriple_of_five
#print axioms Gtz.exists_monochromaticTriangle_six
#print axioms Gtz.exists_monochromaticTriangle_of_pick
#print axioms Gtz.exists_monochromaticTriple_of_pairPredicate
#print axioms Gtz.not_cliqueFree_three_and_compl_cliqueFree_three
#print axioms Gtz.pentagonGraph
#print axioms Gtz.pentagonGraph_adj
#print axioms Gtz.pentagon_no_monochromaticTriple
#print axioms Gtz.cliqueFree_three_pentagonGraph
#print axioms Gtz.cliqueFree_three_compl_pentagonGraph
#print axioms Gtz.exists_cliqueFree_three_and_compl_cliqueFree_three_five
#print axioms Gtz.exists_dominating_triple_or_boxBadTriple
#print axioms Gtz.nearPencilSixDesign_pole_leverage
#print axioms Gtz.nearPencilSixDesign_pole_weight
#print axioms Gtz.nearPencilSixDesign_pole_share
#print axioms Gtz.exists_posDef_triple_nearPencilSixDesign
#print axioms Gtz.nearPencilSixDesign_collarBudget_of_lt_one
#print axioms Gtz.dominates_nearPencilSixDesign_orthogonalTriple

-- Gtz/Design/SignSelectedAggregate.lean
#print axioms Gtz.elliptopeBracket_nonneg_of_coherent_of_pairSums_le_one
#print axioms Gtz.isElliptopePoint_of_coherent_of_pairSums_le_one
#print axioms Gtz.pairSums_le_one_of_sq_le_half
#print axioms Gtz.exists_lightCherries_not_sq_le_half
#print axioms Gtz.IsLightCherry
#print axioms Gtz.isLightCherry_comm
#print axioms Gtz.isLightCherry_iff_normalizedPairing_pairSum_le_one
#print axioms Gtz.isLightCherry_of_halfBoxPairs
#print axioms Gtz.dominates_of_coherentLightCherryTriangle
#print axioms Gtz.exists_nonneg_atomPairingProduct_of_five_atoms
#print axioms Gtz.exists_dominating_triple_of_five_lightCherries
#print axioms Gtz.exists_dominating_triple_of_five_halfBoxPairs
#print axioms Gtz.icosaDesign_isLightCherry
#print axioms Gtz.exists_dominating_triple_icosaDesign_of_five
#print axioms Gtz.exists_heavyCherry_of_five_atoms
#print axioms Gtz.IsHalfBoxGoodPair
#print axioms Gtz.isHalfBoxGoodPair_comm
#print axioms Gtz.halfBoxGoodGraph
#print axioms Gtz.halfBoxGoodGraph_adj
#print axioms Gtz.cliqueFree_five_halfBoxGoodGraph_of_forall_not_dominates
#print axioms Gtz.card_edgeFinset_halfBoxGoodGraph_le
#print axioms Gtz.card_edgeFinset_halfBoxGoodGraph_le_seven
#print axioms Gtz.card_edgeFinset_halfBoxGoodGraph_le_six
#print axioms Gtz.card_edgeFinset_compl_halfBoxGoodGraph_ge
#print axioms Gtz.card_edgeFinset_compl_halfBoxGoodGraph_ge_seven
#print axioms Gtz.excessMass
#print axioms Gtz.excessMass_pos
#print axioms Gtz.sum_excessMass_eq_two
#print axioms Gtz.atomPairing_sq_eq_normalizedPairing_sq_mul
#print axioms Gtz.heavyExcess_mul_sum_excessMass_mul_normalizedPairing_sq
#print axioms Gtz.excessMass_min_lt_rowBudget_of_heavyCherry
#print axioms Gtz.sum_normalizedPairing_sq_of_uniform
#print axioms Gtz.rowAverage_eq_hinge_threshold_iff_seven
#print axioms Gtz.sum_normalizedPairing_sq_uniform_seven
#print axioms Gtz.sum_normalizedPairing_sq_uniform_six
#print axioms Gtz.exists_heavyCherry_rowBudget_of_five_atoms
#print axioms Gtz.rowBudget_heavyCherry_bound_at_uniform_iff
#print axioms Gtz.cherryWitnessAtom
#print axioms Gtz.cherryWitnessWeight
#print axioms Gtz.cherryWitnessDesign
#print axioms Gtz.cherryWitnessDesign_atom
#print axioms Gtz.cherryWitnessBlock
#print axioms Gtz.cherryWitnessBlock_injective
#print axioms Gtz.cherryWitnessDesign_leverage_block
#print axioms Gtz.cherryWitnessDesign_heavyExcess_block
#print axioms Gtz.cherryWitnessDesign_atomPairing_block
#print axioms Gtz.cherryWitnessDesign_allHeavy
#print axioms Gtz.cherryWitnessDesign_isHalfBoxGoodPair_block
#print axioms Gtz.cherryWitnessDesign_isLightCherry_block
#print axioms Gtz.cherryWitnessDesign_not_dominates_block
#print axioms Gtz.exists_allHeavy_design_with_failing_lightCherry_fourBlock

-- The U6 layer: the equal-share (6,3) cell, closed.  The stratum is the set of
-- `Gtz.WeightedDesign 6 3` with every weight `1/6` and every leverage `3`
-- (`Gtz.IsEqualShare`) -- six unit directions in `R^3` summing to `2 I`.  Its headline is
-- `Gtz.gtzWeighted_six_three_of_isEqualShare`: every design OF THAT STRATUM has a dominating
-- triple.  That is `Gtz.GtzWeighted 6 3` with `IsEqualShare` added as a hypothesis, NOT the
-- unrestricted `GtzWeighted 6 3`, which remains open.  The stratum is inhabited
-- (`Gtz.isEqualShare_icosaDesign`, `Gtz.isEqualShare_octahedronDesign`), so the restriction is
-- not vacuous.  Four inputs feed the four-case squeeze that proves it -- the
-- norm cap and the domination dictionary (HollowInvolution), the cubic criterion under that
-- cap (TripleCubicCriterion), the sign-free weight squeeze (WeightProductFloor), and the
-- sigma-preserved / P-negated split law (MirrorLaw) -- and the margin file then removes the
-- one hypothesis the first assembly could not: two trace laws on a blocked symmetric
-- involution replace the missing Jacobi complementary-minor identity, so
-- `Gtz.IsHollowInvolution.exists_posSemidef_twoThirds_shift` holds for EVERY hollow
-- symmetric involution on `Fin 6`, with no coherence and no realizability side condition.
--
-- Four refutations are carried here as theorems and none of them may be restated as a
-- claim.  The pen's "entries in (-1,1)" is NOT a consequence of the S1 data
-- (`Gtz.exists_isHollowInvolution_abs_apply_eq_one`) and is FALSE on the stratum itself:
-- the octahedron has `gamma = -1` on three antipodal pairs
-- (`Gtz.not_forall_abs_directionGram_lt_one_of_isEqualShare`), and it dominates anyway
-- (`Gtz.dominates_octahedronDesign`), so the hypothesis would delete a point at which the
-- conclusion holds.  The mirror law is NOT a fact about symmetric involutions in general
-- (`Gtz.not_forall_det_shift_mirror_ofSymmetricInvolution`); what makes it true here is the
-- tight-frame trace identity, not genericity.  Cap slack buys NO margin at `4/9`
-- (`Gtz.exists_capSlack_signFreeTripleResidual_eq_four_ninths`), yet `4/9` is not tight
-- either: the uniform margin is `9/25` on the eigenvalue side
-- (`Gtz.exists_nine_twentyfifths_le_lambdaMinMat_of_isEqualShare`), whose measured truth is
-- near `0.4122` -- a MEASUREMENT, never a theorem.  Finally the coordinate trap is a
-- theorem, not a warning: this repository's `rho` and the pen's `gamma` differ by `3/2` at
-- this stratum (`Gtz.normalizedPairing_eq_three_halves_mul_directionGram`), so a shipped
-- `rho`-threshold read as a `gamma`-threshold silently changes every constant.

-- Gtz/Quantitative/HollowInvolution.lean
#print axioms Gtz.IsHollowInvolution
#print axioms Gtz.IsHollowInvolution.symmetric
#print axioms Gtz.IsHollowInvolution.diagonal_eq_zero
#print axioms Gtz.IsHollowInvolution.square_eq_one
#print axioms Gtz.IsHollowInvolution.apply_comm
#print axioms Gtz.IsHollowInvolution.isHermitian
#print axioms Gtz.IsHollowInvolution.trace_eq_zero
#print axioms Gtz.IsHollowInvolution.neg
#print axioms Gtz.IsHollowInvolution.sum_sq_row
#print axioms Gtz.IsHollowInvolution.sum_sq_row_erase
#print axioms Gtz.IsHollowInvolution.sq_apply_le_one
#print axioms Gtz.IsHollowInvolution.abs_apply_le_one
#print axioms Gtz.IsHollowInvolution.sq_apply_eq_one_iff
#print axioms Gtz.IsHollowInvolution.sum_sdiff_pair_mul
#print axioms Gtz.IsHollowInvolution.posSemidef_one_sub
#print axioms Gtz.IsHollowInvolution.posSemidef_one_add
#print axioms Gtz.IsHollowInvolution.posSemidef_one_sub_submatrix
#print axioms Gtz.IsHollowInvolution.posSemidef_one_add_submatrix
#print axioms Gtz.IsHollowInvolution.submatrix_transpose
#print axioms Gtz.IsHollowInvolution.submatrix_diagonal_eq_zero
#print axioms Gtz.IsHollowInvolution.positivePart
#print axioms Gtz.IsHollowInvolution.negativePart
#print axioms Gtz.IsHollowInvolution.isIdempotentElem_positivePart
#print axioms Gtz.IsHollowInvolution.isIdempotentElem_negativePart
#print axioms Gtz.IsHollowInvolution.positivePart_add_negativePart
#print axioms Gtz.IsHollowInvolution.positivePart_mul_negativePart
#print axioms Gtz.IsHollowInvolution.trace_positivePart
#print axioms Gtz.IsHollowInvolution.trace_negativePart
#print axioms Gtz.IsHollowInvolution.sq_eigenvalues_eq_one
#print axioms Gtz.IsHollowInvolution.eigenvalues_eq_one_or_neg_one
#print axioms Gtz.IsHollowInvolution.card_eigenvalues_eq_one
#print axioms Gtz.swapInvolutionTwo
#print axioms Gtz.isHollowInvolution_swapInvolutionTwo
#print axioms Gtz.exists_isHollowInvolution_abs_apply_eq_one
#print axioms Gtz.hollowMatrixThree
#print axioms Gtz.hollowMatrixThree_transpose
#print axioms Gtz.one_add_hollowMatrixThree
#print axioms Gtz.one_sub_hollowMatrixThree
#print axioms Gtz.sq_sum_add_two_mul_abs_prod_le_one_of_posSemidef
#print axioms Gtz.IsHollowInvolution.submatrix_three_eq_hollowMatrixThree
#print axioms Gtz.IsHollowInvolution.normCap_triple
#print axioms Gtz.dotProduct_atom_eq_of_uniformLeverage
#print axioms Gtz.IsEqualShare
#print axioms Gtz.IsEqualShare.leverage_eq
#print axioms Gtz.IsEqualShare.weight_eq
#print axioms Gtz.IsEqualShare.size_pos
#print axioms Gtz.IsEqualShare.leverage_pos
#print axioms Gtz.IsEqualShare.atomShare_eq
#print axioms Gtz.IsEqualShare.directionGram_self
#print axioms Gtz.IsEqualShare.allHeavy
#print axioms Gtz.IsEqualShare.dotProduct_atom_eq
#print axioms Gtz.correlationInvolution
#print axioms Gtz.correlationInvolution_apply_of_ne
#print axioms Gtz.correlationInvolution_apply_self
#print axioms Gtz.correlationInvolution_submatrix_three_eq_hollowMatrixThree
#print axioms Gtz.directionGramMatrix_sq_of_isEqualShare
#print axioms Gtz.isHollowInvolution_correlationInvolution
#print axioms Gtz.sum_sq_directionGram_erase_of_isEqualShare
#print axioms Gtz.sum_sdiff_directionGram_mul_of_isEqualShare
#print axioms Gtz.directionGram_normCap_triple
#print axioms Gtz.unitFrameSum
#print axioms Gtz.subsetSum_eq_smul_unitFrameSum
#print axioms Gtz.dominates_iff_posSemidef_unitFrameSum
#print axioms Gtz.tripleGapMatrix_eq_smul_hollowShift
#print axioms Gtz.dominates_triple_iff_posSemidef_hollowShift
#print axioms Gtz.dominates_triple_iff_posSemidef_correlationInvolution_submatrix
#print axioms Gtz.dominates_triple_iff_posSemidef_directionGramMatrix_submatrix
#print axioms Gtz.le_lambdaMinMat_iff_posSemidef_sub_smul_one
#print axioms Gtz.dominates_triple_iff_inv_three_le_lambdaMinMat
#print axioms Gtz.posSemidef_unitFrameSum_iff_posSemidef_directionGramMatrix_submatrix
#print axioms Gtz.normalizedPairing_eq_three_halves_mul_directionGram
#print axioms Gtz.correlationMatrixThree_normalizedPairing_eq_smul_hollowShift
#print axioms Gtz.tightFrameDesign
#print axioms Gtz.tightFrameDesign_atom
#print axioms Gtz.isEqualShare_tightFrameDesign
#print axioms Gtz.unitAtom_tightFrameDesign
#print axioms Gtz.directionGram_tightFrameDesign
#print axioms Gtz.isEqualShare_icosaDesign
#print axioms Gtz.isHollowInvolution_icosaDesign
#print axioms Gtz.octahedronFrame
#print axioms Gtz.octahedronFrame_tight
#print axioms Gtz.octahedronFrame_unit
#print axioms Gtz.octahedronDesign
#print axioms Gtz.isEqualShare_octahedronDesign
#print axioms Gtz.directionGram_octahedronDesign_zero_one
#print axioms Gtz.not_forall_abs_directionGram_lt_one_of_isEqualShare
#print axioms Gtz.dominates_octahedronDesign
#print axioms Gtz.directionGram_eq_zero_of_sq_directionGram_eq_one
#print axioms Gtz.isEqualShare_six_of_weight_of_leverage
#print axioms Gtz.IsEqualShare.weight_eq_six
#print axioms Gtz.IsEqualShare.leverage_eq_three
#print axioms Gtz.IsEqualShare.allHeavy_three
#print axioms Gtz.isHollowInvolution_correlationInvolution_six
#print axioms Gtz.sum_sq_directionGram_erase_six
#print axioms Gtz.sum_sdiff_directionGram_mul_six
#print axioms Gtz.directionGram_normCap_triple_six
#print axioms Gtz.dominates_triple_iff_posSemidef_hollowShift_six
#print axioms Gtz.dominates_triple_iff_inv_three_le_lambdaMinMat_six
#print axioms Gtz.dominates_iff_posSemidef_unitFrameSum_six
#print axioms Gtz.normalizedPairing_eq_three_halves_mul_directionGram_six
#print axioms Gtz.inv_three_le_lambdaMinMat_icosaDesign
#print axioms Gtz.posSemidef_hollowShift_icosaDesign
#print axioms Gtz.sum_sq_directionGram_erase_octahedronDesign

-- Gtz/Quantitative/MirrorLaw.lean
#print axioms Gtz.matrixScalar_eq_smul_one
#print axioms Gtz.det_smul_one_sub_eq_evalCharpoly
#print axioms Gtz.det_shift_gram_eq_det_shift_frame
#print axioms Gtz.det_shift_frame_mirror
#print axioms Gtz.det_shift_gram_mirror
#print axioms Gtz.det_shift_gap_mirror
#print axioms Gtz.det_shift_gap_mirror_ofLevelTwo
#print axioms Gtz.det_gram_eq_det_level_smul_one_sub_gram
#print axioms Gtz.trace_gram_add_trace_gram
#print axioms Gtz.charpoly_gram_mirror
#print axioms Gtz.posSemidef_gram_sub_smul_one_iff_ofTightSplit
#print axioms Gtz.pow_mul_det_shift_gram_mirror
#print axioms Gtz.pow_mul_det_shift_gram_mirror_ofSquareLeft
#print axioms Gtz.det_shift_gram_mirror_sevenThree
#print axioms Gtz.det_shift_eq_of_intertwine
#print axioms Gtz.det_shift_mirror_of_anticommutingBlocks
#print axioms Gtz.det_shift_mirror_of_symmetricInvolutionBlocks
#print axioms Gtz.not_forall_det_shift_mirror_ofSymmetricInvolution
#print axioms Gtz.directionFrame
#print axioms Gtz.directionFrame_mul_transpose
#print axioms Gtz.transpose_mul_directionFrame_apply
#print axioms Gtz.leverageOf_pos_of_atomShare_pos
#print axioms Gtz.subsetSum_add_subsetSum_compl_of_uniformWeight
#print axioms Gtz.dominates_iff_posSemidef_smul_one_sub_subsetSum_compl
#print axioms Gtz.subsetSum_eq_smul_sum_atomMatrix_unitAtom
#print axioms Gtz.subsetSum_triple_eq_smul_directionFrame_mul_transpose
#print axioms Gtz.sum_atomMatrix_unitAtom_of_uniformShare
#print axioms Gtz.sum_eq_of_bijective_six
#print axioms Gtz.directionFrame_tightSplit_six
#print axioms Gtz.directionTripleSigma
#print axioms Gtz.directionTripleProduct
#print axioms Gtz.det_one_smul_sub_directionGram_triple
#print axioms Gtz.directionTripleProduct_compl_eq_neg
#print axioms Gtz.exists_nonneg_directionTripleProduct_ofSplit
#print axioms Gtz.sum_directionGram_sq_split
#print axioms Gtz.directionTripleSigma_compl_eq
#print axioms Gtz.directionSquareMass
#print axioms Gtz.directionCrossSquareMass
#print axioms Gtz.sum_directionGram_sq_of_uniformShare
#print axioms Gtz.directionSquareMass_add_directionCrossSquareMass
#print axioms Gtz.directionCrossSquareMass_compl
#print axioms Gtz.directionSquareMass_sub_directionSquareMass_compl
#print axioms Gtz.directionSquareMass_compl_eq
#print axioms Gtz.directionSquareMass_triple
#print axioms Gtz.directionSquareMass_compl_sub_sevenThree
#print axioms Gtz.atomShare_icosaDesign
#print axioms Gtz.directionTripleSigma_icosaDesign_mirror
#print axioms Gtz.directionTripleProduct_icosaDesign_mirror

-- Gtz/Quantitative/TripleCubicCriterion.lean
#print axioms Gtz.hollowSymmetricThree
#print axioms Gtz.hollowSymmetricThree_transpose
#print axioms Gtz.eq_hollowSymmetricThree_of_transpose_eq_of_diagonal_eq_zero
#print axioms Gtz.smul_one_add_hollowSymmetricThree
#print axioms Gtz.smul_one_sub_hollowSymmetricThree
#print axioms Gtz.smul_one_add_hollowSymmetricThree_transpose
#print axioms Gtz.correlationMatrixThree_eq_one_add_hollowSymmetricThree
#print axioms Gtz.trace_hollowSymmetricThree
#print axioms Gtz.det_smul_one_add_hollowSymmetricThree
#print axioms Gtz.det_smul_one_sub_hollowSymmetricThree
#print axioms Gtz.charpoly_hollowSymmetricThree
#print axioms Gtz.eval_charpoly_hollowSymmetricThree
#print axioms Gtz.nonneg_of_cubicRoot_of_elementarySymmetric_nonneg
#print axioms Gtz.pos_of_cubicRoot_of_elementarySymmetric_pos
#print axioms Gtz.posSemidef_three_of_elementarySymmetric
#print axioms Gtz.posDef_three_of_elementarySymmetric
#print axioms Gtz.smul_hollowSymmetricThree
#print axioms Gtz.smul_one_add_hollowSymmetricThree_eq_smul_correlationMatrixThree
#print axioms Gtz.elliptopeBracket_div_eq_det_div
#print axioms Gtz.posSemidef_smul_one_add_hollowSymmetricThree_iff
#print axioms Gtz.posSemidef_smul_one_sub_hollowSymmetricThree_iff
#print axioms Gtz.posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_correlationMatrixThree
#print axioms Gtz.elliptopeBracket_threeHalves_eq_criterionResidual
#print axioms Gtz.determinantCriterion_of_posSemidef_smul_one_add_hollowSymmetricThree
#print axioms Gtz.posSemidef_smul_one_add_hollowSymmetricThree_of_squareSum_le
#print axioms Gtz.nonneg_of_posSemidef_smul_one_sub_hollowSymmetricThree
#print axioms Gtz.mul_squareSum_add_two_mul_product_le_of_spectralCapUpper
#print axioms Gtz.mul_squareSum_sub_two_mul_product_le_of_spectralCapLower
#print axioms Gtz.mul_squareSum_add_two_mul_abs_product_le_of_spectralCap
#print axioms Gtz.squareSum_add_two_mul_abs_product_le_one
#print axioms Gtz.add_mul_squareSum_le_of_spectralCapUpper_of_determinantCriterion
#print axioms Gtz.squareSum_le_three_mul_sq_of_spectralCapUpper
#print axioms Gtz.posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
#print axioms Gtz.posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
#print axioms Gtz.posSemidef_smul_one_sub_hollowSymmetricThree_iff_of_spectralCapLower
#print axioms Gtz.posDef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapUpper
#print axioms Gtz.uniformStratumQuadratic_factor
#print axioms Gtz.uniformStratumCap_le_hinge_iff_size_le_seven
#print axioms Gtz.posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds
#print axioms Gtz.determinantCriterion_of_spectralCapUpper_of_heavyProduct
#print axioms Gtz.posSemidef_smul_one_add_hollowSymmetricThree_of_spectralCapUpper_of_heavyProduct
#print axioms Gtz.posSemidef_twoThirds_of_spectralCapUpper_of_ninth_le_product
#print axioms Gtz.posSemidef_twoThirds_of_spectralCapUpper_of_coherent_of_ninth_le_abs_product
#print axioms Gtz.criterion_hollowSymmetricThree_negThird_eq_fourNinths
#print axioms Gtz.det_twoThirds_smul_one_add_hollowSymmetricThree_negThird
#print axioms Gtz.posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_negThird
#print axioms Gtz.criterion_hollowSymmetricThree_half_eq_threeEighths
#print axioms Gtz.posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_half
#print axioms Gtz.squareSum_add_two_mul_abs_product_hollowSymmetricThree_half_eq_one
#print axioms Gtz.heavyProduct_hollowSymmetricThree_half
#print axioms Gtz.criterion_hollowSymmetricThree_equiangularFifth
#print axioms Gtz.not_heavyProduct_hollowSymmetricThree_equiangularFifth
#print axioms Gtz.criterion_hollowSymmetricThree_one_one_one
#print axioms Gtz.not_posSemidef_twoThirds_smul_one_add_hollowSymmetricThree_one_one_one
#print axioms Gtz.not_posSemidef_one_sub_hollowSymmetricThree_one_one_one
#print axioms Gtz.exists_hollowSymmetricThree_criterion_without_posSemidef
#print axioms Gtz.exists_hollowSymmetricThree_capSharpness
#print axioms Gtz.posSemidef_one_sub_hollowSymmetricThree_negHalf
#print axioms Gtz.posSemidef_one_add_hollowSymmetricThree_negHalf
#print axioms Gtz.exists_spectralCapped_hollowSymmetricThree_incoherent_heavy_not_posSemidef
#print axioms Gtz.posSemidef_smul_one_add_iff_of_hollow_of_entries
#print axioms Gtz.mul_squareSum_add_two_mul_abs_product_le_of_hollow_of_entries
#print axioms Gtz.posSemidef_smul_one_add_of_hollow_of_entries_of_heavyProduct

-- Gtz/Quantitative/WeightProductFloor.lean
#print axioms Gtz.edgeWeight
#print axioms Gtz.edgeWeight_comm
#print axioms Gtz.edgeWeight_nonneg
#print axioms Gtz.edgeWeight_le_one
#print axioms Gtz.edgeWeight_self
#print axioms Gtz.sum_erase_edgeWeight_eq_of_atomShare_eq
#print axioms Gtz.size_mul_atomShare_eq_rank_of_atomShare_eq
#print axioms Gtz.sum_erase_edgeWeight_eq_of_equalShare
#print axioms Gtz.sum_erase_edgeWeight_eq_one_of_uniformSixThree
#print axioms Gtz.sum_sum_erase_edgeWeight_eq_of_equalShare
#print axioms Gtz.signFreeTripleResidual
#print axioms Gtz.signFreeTripleResidual_swap_first_second
#print axioms Gtz.signFreeTripleResidual_swap_second_third
#print axioms Gtz.signFreeTripleResidual_le_sum
#print axioms Gtz.signFreeTripleResidual_le_three_mul_of_le_bound
#print axioms Gtz.sqrt_sq_mul_sq_mul_sq
#print axioms Gtz.signFreeTripleResidual_sq_eq_sub_abs
#print axioms Gtz.signFreeTripleResidual_sq_eq_min
#print axioms Gtz.signFreeTripleResidual_sq_eq_of_nonneg_product
#print axioms Gtz.signFreeTripleResidual_sq_le_sub
#print axioms Gtz.signFreeTripleResidual_sq_le_add
#print axioms Gtz.signFreeTripleResidual_le_of_sq_le_edgeProduct
#print axioms Gtz.sub_le_signFreeTripleResidual_of_edgeProduct_le_sq
#print axioms Gtz.signFreeTripleResidual_le_sub_of_normCap
#print axioms Gtz.triangleProductFloor
#print axioms Gtz.triangleProductFloor_le_edgeProduct_of_bound_le
#print axioms Gtz.triangleProductFloor_le_edgeProduct_of_le_bound
#print axioms Gtz.rootProductFloor_le_edgeProduct_of_sq_le
#print axioms Gtz.rootProductFloor_le_edgeProduct_of_le_sq
#print axioms Gtz.sq_pow_three_le_edgeProduct_of_sq_le
#print axioms Gtz.pow_mul_sub_le_prod_of_bound_le
#print axioms Gtz.pow_mul_sub_le_prod_of_le_bound
#print axioms Gtz.failureQuadratic
#print axioms Gtz.failureQuadratic_eq
#print axioms Gtz.failureQuadratic_sq
#print axioms Gtz.failureQuadratic_expand
#print axioms Gtz.lt_failureQuadratic_of_lt_signFreeTripleResidual
#print axioms Gtz.signFreeTripleResidual_le_of_failureQuadratic_nonpos
#print axioms Gtz.quadratic_nonpos_of_endpoints_nonpos
#print axioms Gtz.quadratic_neg_of_endpoints_neg
#print axioms Gtz.failureQuadratic_nonpos_of_endpoints_nonpos
#print axioms Gtz.signFreeTripleResidual_le_of_heavyTriangle_endpoints
#print axioms Gtz.signFreeTripleResidual_le_of_lightTriangle_endpoints
#print axioms Gtz.failureQuadratic_at_threshold
#print axioms Gtz.failureQuadratic_at_threshold_nonpos
#print axioms Gtz.failureQuadratic_at_three_mul
#print axioms Gtz.failureQuadratic_four_ninths_at_three_mul
#print axioms Gtz.failureQuadratic_four_ninths_at_three_mul_nonpos
#print axioms Gtz.failureQuadratic_four_ninths_at_normCap_nonpos
#print axioms Gtz.three_mul_sq_le_one_sub_two_mul_pow_three
#print axioms Gtz.signFreeTripleResidual_le_four_ninths_of_lightTriangle
#print axioms Gtz.signFreeTripleResidual_le_four_ninths_of_heavyTriangle_of_normCap
#print axioms Gtz.signFreeTripleResidual_le_four_ninths_of_heavyTriangle_of_largeRoot
#print axioms Gtz.signFreeTripleResidual_le_four_ninths_of_heavyTriangle
#print axioms Gtz.signFreeTripleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle
#print axioms Gtz.orientedTripleResidual
#print axioms Gtz.triangleResidual
#print axioms Gtz.triangleResidual_swap_first_second
#print axioms Gtz.triangleResidual_swap_second_third
#print axioms Gtz.sqrt_edgeWeight_product_eq_abs
#print axioms Gtz.triangleResidual_eq_min
#print axioms Gtz.triangleResidual_le_orientedTripleResidual
#print axioms Gtz.triangleResidual_eq_orientedTripleResidual_of_coherent
#print axioms Gtz.triangleResidual_le_orientedTripleResidual_and_eq_of_coherent
#print axioms Gtz.triangleResidual_le_of_heavyTriangle_endpoints
#print axioms Gtz.triangleResidual_le_of_lightTriangle_endpoints
#print axioms Gtz.triangleResidual_le_three_mul_of_le_bound
#print axioms Gtz.triangleResidual_le_sub_of_normCap
#print axioms Gtz.triangleResidual_le_four_ninths_of_lightTriangle
#print axioms Gtz.triangleResidual_le_four_ninths_of_heavyTriangle
#print axioms Gtz.triangleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle

-- Gtz/Quantitative/EqualShareSixThree.lean
#print axioms Gtz.distinctTriples
#print axioms Gtz.mem_distinctTriples
#print axioms Gtz.distinctTriples_nonempty
#print axioms Gtz.minTripleWeight
#print axioms Gtz.minTripleWeight_nonneg
#print axioms Gtz.maxMinWeight
#print axioms Gtz.minTripleWeight_le_maxMinWeight
#print axioms Gtz.maxMinWeight_nonneg
#print axioms Gtz.exists_heavyTriple
#print axioms Gtz.exists_lightTriple
#print axioms Gtz.pow_three_le_sqrt_edgeProduct
#print axioms Gtz.normCap_pow_three_of_normCap_sqrt
#print axioms Gtz.exists_signFreeTripleResidual_le_four_ninths
#print axioms Gtz.IsHollowInvolution.normCap_sqrt
#print axioms Gtz.exists_signFreeTripleResidual_le_four_ninths_of_isHollowInvolution
#print axioms Gtz.IsHollowInvolution.posSemidef_twoThirds_of_coherent_of_signFreeTripleResidual_le
#print axioms Gtz.edgeWeight_normCap_sqrt
#print axioms Gtz.exists_triangleResidual_le_four_ninths
#print axioms Gtz.exists_bijective_completion_of_distinct
#print axioms Gtz.orientedTripleResidual_eq_sigma_sub
#print axioms Gtz.exists_coherent_orientedTripleResidual_le_of_triangleResidual_le
#print axioms Gtz.dominates_of_orientedTripleResidual_le_four_ninths
#print axioms Gtz.exists_dominating_triple_of_isEqualShare
#print axioms Gtz.gtzWeighted_six_three_of_isEqualShare
#print axioms Gtz.exists_inv_three_le_lambdaMinMat_of_isEqualShare
#print axioms Gtz.tightSide
#print axioms Gtz.tightEdgeWeight
#print axioms Gtz.tightEdgeWeight_comm
#print axioms Gtz.tightEdgeWeight_nonneg
#print axioms Gtz.signFreeTripleResidual_intra
#print axioms Gtz.signFreeTripleResidual_mixed_first
#print axioms Gtz.signFreeTripleResidual_mixed_second
#print axioms Gtz.signFreeTripleResidual_mixed_third
#print axioms Gtz.signFreeTripleResidual_tightEdgeWeight
#print axioms Gtz.sum_erase_tightEdgeWeight
#print axioms Gtz.not_normCap_tightEdgeWeight
#print axioms Gtz.not_cap_hypothesis_tightEdgeWeight
#print axioms Gtz.signFreeTripleResidual_le_sub_of_lightTriangle
#print axioms Gtz.signFreeTripleResidual_le_sub_of_heavyTriangle_of_capSlack
#print axioms Gtz.posDef_of_orientedTripleResidual_lt_four_ninths
#print axioms Gtz.failureQuadratic_four_ninths_at_three_mul_eq_zero_iff
#print axioms Gtz.not_normCap_equilateral_four_ninths
#print axioms Gtz.signFreeTripleResidual_tripod
#print axioms Gtz.signFreeTripleResidual_kFourStar
#print axioms Gtz.signFreeTripleResidual_icosahedral
#print axioms Gtz.signFreeTripleResidual_icosahedral_lt_four_ninths
#print axioms Gtz.exists_dominating_triple_icosaDesign
#print axioms Gtz.exists_dominating_triple_octahedronDesign
#print axioms Gtz.exists_capSlack_signFreeTripleResidual_eq_four_ninths
#print axioms Gtz.signFreeTripleResidual_equilateral
#print axioms Gtz.signFreeTripleResidual_equilateral_sub_four_ninths
#print axioms Gtz.le_half_of_normCap_equilateral
#print axioms Gtz.signFreeTripleResidual_equilateral_le_three_eighths
#print axioms Gtz.signFreeTripleResidual_equilateral_half
#print axioms Gtz.normCap_equilateral_half
#print axioms Gtz.signFreeTripleResidual_equilateral_lt_four_ninths
#print axioms Gtz.signFreeTripleResidual_le_max_of_lightTriangle
#print axioms Gtz.signFreeTripleResidual_degenerate
#print axioms Gtz.signFreeTripleResidual_lt_four_ninths_of_lightTriangle_of_lt

-- Gtz/Quantitative/EqualShareSixThreeMargin.lean
#print axioms Gtz.upperBlockRelation_of_squareEqOne
#print axioms Gtz.crossBlockRelation_of_squareEqOne
#print axioms Gtz.lowerBlockRelation_of_squareEqOne
#print axioms Gtz.trace_cube_add_trace_cube_of_blockRelations
#print axioms Gtz.trace_square_sub_trace_square_of_blockRelations
#print axioms Gtz.trace_hollowMatrixThree
#print axioms Gtz.trace_square_hollowMatrixThree
#print axioms Gtz.trace_cube_hollowMatrixThree
#print axioms Gtz.injective_three_of_ne
#print axioms Gtz.sum_split_of_bijective_six
#print axioms Gtz.IsHollowInvolution.ne_of_bijective_six
#print axioms Gtz.IsHollowInvolution.tripleSigma_compl_eq
#print axioms Gtz.IsHollowInvolution.tripleProduct_compl_eq_neg
#print axioms Gtz.IsHollowInvolution.exists_nonneg_tripleProduct_of_split
#print axioms Gtz.IsHollowInvolution.det_one_sub_submatrix_eq_det_one_add_compl
#print axioms Gtz.IsHollowInvolution.normCap_eq_one_iff_degenerate
#print axioms Gtz.sub_le_max_of_heavyBounds
#print axioms Gtz.signFreeTripleResidual_le_max_of_heavyTriangle
#print axioms Gtz.root_le_half_of_capBound
#print axioms Gtz.lightBranch_le_two_fifths
#print axioms Gtz.heavyBranch_le_two_fifths
#print axioms Gtz.exists_signFreeTripleResidual_le_two_fifths
#print axioms Gtz.signFreeTripleResidual_lightExtremal
#print axioms Gtz.signFreeTripleResidual_heavyExtremal
#print axioms Gtz.normCap_heavyExtremal
#print axioms Gtz.heavyBranch_at_half
#print axioms Gtz.signFreeTripleResidual_kFourStarWeights
#print axioms Gtz.exists_coherent_orientedTripleResidual_le
#print axioms Gtz.exists_triangleResidual_le_two_fifths
#print axioms Gtz.posSemidef_smul_one_add_hollowSymmetricThree_of_criterion_le_sq
#print axioms Gtz.directionGramMatrix_submatrix_three_eq_one_add_hollowMatrixThree
#print axioms Gtz.exists_nine_twentyfifths_le_lambdaMinMat_of_isEqualShare
#print axioms Gtz.exists_orientedTripleResidual_le_two_fifths
#print axioms Gtz.exists_dominating_triple_with_margin
#print axioms Gtz.exists_posDef_shift_of_isEqualShare
#print axioms Gtz.det_subsetSum_triple_eq_smul_det_directionGramMatrix
#print axioms Gtz.normCap_eq_one_iff_det_subsetSum_eq_zero
#print axioms Gtz.IsHollowInvolution.exists_signFreeTripleResidual_le_two_fifths
#print axioms Gtz.IsHollowInvolution.exists_coherent_criterion_le
#print axioms Gtz.IsHollowInvolution.exists_posSemidef_marginShift
#print axioms Gtz.IsHollowInvolution.exists_posSemidef_twoThirds_shift

-- Gtz/Quantitative/WeightedTripleCriterion.lean
#print axioms Gtz.slackHollowThree
#print axioms Gtz.slackHollowThree_transpose
#print axioms Gtz.slackHollowThree_eq_diagonal_add
#print axioms Gtz.slackHollowThree_self
#print axioms Gtz.slackDeterminantThree
#print axioms Gtz.det_slackHollowThree
#print axioms Gtz.posSemidef_slackHollowThree_iff
#print axioms Gtz.posSemidef_slackHollowThree_iff_of_nonneg
#print axioms Gtz.exists_slackClauses_without_posSemidef
#print axioms Gtz.slackDeterminantThree_sub_first
#print axioms Gtz.slackDeterminantThree_sub_second
#print axioms Gtz.slackDeterminantThree_sub_third
#print axioms Gtz.slackDeterminantThree_le_of_le_first
#print axioms Gtz.slackDeterminantThree_le_of_le_second
#print axioms Gtz.slackDeterminantThree_le_of_le_third
#print axioms Gtz.posSemidef_slackHollowThree_of_le
#print axioms Gtz.posSemidef_slackHollowThree_of_floor
#print axioms Gtz.slackHollowThree_convexCombination
#print axioms Gtz.weightSlack
#print axioms Gtz.weightSlack_lt_one
#print axioms Gtz.weightSlack_pos_iff_one_lt_leverage
#print axioms Gtz.weightSlack_pos
#print axioms Gtz.inv_one_sub_weightSlack
#print axioms Gtz.le_weightSlack_iff_le_leverage
#print axioms Gtz.weightSlack_le_iff_leverage_le
#print axioms Gtz.two_thirds_le_weightSlack_iff_three_le_leverage
#print axioms Gtz.weightSlack_le_third_iff_leverage_le
#print axioms Gtz.weightSlack_eq_one_sub_weight_div_atomShare
#print axioms Gtz.sum_weightSlack_of_uniformShare
#print axioms Gtz.sum_weightSlack_eq_four
#print axioms Gtz.weightSlack_eq_two_thirds_of_isEqualShare
#print axioms Gtz.leverageSqrtDiagonal
#print axioms Gtz.leverageSqrtDiagonal_transpose
#print axioms Gtz.isUnit_det_leverageSqrtDiagonal
#print axioms Gtz.tripleGapMatrix_eq_congr_slackHollowThree
#print axioms Gtz.dominates_triple_iff_posSemidef_slackHollowThree
#print axioms Gtz.dominates_triple_iff_slackClauses
#print axioms Gtz.not_dominates_of_lt_edgeWeight
#print axioms Gtz.dominates_triple_of_floor
#print axioms Gtz.dominates_triple_congr
#print axioms Gtz.tripleSlackCell
#print axioms Gtz.mem_tripleSlackCell_iff
#print axioms Gtz.tripleSlackCell_congr
#print axioms Gtz.mem_tripleSlackCell_of_le
#print axioms Gtz.convex_tripleSlackCell
#print axioms Gtz.constantOne_mem_tripleSlackCell
#print axioms Gtz.isClosed_tripleSlackCell
#print axioms Gtz.slackSimplex
#print axioms Gtz.heavySlackSimplex
#print axioms Gtz.heavySlackSimplex_subset_slackSimplex
#print axioms Gtz.convex_slackSimplex
#print axioms Gtz.isCompact_slackSimplex
#print axioms Gtz.constantTwoThirds_mem_slackSimplex
#print axioms Gtz.constantTwoThirds_mem_heavySlackSimplex
#print axioms Gtz.CoversSlackRegion
#print axioms Gtz.coversSlackRegion_mono
#print axioms Gtz.coversSlackRegion_iff_subset_iUnion
#print axioms Gtz.IsUnitTightFrameSix
#print axioms Gtz.frameCorrelationInvolution
#print axioms Gtz.frameCorrelationInvolution_apply_of_ne
#print axioms Gtz.isHollowInvolution_frameCorrelationInvolution
#print axioms Gtz.isUnitTightFrameSix_unitAtomRows
#print axioms Gtz.frameCorrelationInvolution_unitAtomRows
#print axioms Gtz.slackFrameDesign
#print axioms Gtz.slackFrameDesign_atom
#print axioms Gtz.leverageOf_slackFrameDesign_atom
#print axioms Gtz.weightSlack_slackFrameDesign
#print axioms Gtz.atomShare_slackFrameDesign
#print axioms Gtz.unitAtom_slackFrameDesign
#print axioms Gtz.directionGram_slackFrameDesign
#print axioms Gtz.GtzUniformShareSixThree
#print axioms Gtz.exists_dominates_of_coversHeavySlackSimplex
#print axioms Gtz.gtzUniformShareSixThree_iff_forall_coversHeavySlackSimplex
#print axioms Gtz.gtzUniformShareSixThree_of_forall_coversSlackSimplex
#print axioms Gtz.slackHollowThree_eq_hollowShift_of_leverage_eq_three
#print axioms Gtz.coversSlackRegion_singleton_twoThirds
#print axioms Gtz.coversSlackRegion_of_marginFloor
#print axioms Gtz.exists_dominates_of_sixteen_twentyfifths_le_weightSlack
#print axioms Gtz.exists_dominates_of_isEqualShare_six
#print axioms Gtz.sixteen_twentyfifths_lt_sqrtThree_sub_one
#print axioms Gtz.exists_lt_of_budget
#print axioms Gtz.exists_two_thirds_le_of_sum_eq_four
#print axioms Gtz.exists_lt_of_mem_slackSimplex
#print axioms Gtz.card_cheapSlackSet_le_two
#print axioms Gtz.card_cheapAtomSet_le_two

-- Gtz/Quantitative/TauOrderStatistics.lean
#print axioms Gtz.sum_probe_le_sum_of_nonneg_off_probe
#print axioms Gtz.sum_probe_lt_sum_of_pos_off_probe
#print axioms Gtz.exists_card_mul_le_of_sum_probe_le
#print axioms Gtz.exists_card_mul_lt_of_sum_probe_lt
#print axioms Gtz.compl_nonempty_of_card_lt_size
#print axioms Gtz.eq_rank_div_size_of_forall_atomShare_eq
#print axioms Gtz.uniformShare_of_isEqualShare
#print axioms Gtz.leverageOf_pos_of_uniformShare
#print axioms Gtz.inv_leverageOf_pos_of_uniformShare
#print axioms Gtz.inv_leverage_eq_size_div_rank_mul_weight
#print axioms Gtz.sum_inv_leverage_of_uniformShare
#print axioms Gtz.atomCapacity
#print axioms Gtz.atomCapacity_le_one
#print axioms Gtz.atomCapacity_lt_one
#print axioms Gtz.le_atomCapacity_iff_one_le_mul
#print axioms Gtz.lt_atomCapacity_iff_one_lt_mul
#print axioms Gtz.atomCapacity_eq_one_sub_two_mul_weight_iff
#print axioms Gtz.atomCapacity_eq_one_sub_size_div_rank_mul_weight
#print axioms Gtz.sum_atomCapacity_of_uniformShare
#print axioms Gtz.exists_card_mul_rank_le_size_mul_leverage
#print axioms Gtz.exists_card_mul_rank_lt_size_mul_leverage
#print axioms Gtz.exists_rank_le_leverage_of_uniformShare
#print axioms Gtz.exists_lt_atomCapacity_of_uniformShare
#print axioms Gtz.exists_le_atomCapacity_of_uniformShare
#print axioms Gtz.card_mul_rank_lt_size_mul_of_forall_leverage_le
#print axioms Gtz.card_mul_rank_mul_slack_lt_size_of_forall_atomCapacity_le
#print axioms Gtz.exists_subset_card_forall_lt_atomCapacity
#print axioms Gtz.card_filter_leverage_le_mul_rank_lt_size_mul
#print axioms Gtz.sum_atomShare_mul_atomCapacity
#print axioms Gtz.sum_atomShare_mul_slack_le_one_of_forall_atomCapacity_le
#print axioms Gtz.uniformShare_six_three_iff
#print axioms Gtz.exists_three_le_leverage_six_three
#print axioms Gtz.exists_three_le_leverage_six_three_without_uniformShare
#print axioms Gtz.exists_five_halves_lt_leverage_six_three
#print axioms Gtz.exists_two_lt_leverage_six_three
#print axioms Gtz.exists_three_halves_lt_leverage_six_three
#print axioms Gtz.exists_two_thirds_le_atomCapacity_six_three
#print axioms Gtz.exists_three_fifths_lt_atomCapacity_six_three
#print axioms Gtz.exists_one_half_lt_atomCapacity_six_three
#print axioms Gtz.exists_one_third_lt_atomCapacity_six_three
#print axioms Gtz.card_le_two_of_forall_leverage_le_three_halves_six_three
#print axioms Gtz.card_le_two_of_forall_atomCapacity_le_one_third_six_three
#print axioms Gtz.card_le_one_of_forall_leverage_le_one_six_three
#print axioms Gtz.exists_heavy_triple_atomCapacity_six_three
#print axioms Gtz.exists_heavy_triple_leverage_six_three
#print axioms Gtz.exists_heavy_pair_atomCapacity_six_three
#print axioms Gtz.exists_heavy_pair_leverage_six_three
#print axioms Gtz.two_mul_card_lt_size_of_forall_leverage_le_three_halves_rank_three
#print axioms Gtz.card_le_three_of_forall_leverage_le_three_halves_seven_three
#print axioms Gtz.exists_eighteen_sevenths_lt_leverage_seven_three
#print axioms Gtz.exists_fifteen_sevenths_lt_leverage_seven_three
#print axioms Gtz.exists_twelve_sevenths_lt_leverage_seven_three
#print axioms Gtz.exists_two_thirds_le_atomCapacity_seven_three
#print axioms Gtz.exists_eleven_eighteenths_lt_atomCapacity_seven_three
#print axioms Gtz.exists_eight_fifteenths_lt_atomCapacity_seven_three
#print axioms Gtz.exists_five_twelfths_lt_atomCapacity_seven_three
#print axioms Gtz.size_sub_size_div_rank_eq_size_sub_two_iff
#print axioms Gtz.atomShare_tetraDesign_eq_rank_div_size
#print axioms Gtz.sum_atomCapacity_tetraDesign
#print axioms Gtz.sum_atomCapacity_tetraDesign_ne_size_sub_two
#print axioms Gtz.sum_atomCapacity_of_uniformShare_seven_three

-- Gtz/Quantitative/MinorSumIdentities.lean
#print axioms Gtz.sum_det_principalMinors_compression_eq_sum_prod_eigenvalues
#print axioms Gtz.det_submatrix_subtype_image_eq_det_submatrix
#print axioms Gtz.image_mem_powersetCard_of_injective
#print axioms Gtz.eigenvalues_eq_zero_or_eq_of_sq_eq_smul
#print axioms Gtz.card_eigenvalues_eq_of_sq_eq_smul
#print axioms Gtz.sum_prod_of_eigenvalues_two_valued
#print axioms Gtz.sum_det_principalMinors_of_sq_eq_smul
#print axioms Gtz.directionGramMatrix_sq_of_uniformShare
#print axioms Gtz.trace_directionGramMatrix_of_uniformShare
#print axioms Gtz.sum_det_principalMinors_directionGramMatrix_of_uniformShare
#print axioms Gtz.det_directionGramMatrix_submatrix_eq_zero_of_uniformShare
#print axioms Gtz.hollowTripleSigma
#print axioms Gtz.hollowTripleProduct
#print axioms Gtz.hollowTripleBracket
#print axioms Gtz.hollowTripleBracket_eq_one_sub_sigma_add
#print axioms Gtz.IsHollowInvolution.det_one_add_submatrix_three_eq_hollowTripleBracket
#print axioms Gtz.symmetricMatrixFour
#print axioms Gtz.det_symmetricMatrixFour
#print axioms Gtz.injective_four_of_ne
#print axioms Gtz.isHollowInvolution_correlationInvolution_of_uniformShare
#print axioms Gtz.hollowTripleSigma_correlationInvolution_eq
#print axioms Gtz.hollowTripleProduct_correlationInvolution_eq
#print axioms Gtz.hollowTripleBracket_correlationInvolution_eq
#print axioms Gtz.sum_det_principalMinors_directionGramMatrix_sixThree
#print axioms Gtz.sum_det_principalMinors_directionGramMatrix_sevenThree
#print axioms Gtz.sq_directionGram_icosaDesign
#print axioms Gtz.det_smul_one_sub_submatrix_four_icosaDesign
#print axioms Gtz.exists_distinct_tripleBracket_ge_two_fifths_icosaDesign
#print axioms Gtz.IsHollowInvolution.sq_one_add
#print axioms Gtz.IsHollowInvolution.trace_one_add
#print axioms Gtz.IsHollowInvolution.sum_det_principalMinors_one_add
#print axioms Gtz.IsHollowInvolution.det_one_add_submatrix_eq_zero
#print axioms Gtz.IsHollowInvolution.det_one_sub_submatrix_eq_zero
#print axioms Gtz.IsHollowInvolution.sum_pair_mul_eq_zero
#print axioms Gtz.IsHollowInvolution.sum_pairTripleProduct_eq_zero
#print axioms Gtz.IsHollowInvolution.sum_vertexTripleProduct_eq_zero
#print axioms Gtz.IsHollowInvolution.sum_tripleProduct_ordered_eq_zero
#print axioms Gtz.IsHollowInvolution.sum_sq_row_six
#print axioms Gtz.IsHollowInvolution.sum_pairSquare_six
#print axioms Gtz.IsHollowInvolution.sum_pairSquare_fiveSet
#print axioms Gtz.IsHollowInvolution.sum_pairSquare_fourSet
#print axioms Gtz.IsHollowInvolution.sum_pairTripleProduct_six
#print axioms Gtz.IsHollowInvolution.sum_tripleProduct_throughPair
#print axioms Gtz.IsHollowInvolution.sum_tripleProduct_six
#print axioms Gtz.IsHollowInvolution.sum_tripleProduct_fiveSet
#print axioms Gtz.IsHollowInvolution.sum_tripleProduct_fourSet
#print axioms Gtz.IsHollowInvolution.sum_tripleSigma_six
#print axioms Gtz.IsHollowInvolution.sum_tripleSigma_throughVertex
#print axioms Gtz.IsHollowInvolution.sum_tripleSigma_fiveSet
#print axioms Gtz.IsHollowInvolution.sum_tripleSigma_fourSet
#print axioms Gtz.IsHollowInvolution.sum_tripleBracket_six
#print axioms Gtz.IsHollowInvolution.sum_tripleBracket_fiveSet
#print axioms Gtz.IsHollowInvolution.sum_tripleBracket_fourSet
#print axioms Gtz.IsHollowInvolution.exists_tripleBracket_ge_fourSet
#print axioms Gtz.IsHollowInvolution.exists_distinct_tripleBracket_ge_two_fifths
#print axioms Gtz.IsHollowInvolution.exists_distinct_tripleBracket_ge_two_fifths_avoiding
#print axioms Gtz.IsHollowInvolution.smul_one_sub_submatrix_four_eq
#print axioms Gtz.IsHollowInvolution.det_smul_one_sub_submatrix_four_expand
#print axioms Gtz.IsHollowInvolution.det_smul_one_sub_submatrix_four
#print axioms Gtz.IsHollowInvolution.det_submatrix_four_eq_pairSquare

-- Gtz/Quantitative/GTransformGate.lean
#print axioms Gtz.hollowMatrixThree_eq_hollowSymmetricThree
#print axioms Gtz.det_one_add_hollowMatrixThree
#print axioms Gtz.det_smul_one_add_hollowMatrixThree
#print axioms Gtz.gTransform
#print axioms Gtz.gTransform_eq_one_sub_quarter_mul_cubicSum
#print axioms Gtz.gTransform_zero
#print axioms Gtz.gTransform_one
#print axioms Gtz.gTransform_lt_gTransform_of_lt
#print axioms Gtz.gTransform_le_gTransform_of_le
#print axioms Gtz.gTransform_nonneg_of_le_one
#print axioms Gtz.gTransform_sqrtThree_sub_one
#print axioms Gtz.gTransform_le_iff_cube_add_three_mul_sq_le
#print axioms Gtz.cubicSum_eq_depressedCubic_shifted
#print axioms Gtz.gTransform_one_le_of_pairWeight_le_one
#print axioms Gtz.gTransform_affineThreshold_le
#print axioms Gtz.gTransform_le_half_iff_sqrtThree_sub_one_le
#print axioms Gtz.half_lt_gTransform_twoThirds
#print axioms Gtz.gTransform_fourFifths_le_at_pairWeight_fifth
#print axioms Gtz.affineThreshold_mem_unitInterval
#print axioms Gtz.twentySeven_mul_sq_tripleProduct_le_cube_squareSum
#print axioms Gtz.cappedCubicResidual_eq_gapCertificate
#print axioms Gtz.four_mul_cube_le_cappedCubic_of_le_threeQuarters
#print axioms Gtz.threeQuarters_mul_sq_le_of_amgm_of_root
#print axioms Gtz.threeQuarters_mul_sq_le_squareSum_of_shiftedDet_eq_zero
#print axioms Gtz.squareSum_le_three_mul_sq_of_amgm_of_determinantFloor
#print axioms Gtz.criterion_of_amgm_of_determinantFloor
#print axioms Gtz.middle_le_min_of_traceZero_of_capped
#print axioms Gtz.det_one_add_le_gTransform_of_shiftedDet_eq_zero
#print axioms Gtz.posSemidef_smul_one_add_hollowMatrixThree_of_gTransform_le_det
#print axioms Gtz.det_one_add_lt_gTransform_of_not_posSemidef
#print axioms Gtz.IsHollowInvolution.posSemidef_smul_one_add_submatrix_of_gTransform_le_det
#print axioms Gtz.posSemidef_diagonal_add_of_le
#print axioms Gtz.posSemidef_diagonal_add_of_floor
#print axioms Gtz.posSemidef_diagonal_add_hollowMatrixThree_of_gTransform_le_det
#print axioms Gtz.IsHollowInvolution.posSemidef_diagonal_add_submatrix_of_gTransform_le_det
#print axioms Gtz.hollowMatrixFour
#print axioms Gtz.hollowMatrixTwo
#print axioms Gtz.trace_hollowMatrixFour
#print axioms Gtz.trace_square_hollowMatrixFour
#print axioms Gtz.trace_cube_hollowMatrixFour
#print axioms Gtz.trace_hollowMatrixTwo
#print axioms Gtz.trace_square_hollowMatrixTwo
#print axioms Gtz.trace_cube_hollowMatrixTwo
#print axioms Gtz.injective_four_of_ne
#print axioms Gtz.injective_two_of_ne
#print axioms Gtz.sum_split_four_two_of_bijective_six
#print axioms Gtz.IsHollowInvolution.submatrix_four_eq_hollowMatrixFour
#print axioms Gtz.IsHollowInvolution.submatrix_two_eq_hollowMatrixTwo
#print axioms Gtz.IsHollowInvolution.sum_sq_edge_fourSet_eq
#print axioms Gtz.IsHollowInvolution.sum_tripleProduct_fourSet_eq_zero
#print axioms Gtz.IsHollowInvolution.sum_det_one_add_submatrix_fourSet_eq
#print axioms Gtz.exists_ge_of_four_sum
#print axioms Gtz.IsHollowInvolution.exists_triple_det_ge_of_fourSet
#print axioms Gtz.IsHollowInvolution.exists_pick_posSemidef_diagonal_add_of_capacity_floor
#print axioms Gtz.IsHollowInvolution.exists_triple_posSemidef_diagonal_add_hollowMatrixThree_of_capacity_floor
#print axioms Gtz.IsHollowInvolution.exists_pick_posSemidef_diagonal_add_of_affineThreshold

-- Gtz/Quantitative/PlanarTightFrameRigidity.lean
#print axioms Gtz.IsHollowInvolution.exists_zeroMatching_four
#print axioms Gtz.IsHollowInvolution.exists_zeroEntry_four
#print axioms Gtz.IsHollowInvolution.crossBlock_isOrthonormal_of_zeroEdge
#print axioms Gtz.IsHollowInvolution.complementaryEdge_eq_zero_of_zeroEdge_four
#print axioms Gtz.IsHollowInvolution.crossBlock_quarterTurn_of_zeroEdge
#print axioms Gtz.orthogonalPairInvolution
#print axioms Gtz.isHollowInvolution_orthogonalPairInvolution
#print axioms Gtz.familyGramMatrix
#print axioms Gtz.familyGramMatrix_apply
#print axioms Gtz.gramSquare_of_tightOnPlane
#print axioms Gtz.isHollowInvolution_familyGramMatrix_sub_one
#print axioms Gtz.exists_orthogonalMatching_of_unitTightFamily
#print axioms Gtz.exists_orthogonalPair_of_unitTightFamily
#print axioms Gtz.exists_orthogonalMatching_of_planarTightFrame
#print axioms Gtz.exists_orthogonalMatching_of_axisTightResidue
#print axioms Gtz.add_atomMatrix_eq_one_of_planarOrthonormalPair
#print axioms Gtz.sum_atomMatrix_eq_two_smul_one_of_orthogonalMatching
#print axioms Gtz.planarTightFrame_iff_exists_orthogonalMatching
#print axioms Gtz.dotProduct_eq_zero_of_planarTightFrame_two
#print axioms Gtz.mercedesPlanarFrame
#print axioms Gtz.exists_planarTightFrame_three_without_orthogonalPair
#print axioms Gtz.doubleMercedesPlanarFrame
#print axioms Gtz.exists_planarTightFrame_six_without_orthogonalPair
#print axioms Gtz.unitDirection_atom_eq_unitAtom
#print axioms Gtz.sum_atomMatrix_unitDirection_erase_of_saturatedAxis
#print axioms Gtz.dotProduct_eq_zero_of_unitDirection_dotProduct_eq_zero
#print axioms Gtz.exists_dominating_triple_of_axisTightResidue
#print axioms Gtz.exists_dominating_triple_of_saturatedAxisStratum

-- Gtz/Quantitative/CheapAtomGate.lean
#print axioms Gtz.atomWeightSlack
#print axioms Gtz.sum_atomWeightSlack
#print axioms Gtz.atomWeightSlack_lt_one
#print axioms Gtz.atomWeightSlack_eq_one_iff
#print axioms Gtz.leverage_mul_atomWeightSlack
#print axioms Gtz.slackTripleDeterminant
#print axioms Gtz.det_tripleGapMatrix_eq_slack
#print axioms Gtz.dominates_triple_of_slackMinors
#print axioms Gtz.slackTripleDeterminant_nonneg_of_dominates
#print axioms Gtz.shareValue_mul_sum_sq_dotProduct_unitAtom
#print axioms Gtz.eq_smul_of_sq_dotProduct_eq_one
#print axioms Gtz.dotProduct_unitAtom_self
#print axioms Gtz.exists_unitNormal_iff_edgeWeight_eq_one
#print axioms Gtz.not_exists_unitNormal_of_edgeWeight_ne_one
#print axioms Gtz.exists_unitNormal_octahedronDesign
#print axioms Gtz.directionTripleDeterminant
#print axioms Gtz.sum_directionGram_chain_through_pair
#print axioms Gtz.sum_edgeWeight_within_quadruple_eq
#print axioms Gtz.sum_directionTripleProduct_within_quadruple_eq_zero
#print axioms Gtz.sum_directionTripleDeterminant_within_quadruple_eq
#print axioms Gtz.directionTripleDeterminant_le_one_sub_edgeWeight
#print axioms Gtz.dominates_triple_of_directionTripleDeterminant_ge
#print axioms Gtz.exists_dominates_triple_of_twoCheapAtoms
#print axioms Gtz.not_three_cheap_atoms
#print axioms Gtz.pairSumValue
#print axioms Gtz.pairSumValue_le
#print axioms Gtz.pairSumValue_nonpos
#print axioms Gtz.pairSumValue_neg_of_lt_two
#print axioms Gtz.pairSumValue_eq_zero_iff
#print axioms Gtz.pairSumValue_one_one
#print axioms Gtz.sum_slackTripleDeterminant_through_pair_eq
#print axioms Gtz.sum_atomWeightSlack_six
#print axioms Gtz.atomWeightSlack_pair_mem_open
#print axioms Gtz.pairSumValue_atomWeightSlack_neg
#print axioms Gtz.not_zero_le_pairSumValue_atomWeightSlack
#print axioms Gtz.exists_not_dominates_through_pair
#print axioms Gtz.planarProjectionMass
#print axioms Gtz.sum_planarProjectionMass_through_pair_eq
#print axioms Gtz.slackTripleDeterminant_eq_of_deletionCorner
#print axioms Gtz.sum_slackTripleDeterminant_eq_of_deletionCorner
#print axioms Gtz.exists_nonneg_slackTripleDeterminant_of_deletionCorner
#print axioms Gtz.edgeSignSum
#print axioms Gtz.triangleSignSum
#print axioms Gtz.triangleCertificate_nonneg
#print axioms Gtz.edgeSignSum_le_five_of_mirrorBalance
#print axioms Gtz.coherentCount_le_seven
#print axioms Gtz.three_le_coherent_avoiding_atom

-- Gtz/Quantitative/WeightedBandCovering.lean
#print axioms Gtz.involSlackDeterminant
#print axioms Gtz.involSlackDeterminant_eq_det
#print axioms Gtz.mem_tripleSlackCell_of_clauses
#print axioms Gtz.sum_involSlackDeterminant_through_pair
#print axioms Gtz.sum_involSlackDeterminant_off_hub
#print axioms Gtz.exists_nonneg_involSlackDeterminant_of_starvedHub
#print axioms Gtz.exists_mem_tripleSlackCell_of_starvedHub
#print axioms Gtz.pairSumValue_self
#print axioms Gtz.involSlackDeterminant_self_eq_bracket_sub
#print axioms Gtz.starvedHub_of_hollowTripleBracket_le
#print axioms Gtz.sum_involSlackDeterminant_six
#print axioms Gtz.sum_involSlackDeterminant_le_of_mem_slackSimplex
#print axioms Gtz.hollowTripleBracket_mem_residualWindow
#print axioms Gtz.residualWindow_width
#print axioms Gtz.exists_dominates_of_starvedHub
#print axioms Gtz.coneCross
#print axioms Gtz.coneCross_sq
#print axioms Gtz.mercedesConeInvolution
#print axioms Gtz.isHollowInvolution_mercedesConeInvolution
#print axioms Gtz.mercedesConeInvolution_zeroOne
#print axioms Gtz.mercedesConeInvolution_zeroTwo
#print axioms Gtz.mercedesConeInvolution_oneTwo
#print axioms Gtz.mercedesConeInvolution_threeFour
#print axioms Gtz.mercedesConeInvolution_threeFive
#print axioms Gtz.mercedesConeInvolution_fourFive
#print axioms Gtz.hollowTripleBracket_mercedesCone_heavy
#print axioms Gtz.hollowTripleSigma_mercedesCone_heavy
#print axioms Gtz.sq_mercedesConeInvolution_heavyEdge
#print axioms Gtz.sq_mercedesConeInvolution_row_le
#print axioms Gtz.mem_tripleSlackCell_mercedesCone_light
#print axioms Gtz.mercedesCone_gateThreshold
#print axioms Gtz.mercedesCone_gateThreshold_lt_five_sixths
#print axioms Gtz.mercedesCone_covers_symmetricBand
#print axioms Gtz.involSlackDeterminant_mercedesCone_at_nine_tenths

-- The (7,3) frontier layer: the July 2026 pen campaign mechanized.  The uniform-share
-- (7,3) cell is the global frontier -- rank-three GTZ at every size IS the all-heavy (7,3)
-- statement (`Gtz.discriminantCovering_seven_iff_rank_three`) -- and on that stratum the
-- landed square law `Gamma^2 = (7/3) Gamma` becomes the quadratic law
-- `M^2 = (1/3) M + (4/3) 1` on the hollow correlation matrix, the one engine all eight
-- modules below run on.  SevenThreeInvolution lands the quadratic package (cube law, trace
-- laws, row law, positive supply chain), the one-line spectral caps, the single-clause
-- criterion `Dominates T <-> sigma_T - 3 P_T <= 4/9` (C1-IFF), and the basis-plus-tetrapod
-- witness `Gtz.sevenThreeBasisTetrapodDesign` -- the first design in the tree with every
-- share `3/7`, closing wf3's named non-vacuity gap and inhabiting both the hypothesis
-- stratum and the conclusion of `Gtz.GtzUniformShareSevenThree`.  SevenThreeConservation
-- lands the six conservation laws (C-P1, C-P2, C-P3, C-D1, C-D2, C-5SET, every constant
-- exact) and the weighted aggregate identity C-AGG: the 35 determinant clauses have the
-- frame-independent total `e_3(tau) - (10/3) sum tau + 28/27`, negative on the whole
-- capacity polytope -- no aggregate selector exists; what survives is the starved-hub gate
-- `Gtz.exists_dominates_of_starvedHub_sevenThree`.  SevenThreeRigidity lands the
-- interlacing-free block freezes -- the dropped-atom 6x6 charpoly
-- `(t+1)^3 (t-4/3)^2 (t-1/3)` with the dropped profile as the `1/3`-eigenvector, the
-- five-block one-parameter factorization -- and the sevenths reformulation R-7:
-- `T` dominates iff `2*1 - Gamma[F] >= 0` on the complementary four-set, with the exact
-- charpoly reflection `det(t 1_4 - Gamma[F]) = -t det((7/3 - t) 1_3 - Gamma[T])`.
-- SevenThreeCapsGates lands the two determinant caps, the sigma mass cap `13/9` (the
-- campaign's unverified chart maximum, now chart-exact; design-side attainment stays open),
-- the light gate at edge weight `1/9` and the RIGID heavy gate at `4/9` -- both ties landed
-- as PSD blocks with vanishing determinant -- so every failing triple lives in the open
-- middle band `m in (1/9, 4/9)` of the endpoint cubic `9(m - 1/9)(m - 4/9)^2`.
-- SevenThreeMaxVolume lands the fifths theorem STRICT (at every swap-maximal nonsingular
-- pick of a uniform-share design, `Gamma[T#] - (1/5) 1` is positive DEFINITE, the boundary
-- killed by the parity argument `extremalSignQuadratic_ne_one`, no eigenvalues anywhere)
-- and records the share-agnostic gate silent at (7,3): `3/7 + 1/9 = 34/63 < 1`.
-- SevenThreeNoGo closes six dead routes as theorems: Kneser disjointness (disjoint triples
-- cannot both starve -- the topological route needs overlap, so it cannot fire), axis
-- spillover (no (3,2,2) clustering is isotropic), the deflation-gate cancellation
-- (`s(1 - 1/l) = t(l - 1)` identically, the Schur route buys nothing at any leverage), the
-- field-blindness of the 2025 interlacing family (its (4,2) bound IS `Gtz.alphaRankTwo`,
-- the sharp COMPLEX constant, and R3 is a real-vs-complex separation), the capacity-point
-- aggregate constant `-224/9` (ordered form), and the two-zero-ATOM corner (honest
-- transport of the pen's zero-weight corner), which falls to `Gtz.gtzWeighted_of_le_five`.
-- The two frontier lanes: SevenThreeCBFloor sharpens the fifths floor to the Cauchy-Binet
-- floor `lambda_min(Gamma[T#]) > 31/150` at every maximal-volume pick (pick supplied
-- unconditionally), the relaxation optimum bracketed by sign evaluations of
-- `135 x^3 - 405 x^2 + 315 x - 49`, with the ERRATUM re-verified in exact arithmetic: the
-- campaign's earlier `0.2543` was the symmetric slice, the genuine optimum is asymmetric at
-- `0.2067...`; conjecture M7 is NAMED as the Prop `Gtz.MaxVolumeGramThirdFloorSevenThree`
-- (maximal-volume Gram clears `1/3`), shown to imply domination on the leverage-3 stratum,
-- and left OPEN -- the equality-case kill `fourEvenSignVectors_unitNorm_inconsistent` does
-- not perturb to a floor above `31/150` and the file says so.  SevenThreeMiddleBand fences
-- the band: per-pair completion identities (the pair mean NEVER certifies -- vacuity
-- recorded), the starve-feed sandwich `4/9 < r_T < 8/9 + 2 w_min`, five-set coherent floors
-- (every five-set carries strictly positive product mass), the new sigma gate
-- `sigma_T <= 1/3` forces domination (sharp at the witness's tetrapod tie), and the Ramsey
-- pigeonhole making both band endpoints kernel facts.  HONEST LEDGER: no sub-band of
-- `(1/9, 4/9)` is closed by this layer; the per-triple scalar system admits failing-shaped
-- data throughout the band, so interior closures need cross-triple realizability -- exactly
-- the open content of R3.  The named residuals: M7, the middle band, design-side attainment
-- of the `13/9` corner, and the light squeeze at free weights.

-- Gtz/Quantitative/SevenThreeInvolution.lean
#print axioms Gtz.correlationInvolution_sq_of_uniformShare
#print axioms Gtz.directionGramMatrix_sq_sevenThree
#print axioms Gtz.correlationInvolution_sq_uniformSevenThree
#print axioms Gtz.correlationInvolution_cube_uniformSevenThree
#print axioms Gtz.trace_correlationInvolution_of_uniformShare
#print axioms Gtz.trace_correlationInvolution_sq_uniformSevenThree
#print axioms Gtz.trace_correlationInvolution_cube_uniformSevenThree
#print axioms Gtz.sum_erase_edgeWeight_sevenThree
#print axioms Gtz.sum_sum_erase_edgeWeight_sevenThree
#print axioms Gtz.sum_sdiff_directionGram_mul_directionGram_sevenThree
#print axioms Gtz.posSemidef_smul_one_sub_of_sq_eq_smul
#print axioms Gtz.posSemidef_smul_one_sub_directionGramMatrix_of_uniformShare
#print axioms Gtz.posSemidef_sevenThirds_smul_one_sub_directionGramMatrix
#print axioms Gtz.posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_sevenThree
#print axioms Gtz.directionTripleSigma_add_three_halves_mul_directionTripleProduct_le_sevenThree
#print axioms Gtz.nonneg_one_sub_directionTripleSigma_add_two_mul_directionTripleProduct
#print axioms Gtz.two_mul_directionTripleProduct_le_directionTripleSigma
#print axioms Gtz.one_sub_directionTripleSigma_add_two_mul_directionTripleProduct_le_one
#print axioms Gtz.dominates_triple_iff_sigma_sub_three_mul_product_sevenThree
#print axioms Gtz.sevenThreeBasisTetrapodAtom
#print axioms Gtz.sevenThreeBasisTetrapodAtom_zero
#print axioms Gtz.sevenThreeBasisTetrapodAtom_one
#print axioms Gtz.sevenThreeBasisTetrapodAtom_two
#print axioms Gtz.sevenThreeBasisTetrapodAtom_three
#print axioms Gtz.sevenThreeBasisTetrapodAtom_four
#print axioms Gtz.sevenThreeBasisTetrapodAtom_five
#print axioms Gtz.sevenThreeBasisTetrapodAtom_six
#print axioms Gtz.sevenThreeBasisTetrapodDesign
#print axioms Gtz.sevenThreeBasisTetrapodDesign_atom
#print axioms Gtz.sevenThreeBasisTetrapodDesign_weight
#print axioms Gtz.leverageOf_sevenThreeBasisTetrapodDesign
#print axioms Gtz.isEqualShare_sevenThreeBasisTetrapodDesign
#print axioms Gtz.atomShare_sevenThreeBasisTetrapodDesign
#print axioms Gtz.allHeavy_sevenThreeBasisTetrapodDesign
#print axioms Gtz.weightSlack_sevenThreeBasisTetrapodDesign
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_zero_one
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_zero_two
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_one_two
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_three_four
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_three_five
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_three_six
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_four_five
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_four_six
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_five_six
#print axioms Gtz.directionGram_sevenThreeBasisTetrapodDesign_zero_three
#print axioms Gtz.edgeWeight_sevenThreeBasisTetrapodDesign_zero_three
#print axioms Gtz.directionTripleSigma_tetrapodTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.directionTripleProduct_tetrapodTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.tetrapodTriple_tie_sevenThreeBasisTetrapodDesign
#print axioms Gtz.gramBracket_tetrapodTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.slackDeterminantThree_tetrapodTriple_eq_zero
#print axioms Gtz.dominates_tetrapodTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.directionTripleSigma_basisTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.directionTripleProduct_basisTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.gramBracket_basisTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.dominates_basisTriple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.basisTripleGap_form_sevenThreeBasisTetrapodDesign
#print axioms Gtz.posDef_basisTripleGap_sevenThreeBasisTetrapodDesign
#print axioms Gtz.GtzUniformShareSevenThree
#print axioms Gtz.exists_dominating_triple_sevenThreeBasisTetrapodDesign
#print axioms Gtz.sevenThreeBasisTetrapodDesign_witnesses_gtzUniformShareSevenThree

-- Gtz/Quantitative/SevenThreeConservation.lean
#print axioms Gtz.sum_eq_of_bijective_seven
#print axioms Gtz.ne_of_bijective_seven
#print axioms Gtz.correlationInvolution_comm
#print axioms Gtz.involSlackDeterminant_one_eq_hollowTripleBracket
#print axioms Gtz.correlationInvolution_sq_sevenThree
#print axioms Gtz.correlationInvolution_cube_sevenThree
#print axioms Gtz.trace_correlationInvolution_sevenThree
#print axioms Gtz.trace_sq_correlationInvolution_sevenThree
#print axioms Gtz.trace_cube_correlationInvolution_sevenThree
#print axioms Gtz.sum_sq_correlationInvolution_sevenThree
#print axioms Gtz.sum_correlationInvolution_chain_sevenThree
#print axioms Gtz.sum_tripleProduct_pair_sevenThree
#print axioms Gtz.sum_sdiff_tripleProduct_pair_sevenThree
#print axioms Gtz.sum_sdiff_tripleProduct_pair_nonneg_sevenThree
#print axioms Gtz.sum_ordered_tripleProduct_vertex_sevenThree
#print axioms Gtz.sum_sq_row_sevenThree
#print axioms Gtz.sum_tripleProduct_throughPair_sevenThree
#print axioms Gtz.sum_pairTripleProduct_vertex_sevenThree
#print axioms Gtz.sum_tripleProduct_sevenThree
#print axioms Gtz.sum_pairSquare_sevenThree
#print axioms Gtz.sum_pairSquare_sixSet_sevenThree
#print axioms Gtz.sum_pairSquare_fiveSet_sevenThree
#print axioms Gtz.sum_sdiff_tripleBracket_pair_sevenThree
#print axioms Gtz.sum_tripleSigma_vertex_sevenThree
#print axioms Gtz.sum_tripleBracket_vertex_sevenThree
#print axioms Gtz.sum_tripleSigma_sevenThree
#print axioms Gtz.sum_tripleBracket_sevenThree
#print axioms Gtz.sum_tripleProduct_fiveSet_sevenThree
#print axioms Gtz.sum_tripleProduct_fiveSet_pos_sevenThree
#print axioms Gtz.exists_distinct_tripleProduct_ge_avoiding_sevenThree
#print axioms Gtz.sum_involSlackDeterminant_sevenThree
#print axioms Gtz.sum_involSlackDeterminant_eq_of_constant_sevenThree
#print axioms Gtz.sum_involSlackDeterminant_slack_one_sevenThree
#print axioms Gtz.sum_involSlackDeterminant_criterion_sevenThree
#print axioms Gtz.slackSimplexSeven
#print axioms Gtz.sum_involSlackDeterminant_le_of_mem_slackSimplexSeven
#print axioms Gtz.constantSlackAggregate_sub_factor_sevenThree
#print axioms Gtz.constantSlackAggregate_stationary_iff_sevenThree
#print axioms Gtz.pairSumValueSeven
#print axioms Gtz.pairSumValueSeven_self
#print axioms Gtz.pairSumValueSeven_criterionPoint
#print axioms Gtz.pairSumValueSeven_one_one
#print axioms Gtz.pairSumValueSeven_le
#print axioms Gtz.pairSumValueSeven_nonpos
#print axioms Gtz.sum_involSlackDeterminant_through_pair_sevenThree
#print axioms Gtz.sum_involSlackDeterminant_through_pair_criterion_sevenThree
#print axioms Gtz.sum_involSlackDeterminant_off_hub_sevenThree
#print axioms Gtz.exists_nonneg_involSlackDeterminant_of_starvedHub_sevenThree
#print axioms Gtz.exists_dominates_of_starvedHub_sevenThree
#print axioms Gtz.sum_det_principalMinors_eq_sum_tripleBracket_sevenThree

-- Gtz/Quantitative/SevenThreeRigidity.lean
#print axioms Gtz.det_smul_one_sub_transpose_mul_comm
#print axioms Gtz.det_transpose_mul_self_eq_zero_of_lt
#print axioms Gtz.posSemidef_smul_one_sub_transpose_mul_comm
#print axioms Gtz.sixBlockMatrix
#print axioms Gtz.sixBlockProfile
#print axioms Gtz.sixBlockProfile_dotProduct_self
#print axioms Gtz.sixBlockProfile_ne_zero
#print axioms Gtz.sixBlockMatrix_sq
#print axioms Gtz.sixBlockMatrix_mulVec_profile
#print axioms Gtz.smul_one_sub_sixBlockMatrix_mul_add_one
#print axioms Gtz.sixBlockMatrix_cubic_eq_zero
#print axioms Gtz.trace_sixBlockMatrix
#print axioms Gtz.trace_sixBlockMatrix_sq
#print axioms Gtz.trace_sixBlockMatrix_cube
#print axioms Gtz.det_smul_one_sub_sixBlockMatrix
#print axioms Gtz.det_sixBlockMatrix
#print axioms Gtz.fiveBlockMatrix
#print axioms Gtz.fiveBlockProfileOne
#print axioms Gtz.fiveBlockProfileTwo
#print axioms Gtz.fiveBlockProfileOne_dotProduct_self
#print axioms Gtz.fiveBlockProfileTwo_dotProduct_self
#print axioms Gtz.fiveBlockMatrix_sq
#print axioms Gtz.trace_fiveBlockMatrix
#print axioms Gtz.trace_fiveBlockMatrix_sq
#print axioms Gtz.det_smul_one_sub_fiveBlockMatrix
#print axioms Gtz.det_fiveBlockMatrix
#print axioms Gtz.posSemidef_unitFrameSum_sub_iff_quadGramCap_sevenThree
#print axioms Gtz.dominates_triple_iff_posSemidef_quadGramCap_sevenThree
#print axioms Gtz.det_smul_one_sub_quadGram_reflection_sevenThree

-- Gtz/Quantitative/SevenThreeCapsGates.lean
#print axioms Gtz.bandGateCubic_factorisation
#print axioms Gtz.bandGateCubic_vanishes_at_lightGate
#print axioms Gtz.bandGateCubic_vanishes_at_heavyGate
#print axioms Gtz.squeezeNonTransferSeptic_factorisation
#print axioms Gtz.squeezeNonTransferSeptic_vanishes_at_twoThirds
#print axioms Gtz.squeezeNonTransferSeptic_pos_of_ne_twoThirds
#print axioms Gtz.squeezeNonTransferSeptic_pos_of_lt_twoThirds
#print axioms Gtz.posSemidef_of_mul_self_eq_smul
#print axioms Gtz.posSemidef_smul_one_sub_of_mul_self_eq_smul
#print axioms Gtz.posSemidef_smul_one_sub_directionGramMatrix_of_atomShare_eq
#print axioms Gtz.directionGramMatrix_submatrix_three_eq_correlationMatrixThree
#print axioms Gtz.posSemidef_smul_one_sub_hollowSymmetricThree_of_uniformShare
#print axioms Gtz.posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_of_uniformShare
#print axioms Gtz.orientedTripleResidual_eq_sigma_sub_three_mul_product
#print axioms Gtz.dominates_triple_iff_orientedTripleResidual_le_four_ninths_of_uniformShare
#print axioms Gtz.dominates_triple_iff_orientedTripleResidual_le_four_ninths_sevenThree
#print axioms Gtz.posSemidef_smul_one_add_hollowSymmetricThree_iff_sevenThree
#print axioms Gtz.edgeWeight_le_four_ninths_of_dominates_triple
#print axioms Gtz.directionTripleSigma_le_one_add_two_mul_directionTripleProduct
#print axioms Gtz.directionTripleSigma_add_two_mul_abs_directionTripleProduct_le_one_of_nonpos
#print axioms Gtz.directionTripleSigma_add_three_halves_mul_product_le_sevenThree
#print axioms Gtz.directionTripleSigma_le_thirteen_ninths_of_uniformShare_sevenThree
#print axioms Gtz.dominates_triple_of_lightEdges_sevenThree
#print axioms Gtz.heavyEdges_rigid_of_uniformShare_sevenThree
#print axioms Gtz.dominates_triple_of_heavyEdges_sevenThree
#print axioms Gtz.middleBandEdges_of_not_dominates_sevenThree
#print axioms Gtz.failingChartCorner_thirteen_ninths
#print axioms Gtz.posSemidef_lightGateTie
#print axioms Gtz.det_lightGateTie_eq_zero
#print axioms Gtz.posSemidef_heavyGateTie
#print axioms Gtz.det_heavyGateTie_eq_zero

-- Gtz/Quantitative/SevenThreeMaxVolume.lean
#print axioms Gtz.offSquareSumScaled_le_of_traceCap
#print axioms Gtz.shiftedDetThreshold_nonneg_of_traceCap
#print axioms Gtz.sevenThreeShiftedDet_boundary_forces
#print axioms Gtz.extremalSignQuadratic_ne_one
#print axioms Gtz.det_of_unitDiagonalThree
#print axioms Gtz.inv_diagonal_of_unitDiagonalThree
#print axioms Gtz.posSemidef_sub_smul_one_of_traceCap
#print axioms Gtz.posSemidef_trace_smul_one_sub_of_three
#print axioms Gtz.IsSwapMaximalRowPick
#print axioms Gtz.abs_solveMatrix_le_one_of_swapMaximalRowPick
#print axioms Gtz.rawAtomRows
#print axioms Gtz.rawAtomRows_apply
#print axioms Gtz.sum_weight_smul_atomMatrix_solveMatrix
#print axioms Gtz.sum_atomMatrix_solveMatrix_of_uniformShare
#print axioms Gtz.inv_pickGram_eq_diagonal_add_outside
#print axioms Gtz.inv_unitPickGram_diagonal_of_uniformShare
#print axioms Gtz.inv_unitPickGram_diagonal_le_of_swapMaximal
#print axioms Gtz.inv_unitPickGram_diagonal_le_sevenThree
#print axioms Gtz.trace_inv_unitPickGram_le_sevenThree
#print axioms Gtz.posDef_unitPickGram_sub_fifth_sevenThree
#print axioms Gtz.posSemidef_unitPickGram_sub_fifth_sevenThree
#print axioms Gtz.posSemidef_unitPickGram_sub_sqrtSeventeenFloor_sixThree
#print axioms Gtz.dominates_of_pickWeight_add_inv_leverageSum
#print axioms Gtz.pickWeight_add_inv_leverageSum_lt_one_of_sevenThree

-- Gtz/Quantitative/SevenThreeNoGo.lean
#print axioms Gtz.subsetSum_univ_sevenThree_of_uniformWeight
#print axioms Gtz.subsetSum_disjoint_add_eq_seven_smul_one_sub_atomMatrix
#print axioms Gtz.posSemidef_smul_one_sub_atomMatrix_of_leverage_le
#print axioms Gtz.posSemidef_subsetSum_disjoint_add_sub_four_sevenThree
#print axioms Gtz.not_dotProduct_lt_of_disjoint_triples_sevenThree
#print axioms Gtz.not_dotProduct_lt_of_disjoint_triples_of_isEqualShare
#print axioms Gtz.sum_sq_dotProduct_unitAtom_of_uniformShare
#print axioms Gtz.sq_dotProduct_unitAtom_le_dotProduct_self
#print axioms Gtz.third_le_sum_sdiff_sq_dotProduct_unitAtom_sevenThree
#print axioms Gtz.deflationGateBound
#print axioms Gtz.deflationGate_cancellation
#print axioms Gtz.deflationGateBound_eq_weight_gate
#print axioms Gtz.deflationGateBound_lt_share
#print axioms Gtz.exists_deflationGateBound_near_share
#print axioms Gtz.xuQuadraticFourTwo_eq_zero_iff
#print axioms Gtz.xuQuadraticRootFourTwo_pos
#print axioms Gtz.xuQuadraticRootFourTwo_lt_mirror
#print axioms Gtz.four_mul_xuQuadraticRootFourTwo_eq_alphaRankTwo
#print axioms Gtz.exists_xuCubicRoot_sevenThree_lt_inv_seven
#print axioms Gtz.sum_sdiff_involSlackDeterminant_capacity_sevenThree
#print axioms Gtz.sum_ordered_involSlackDeterminant_capacity_sevenThree
#print axioms Gtz.exists_involSlackDeterminant_capacity_neg_sevenThree
#print axioms Gtz.exists_dominating_triple_of_two_zero_atoms_sevenThree

-- Gtz/Quantitative/SevenThreeCBFloor.lean
#print axioms Gtz.relaxationCubic_image_eq_cauchyBinetFloorCubic_sevenThree
#print axioms Gtz.cauchyBinetFloorCubic_sevenThree_neg_at_landedFloor
#print axioms Gtz.cauchyBinetFloorCubic_sevenThree_pos_at_upperBracket
#print axioms Gtz.cauchyBinetFloorCubic_sixThree_neg_at_landedFloor
#print axioms Gtz.cauchyBinetFloorCubic_sixThree_pos_at_quarter
#print axioms Gtz.squareSum_le_fourThirds_of_traceGate
#print axioms Gtz.squareSum_le_fiveFourths_of_traceGate
#print axioms Gtz.fourEvenSignVectors_unitNorm_inconsistent
#print axioms Gtz.det_tetrahedralCorrelationThree
#print axioms Gtz.sq_det_tetrapodUnitTriple
#print axioms Gtz.abs_det_solveMatrix_submatrix_le_one_of_maximalVolume
#print axioms Gtz.abs_twoRowMinor_solveMatrix_le_one_of_maximalVolume
#print axioms Gtz.det_transpose_mul_self_four_rows_eq_sum_sq_minors
#print axioms Gtz.trace_transpose_mul_self_le_of_abs_entries_le_one
#print axioms Gtz.posDef_sub_cauchyBinetFloor_of_exchangeGates_sevenThree
#print axioms Gtz.posDef_sub_cauchyBinetFloor_of_exchangeGates_sixThree
#print axioms Gtz.exists_injective_pick_det_unitAtomRows_ne_zero
#print axioms Gtz.exists_maximalVolume_pick_unitAtomRows
#print axioms Gtz.unitPickGram_eq_directionGramMatrix_submatrix
#print axioms Gtz.traceGate_of_maximalVolume_sevenThree
#print axioms Gtz.volumeGate_of_maximalVolume_sevenThree
#print axioms Gtz.directionTripleSigma_le_fourThirds_of_maximalVolume_sevenThree
#print axioms Gtz.posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree
#print axioms Gtz.posDef_directionGramMatrix_submatrix_sub_cauchyBinetFloor_sevenThree
#print axioms Gtz.exists_pick_posDef_unitPickGram_sub_cauchyBinetFloor_sevenThree
#print axioms Gtz.traceGate_of_maximalVolume_sixThree
#print axioms Gtz.nonneg_directionTripleProduct_of_maximalVolume_sixThree
#print axioms Gtz.directionTripleSigma_le_fiveFourths_of_maximalVolume_sixThree
#print axioms Gtz.posDef_unitPickGram_sub_cauchyBinetFloor_sixThree
#print axioms Gtz.exists_pick_posDef_unitPickGram_sub_cauchyBinetFloor_sixThree
#print axioms Gtz.exists_pick_posDef_sub_cauchyBinetFloor_icosaDesign
#print axioms Gtz.MaxVolumeGramThirdFloorSevenThree
#print axioms Gtz.exists_dominating_triple_of_maxVolumeGramThirdFloor

-- Gtz/Quantitative/SevenThreeMiddleBand.lean
#print axioms Gtz.sum_tripleSigma_pairCompletions_bandSeven
#print axioms Gtz.sum_tripleProduct_pairCompletions_bandSeven
#print axioms Gtz.sum_orientedResidual_pairCompletions_bandSeven
#print axioms Gtz.sum_slackDeterminantThree_pairCompletions_bandSeven
#print axioms Gtz.pairCompletions_mean_exceeds_criterion_bandSeven
#print axioms Gtz.sum_ordered_orientedResidual_bandSeven
#print axioms Gtz.exists_orientedResidual_le_mean_bandSeven
#print axioms Gtz.four_ninths_lt_orientedResidual_of_not_dominates_bandSeven
#print axioms Gtz.four_ninths_lt_tripleSigma_of_coherent_not_dominates_bandSeven
#print axioms Gtz.tripleProduct_lt_of_not_dominates_bandSeven
#print axioms Gtz.orientedResidual_window_of_allFailing_bandSeven
#print axioms Gtz.exists_dominates_completion_of_starvedHub_bandSeven
#print axioms Gtz.sum_ordered_tripleProduct_avoidingPair_bandSeven
#print axioms Gtz.exists_tripleProduct_ge_floor_avoidingPair_bandSeven
#print axioms Gtz.exists_coherentCarrier_of_allFailing_avoidingPair_bandSeven
#print axioms Gtz.dominates_triple_of_tripleSigma_le_third_bandSeven
#print axioms Gtz.third_lt_tripleSigma_of_not_dominates_bandSeven
#print axioms Gtz.sum_sum_edgeWeight_complementFourSet_bandSeven
#print axioms Gtz.two_lt_sum_sum_edgeWeight_complementFourSet_of_not_dominates_bandSeven
#print axioms Gtz.dominates_triple_of_sum_sum_edgeWeight_complementFourSet_le_bandSeven
#print axioms Gtz.edgeWeight_floor_le_quarter_of_tripleProduct_nonpos
#print axioms Gtz.exists_edgeWeight_le_four_ninths_bandSeven
#print axioms Gtz.exists_edgeWeight_lt_four_ninths_of_not_dominates_bandSeven
#print axioms Gtz.exists_heavyTriangle_of_allFailing_bandSeven
