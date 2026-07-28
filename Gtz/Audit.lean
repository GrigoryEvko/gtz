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
