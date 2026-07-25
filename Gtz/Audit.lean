/-
# Audit: axiom hygiene for everything claimed proven (FX discipline)

Every theorem this project calls PROVEN is listed here with `#print axioms`, so
each build displays exactly what it rests on. Expected axiom set for
Mathlib-backed proofs: `propext`, `Classical.choice`, `Quot.sound` — and NOTHING
else. In particular `sorryAx` appearing for any theorem listed here is a broken
promise; roadmap statements carrying `sorry` are deliberately NOT listed.

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
#print axioms Gtz.SpansSameLine
#print axioms Gtz.ComplexIsEquiangularAt
#print axioms Gtz.ComplexSpansSameLine
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
