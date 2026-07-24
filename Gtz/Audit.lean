/-
# Audit: axiom hygiene for everything claimed proven (FX discipline)

Every theorem this project calls PROVEN is listed here with `#print axioms`, so
each build displays exactly what it rests on. Expected axiom set for
Mathlib-backed proofs: `propext`, `Classical.choice`, `Quot.sound` — and NOTHING
else. In particular `sorryAx` appearing for any theorem listed here is a broken
promise; roadmap statements carrying `sorry` are deliberately NOT listed.

Update this file in the same commit that completes a proof.
-/
import Gtz.BhatiaDavis
import Gtz.Sanity
import Gtz.SchurRankOne
import Gtz.TraceIdentity
import Gtz.TriangleClosure
import Gtz.ResidueDissolution
import Gtz.CollaredCompact
import Gtz.OneObjectNarrowing
import Gtz.GapStabilityFacts
import Gtz.CornerFiber
import Gtz.CapCriterion
import Gtz.Crystallization
import Gtz.PsdKit
import Gtz.Completion
import Gtz.Naimark
import Gtz.Reductions
import Gtz.RatCertificate
import Gtz.PlanarPlatform
import Gtz.BlochDictionary
import Gtz.DustControl
import Gtz.LawCounterexample
import Gtz.Pushoff
import Gtz.TightGraph
import Gtz.CertificateFrame
import Gtz.MomentCovector
import Gtz.Compression
import Gtz.DescentLadder
import Gtz.FirstOrderLaw
import Gtz.CollarFloor
import Gtz.CapSlack
import Gtz.QuantitativeCorner
import Gtz.StressFrame
import Gtz.ComplexWitness
import Gtz.Seam
import Gtz.ComplexPadding
import Gtz.PThreeStratum
import Gtz.CollinearStratum
import Gtz.MomentBound
import Gtz.CornerResolvent
import Gtz.SilenceDictionary
import Gtz.BallPerturbation
import Gtz.EulerPairing
import Gtz.SplittingRule
import Gtz.ChordTheorem
import Gtz.LocalLaw
import Gtz.Completeness
import Gtz.ResolventPerturbation
import Gtz.IdempotentSplitting
import Gtz.LeafTangency
import Gtz.CapDictionary
import Gtz.MarginTransfer
import Gtz.AggregatePushoff
import Gtz.CornerPerturbation
import Gtz.FrameEncoding
import Gtz.WedgeChain
import Gtz.CertificateAnchor
import Gtz.BernsteinPositivity
import Gtz.SylvesterThree
import Gtz.GordanAlternative
import Gtz.TiedQuadruple
import Gtz.CoveringMargin
import Gtz.DowndateInterlacing
import Gtz.CyclicStress
import Gtz.LawEquivalence
import Gtz.WhiteningDistortion
import Gtz.ClosureObtuse
import Gtz.SymmetryReduction
import Gtz.DeflationCertificate
import Gtz.LeverageBound
import Gtz.Certs.PFourCertificate
import Gtz.Certs.CFiveCertificate
import Gtz.GeometricExclusion
import Gtz.LiftingLemma
import Gtz.Interface

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
#print axioms Gtz.mul_vecMulVec_eq
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
#print axioms Gtz.map_mul_cast
#print axioms Gtz.det_cast
#print axioms Gtz.RatDesign.gram_cast
#print axioms Gtz.ratInv_cast
#print axioms Gtz.RatDesign.pivot_cast
#print axioms Gtz.ratCertificate_dominates
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
#print axioms Gtz.cexBudget_eq_trace
#print axioms Gtz.cexBudget_quadratic
#print axioms Gtz.cexMaxSlack_ge
#print axioms Gtz.cexMaxSlack_le
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
#print axioms Gtz.newInterfacePair_nonempty
#print axioms Gtz.interfaceFormula_rounds_down
#print axioms Gtz.interfacePair_nonvacuous_iff
#print axioms Gtz.weighted_defect_leash
#print axioms Gtz.smul_eq_smul_of_independent
#print axioms Gtz.eq_of_two_independent_rays
#print axioms Gtz.parabola_conic_zero_iff
#print axioms Gtz.parabola_poles_are_clones
#print axioms Gtz.c2_assembly
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
#print axioms Gtz.atomMatrix_compress
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
#print axioms Gtz.design_weighted_leverage_sum
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
#print axioms Gtz.atomMatrix_conjugate
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
#print axioms Gtz.posDef_three_of_leading_minors
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
#print axioms Gtz.atomMatrix_mulVec_conj
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
#print axioms Gtz.pair_budget_decompose
#print axioms Gtz.tight_pair_second_order_nonpos
#print axioms Gtz.pair_budget_le_firstOrder
#print axioms Gtz.envelope_forces_slack_pos
#print axioms Gtz.complex_sic_slack_neg
#print axioms Gtz.transverse_dist_le_of_coercive
#print axioms Gtz.quotient_floor_uniform
