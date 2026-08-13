/-
# The whitening at general rank, and the anchor-reach obligation as a theorem

`GeneralRankReachSkeleton` left two topological Props per window cell.
`MomentHubSchedule` discharged the first one.  This file discharges the second,
`WhiteningTransferAtRank`, at EVERY size and EVERY rank, with no window
hypothesis at all — and then closes the whole anchor-reach obligation.

THE MECHANISM.  The rank-three interface is explicit 3x3 Cholesky with
hand-written pivots (`Gtz/Reduction/CholeskyWhitening.lean`), and none of it
ports.  What replaces it is the positive-definite square root of the continuous
functional calculus: `gramRoot gram := cfc Real.sqrt gram`.  Three facts carry
the whole file.

* `gramRoot_mul_self`: on a positive-definite Gram the square root squares back,
  because `Real.sqrt` and the identity agree on a nonnegative spectrum.
* `transpose_gramRoot`: the calculus returns a self-adjoint matrix, and a
  self-adjoint real matrix is symmetric.
* `continuous_gramRoot_entry`: the calculus is continuous in its argument on a
  compact spectral window, and the spectrum of a matrix sits in the closed ball
  of its own norm, so a continuous Hermitian path has a continuous square root.

The mix is `(gramRoot gram)⁻¹`, whose entries are one determinant over another,
thus continuous where the determinant does not vanish, and the determinant of
the root squares to the determinant of the Gram, which is positive.  The
congruence `M gram Mᵀ = 1` is then four rewrites.

WHAT THIS CLOSES.  `whiteningTransferAtRank_general` needs no hypothesis, so
with the schedule the anchor-reach obligation becomes a theorem:
`sharpWindowAnchorReachRankFourAndUp` carries the exact type of
`Skeleton.obligationSharpWindowAnchorReachRankFourAndUp`, and
`canonicalWindowParallelFreeConnectivity_of_three_le` closes the connectivity
residual of `AnchorReachAssembly` at every rank of three or more.  Rank two
stays refuted (`not_canonicalWindowParallelFreeConnectivity_two`), so the floor
is sharp.

WHAT ELSE FALLS OUT.  Both anchor Props of `RouteBProps` become theorems, and
the connectedness route loses two of its four inputs:
`gtzWeighted_of_hinge_of_parallelBranch` gives weighted GTZ at every window cell
from the hinge and the parallel branch alone.  At `(6,3)` the parallel branch is
a shipped theorem, so `gtzWeighted_six_three_of_hinge` rests on the hinge only.
-/
import Gtz.Uniform.MomentHubSchedule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace GeneralRankReach

open Matrix Finset

/-! ## Congruence of the Gram

Mixing every row by one matrix conjugates the Gram.  This is `atomMatrix_conj`
summed over the labels. -/

/-- **THE CONGRUENCE.**  A common linear mix of the rows conjugates the Gram. -/
theorem gramOf_conj {size rank : ℕ} (mix : Matrix (Fin rank) (Fin rank) ℝ)
    (rows : Fin size → Fin rank → ℝ) :
    gramOf (fun label => mix *ᵥ rows label) = mix * gramOf rows * mixᵀ := by
  rw [gramOf, gramOf, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun label _ => atomMatrix_conj mix (rows label)

/-- The Gram entry is the sum of the products of two row coordinates. -/
theorem gramOf_apply {size rank : ℕ} (rows : Fin size → Fin rank → ℝ)
    (rowIndex colIndex : Fin rank) :
    gramOf rows rowIndex colIndex = ∑ label, rows label rowIndex * rows label colIndex := by
  rw [gramOf, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun label _ => rfl

/-! ## The positive-definite square root

`cfc Real.sqrt` is the square root of the continuous functional calculus.  The
calculus is available on `Matrix (Fin rank) (Fin rank) ℝ` through
`Matrix.IsHermitian.instContinuousFunctionalCalculus`, and every property below
is read from the spectrum. -/

/-- The square root of a Gram matrix. -/
noncomputable def gramRoot {rank : ℕ} (gram : Matrix (Fin rank) (Fin rank) ℝ) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  cfc Real.sqrt gram

/-- The square root is self-adjoint, whatever the argument. -/
theorem isSelfAdjoint_gramRoot {rank : ℕ} (gram : Matrix (Fin rank) (Fin rank) ℝ) :
    IsSelfAdjoint (gramRoot gram) :=
  cfc_predicate Real.sqrt gram

/-- A self-adjoint real matrix is symmetric, thus the square root is its own
transpose. -/
theorem transpose_gramRoot {rank : ℕ} (gram : Matrix (Fin rank) (Fin rank) ℝ) :
    (gramRoot gram)ᵀ = gramRoot gram := by
  have hhermitian : (gramRoot gram).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr (isSelfAdjoint_gramRoot gram)
  have hsymm : (gramRoot gram).IsSymm := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hhermitian
  exact hsymm.eq

/-- **THE SQUARE.**  On a positive-definite matrix the spectrum is nonnegative,
so the square root squares back to the matrix. -/
theorem gramRoot_mul_self {rank : ℕ} {gram : Matrix (Fin rank) (Fin rank) ℝ}
    (hpos : gram.PosDef) : gramRoot gram * gramRoot gram = gram := by
  have hspectrum : ∀ value ∈ spectrum ℝ gram, 0 ≤ value := fun value hvalue =>
    (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hpos.posSemidef).2 hvalue
  have hselfAdjoint : IsSelfAdjoint gram := Matrix.isHermitian_iff_isSelfAdjoint.mp hpos.1
  rw [gramRoot, ← cfc_mul Real.sqrt Real.sqrt gram]
  exact (cfc_congr (g := (id : ℝ → ℝ))
    fun value hvalue => Real.mul_self_sqrt (hspectrum value hvalue)).trans
      (cfc_id ℝ gram hselfAdjoint)

/-- The identity is its own square root: the calculus commutes with the
structure map. -/
@[simp] theorem gramRoot_one {rank : ℕ} :
    gramRoot (1 : Matrix (Fin rank) (Fin rank) ℝ) = 1 := by
  rw [gramRoot, show (1 : Matrix (Fin rank) (Fin rank) ℝ) = algebraMap ℝ _ 1 from (map_one _).symm,
    cfc_algebraMap, Real.sqrt_one, map_one]

/-- **THE ROOT IS INVERTIBLE.**  Its determinant squares to the determinant of
the Gram, which is positive. -/
theorem det_gramRoot_ne_zero {rank : ℕ} {gram : Matrix (Fin rank) (Fin rank) ℝ}
    (hpos : gram.PosDef) : (gramRoot gram).det ≠ 0 := by
  have hsquare : (gramRoot gram).det * (gramRoot gram).det = gram.det := by
    rw [← Matrix.det_mul, gramRoot_mul_self hpos]
  intro hzero
  rw [hzero, mul_zero] at hsquare
  exact hpos.det_pos.ne' hsquare.symm

theorem isUnit_det_gramRoot {rank : ℕ} {gram : Matrix (Fin rank) (Fin rank) ℝ}
    (hpos : gram.PosDef) : IsUnit (gramRoot gram).det :=
  isUnit_iff_ne_zero.mpr (det_gramRoot_ne_zero hpos)

/-- The inverse root is invertible too. -/
theorem det_inv_gramRoot_ne_zero {rank : ℕ} {gram : Matrix (Fin rank) (Fin rank) ℝ}
    (hpos : gram.PosDef) : ((gramRoot gram)⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero (det_gramRoot_ne_zero hpos)

/-- The inverse root is symmetric, because the root is. -/
theorem transpose_inv_gramRoot {rank : ℕ} (gram : Matrix (Fin rank) (Fin rank) ℝ) :
    ((gramRoot gram)⁻¹)ᵀ = (gramRoot gram)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, transpose_gramRoot]

/-- **THE WHITENING IDENTITY.**  The inverse root conjugates a positive-definite
Gram to the identity. -/
theorem conj_inv_gramRoot {rank : ℕ} {gram : Matrix (Fin rank) (Fin rank) ℝ}
    (hpos : gram.PosDef) :
    (gramRoot gram)⁻¹ * gram * ((gramRoot gram)⁻¹)ᵀ = 1 := by
  have hunit : IsUnit (gramRoot gram).det := isUnit_det_gramRoot hpos
  have hleft : (gramRoot gram)⁻¹ * gramRoot gram = 1 := Matrix.nonsing_inv_mul _ hunit
  have hright : gramRoot gram * (gramRoot gram)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  calc (gramRoot gram)⁻¹ * gram * ((gramRoot gram)⁻¹)ᵀ
      = (gramRoot gram)⁻¹ * (gramRoot gram * gramRoot gram) * (gramRoot gram)⁻¹ := by
        rw [transpose_inv_gramRoot, gramRoot_mul_self hpos]
    _ = ((gramRoot gram)⁻¹ * gramRoot gram) * (gramRoot gram * (gramRoot gram)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hleft, hright, Matrix.one_mul]

/-! ## Continuity of the square root

The calculus is continuous on a set of self-adjoint elements with a common
compact spectral window.  Along a continuous path the norm is locally bounded,
and the spectrum sits in the closed ball of the norm, so the window exists near
every time.  The statement is entrywise, thus no norm on matrices appears in
it. -/

open scoped Matrix.Norms.L2Operator in
/-- **THE SQUARE ROOT IS CONTINUOUS.**  A continuous self-adjoint matrix path
has a continuous square root, entry by entry. -/
theorem continuous_gramRoot_entry {rank : ℕ} {gram : ℝ → Matrix (Fin rank) (Fin rank) ℝ}
    (hentry : ∀ rowIndex colIndex, Continuous fun time => gram time rowIndex colIndex)
    (hselfAdjoint : ∀ time, IsSelfAdjoint (gram time)) (rowIndex colIndex : Fin rank) :
    Continuous fun time => gramRoot (gram time) rowIndex colIndex := by
  have hpath : Continuous gram := continuous_matrix fun row col => hentry row col
  have hroot : Continuous fun time => cfc Real.sqrt (gram time) := by
    refine continuous_iff_continuousAt.mpr fun timeBase => ?_
    refine ContinuousAt.cfc (s := Metric.closedBall (0 : ℝ)
        ((‖gram timeBase‖ + 1) * ‖(1 : Matrix (Fin rank) (Fin rank) ℝ)‖))
      (isCompact_closedBall _ _) Real.sqrt hpath.continuousAt ?_
      (Filter.Eventually.of_forall hselfAdjoint) Real.continuous_sqrt.continuousOn
    have hnear : ∀ᶠ time in nhds timeBase, ‖gram time‖ < ‖gram timeBase‖ + 1 := by
      have hball := hpath.continuousAt.norm (Metric.ball_mem_nhds (‖gram timeBase‖) one_pos)
      filter_upwards [hball] with time htime
      have hdist := Real.dist_eq _ _ ▸ Metric.mem_ball.mp htime
      cases abs_lt.mp hdist
      linarith
    filter_upwards [hnear] with time htime
    refine (spectrum.subset_closedBall_norm_mul (gram time)).trans ?_
    exact Metric.closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right htime.le (norm_nonneg _))
  exact (continuous_apply colIndex).comp ((continuous_apply rowIndex).comp hroot)

/-- **THE MIX IS CONTINUOUS.**  The inverse root has entries `adjugate` over
`det`, and the determinant of the root never vanishes on a positive-definite
path. -/
theorem continuous_inv_gramRoot_entry {rank : ℕ} {gram : ℝ → Matrix (Fin rank) (Fin rank) ℝ}
    (hentry : ∀ rowIndex colIndex, Continuous fun time => gram time rowIndex colIndex)
    (hpos : ∀ time, (gram time).PosDef) (rowIndex colIndex : Fin rank) :
    Continuous fun time => (gramRoot (gram time))⁻¹ rowIndex colIndex := by
  have hselfAdjoint : ∀ time, IsSelfAdjoint (gram time) := fun time =>
    Matrix.isHermitian_iff_isSelfAdjoint.mp (hpos time).1
  have hroot : Continuous fun time => gramRoot (gram time) :=
    continuous_matrix fun row col => continuous_gramRoot_entry hentry hselfAdjoint row col
  have hdet : Continuous fun time => (gramRoot (gram time)).det := hroot.matrix_det
  have hadjugate : Continuous fun time => (gramRoot (gram time)).adjugate rowIndex colIndex :=
    (continuous_apply colIndex).comp ((continuous_apply rowIndex).comp hroot.matrix_adjugate)
  have hsplit : ∀ time, (gramRoot (gram time))⁻¹ rowIndex colIndex
      = ((gramRoot (gram time)).det)⁻¹ * (gramRoot (gram time)).adjugate rowIndex colIndex := by
    intro time
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  simp only [hsplit]
  exact (hdet.inv₀ fun time => det_gramRoot_ne_zero (hpos time)).mul hadjugate

/-! ## T2 at every size and rank -/

/-- **THE WHITENING INTERFACE, PROVED.**  A continuous tuple path with
positive-definite Gram and Parseval endpoints deforms onto the Parseval shell
through the pointwise inverse square root of its own Gram.  No window
hypothesis, no rank hypothesis, no size hypothesis. -/
theorem whiteningTransferAtRank_general {size rank : ℕ} : WhiteningTransferAtRank size rank := by
  classical
  intro tuplePath hcont hpos hstart hend
  have hcoord : ∀ (label : Fin size) (coord : Fin rank),
      Continuous fun time => tuplePath time label coord := fun label coord =>
    (continuous_apply coord).comp ((continuous_apply label).comp hcont)
  have hgramEntry : ∀ rowIndex colIndex,
      Continuous fun time => gramOf (tuplePath time) rowIndex colIndex := by
    intro rowIndex colIndex
    simp only [gramOf_apply]
    exact continuous_finsetSum _ fun label _ =>
      (hcoord label rowIndex).mul (hcoord label colIndex)
  have hmixEntry : ∀ rowIndex colIndex,
      Continuous fun time => (gramRoot (gramOf (tuplePath time)))⁻¹ rowIndex colIndex :=
    continuous_inv_gramRoot_entry hgramEntry hpos
  refine ⟨fun time label => (gramRoot (gramOf (tuplePath time)))⁻¹ *ᵥ tuplePath time label,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun label => continuous_pi fun coord => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun other _ =>
      (hmixEntry coord other).mul (hcoord label other)
  · funext label
    show (gramRoot (gramOf (tuplePath 0)))⁻¹ *ᵥ tuplePath 0 label = tuplePath 0 label
    rw [hstart, gramRoot_one, inv_one, Matrix.one_mulVec]
  · funext label
    show (gramRoot (gramOf (tuplePath 1)))⁻¹ *ᵥ tuplePath 1 label = tuplePath 1 label
    rw [hend, gramRoot_one, inv_one, Matrix.one_mulVec]
  · intro time
    show gramOf (fun label => (gramRoot (gramOf (tuplePath time)))⁻¹ *ᵥ tuplePath time label) = 1
    rw [gramOf_conj]
    exact conj_inv_gramRoot (hpos time)
  · intro time
    exact ⟨(gramRoot (gramOf (tuplePath time)))⁻¹, det_inv_gramRoot_ne_zero (hpos time),
      fun _ => rfl⟩

/-- **PARITY.**  The general whitening covers the cell where the tree already
owns an explicit 3x3 Cholesky interface. -/
theorem whiteningTransferAtRank_six_three_ofSpectral : WhiteningTransferAtRank 6 3 :=
  whiteningTransferAtRank_general

/-! ## The reach, with both inputs discharged -/

/-- **THE REACH AT EVERY WINDOW CELL.**  Every parallel-free design of a cell
with `3 <= rank` and `2 * rank <= size` reaches every parallel-free anchor of
that cell through parallel-free designs. -/
theorem parallelFreeReachesAnchor_of_window {size rank : ℕ} (hrank : 3 ≤ rank)
    (hwindow : 2 * rank ≤ size) (anchor : WeightedDesign size rank)
    (hanchorFree : ¬ HasParallelPair anchor) : ParallelFreeReachesAnchor size rank anchor :=
  parallelFreeReachesAnchor_of_tupleReach (goodTupleConnected_of_window hrank hwindow)
    whiteningTransferAtRank_general anchor hanchorFree

/-- **THE CONNECTIVITY RESIDUAL OF THE ASSEMBLY, CLOSED.**  Rank two is refuted
by `not_canonicalWindowParallelFreeConnectivity_two`, so the floor is sharp. -/
theorem canonicalWindowParallelFreeConnectivity_of_three_le {rank : ℕ} (hrank : 3 ≤ rank) :
    UniformPositionBridge.CanonicalWindowParallelFreeConnectivity rank :=
  fun _ hinside anchor hanchorFree =>
    parallelFreeReachesAnchor_of_window hrank hinside.1 anchor hanchorFree

/-- The same over the sharp window. -/
theorem sharpWindowParallelFreeConnectivity_of_three_le {rank : ℕ} (hrank : 3 ≤ rank) :
    UniformPositionBridge.SharpWindowParallelFreeConnectivity rank :=
  fun _ hbelow _ anchor hanchorFree =>
    parallelFreeReachesAnchor_of_window hrank hbelow anchor hanchorFree

/-- **THE ANCHOR-REACH STATEMENT, AT EVERY RANK OF THREE OR MORE.**  Same shape
as `Skeleton.obligationSharpWindowAnchorReach`, with no hypothesis beyond the
rank floor. -/
theorem sharpWindowAnchorReach {rank : ℕ} (hrank : 3 ≤ rank) :
    ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
      ∃ anchor : WeightedDesign size rank,
        HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor :=
  UniformPositionBridge.sharpWindowAnchorReach_of_connectivity hrank
    (sharpWindowParallelFreeConnectivity_of_three_le hrank)

/-- **THE OBLIGATION, AS A THEOREM.**  The exact type of
`Skeleton.obligationSharpWindowAnchorReachRankFourAndUp`.  Nothing is assumed:
the anchor is assembled, the walk is scheduled, and the whitening is the
functional calculus. -/
theorem sharpWindowAnchorReachRankFourAndUp :
    ∀ rank : ℕ, 4 ≤ rank →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        ∃ anchor : WeightedDesign size rank,
          HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size rank anchor :=
  fun _ hrank => sharpWindowAnchorReach (by omega)

/-- The rank-three half of the same statement, independent of `icosaDesign`. -/
theorem sharpWindowAnchorReachRankThree :
    ∀ size : ℕ, 6 ≤ size → size ≤ 6 →
      ∃ anchor : WeightedDesign size 3,
        HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor size 3 anchor :=
  fun size hbelow habove => sharpWindowAnchorReach (le_refl 3) size (by omega) (by omega)

/-- **ROUTE (b), ON ONE INPUT.**  The relativized window hinge is the only
topological hypothesis left in route (b): the anchor, the walk and the whitening
are all theorems. -/
theorem routeB_target_of_windowTie
    (hwindowTie : ∀ rank : ℕ, 3 ≤ rank →
      UniformPositionBridge.ParallelPairAtWindowTieRelative rank) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank :=
  UniformPositionBridge.routeB_target_of_connectivity hwindowTie
    fun _ hrank => canonicalWindowParallelFreeConnectivity_of_three_le hrank

/-! ## The route-(b) anchor Props, discharged

`RouteBProps` states the anchor half of route (b) twice, with and without the
parallel-freeness of the anchor.  Both are theorems at every rank of three or
more. -/

/-- **THE ANCHOR HALF WITH PARALLEL-FREENESS.**  At every rank of three or more
each canonical window cell carries a parallel-free anchor that dominates
strictly and that every parallel-free design reaches. -/
theorem windowAnchorReachFree_of_three_le {rank : ℕ} (hrank : 3 ≤ rank) :
    UniformPositionBridge.WindowAnchorReachFree rank :=
  UniformPositionBridge.windowAnchorReachFree_of_connectivity hrank
    (canonicalWindowParallelFreeConnectivity_of_three_le hrank)

/-- The same without the parallel-freeness field. -/
theorem windowAnchorReach_of_three_le {rank : ℕ} (hrank : 3 ≤ rank) :
    UniformPositionBridge.WindowAnchorReach rank :=
  UniformPositionBridge.windowAnchorReach_of_connectivity hrank
    (canonicalWindowParallelFreeConnectivity_of_three_le hrank)

/-! ## The connectedness route, with its topological input supplied

`Gtz.gtzWeighted_of_hinge_of_reach` needs a hinge, a reach statement, a strictly
dominating anchor and a parallel branch.  Two of the four are now theorems at
every window cell, so the route runs on the hinge and the parallel branch. -/

/-- **STRICT DOMINATION FROM THE HINGE ALONE.**  Inside the window, every
parallel-free design of a cell whose hinge holds dominates strictly.  The anchor
and the path are supplied here. -/
theorem strictlyDominating_of_hinge_of_window {size rank : ℕ} (hrank : 3 ≤ rank)
    (hwindow : 2 * rank ≤ size) (hhinge : HingeHoldsAtSize size rank)
    (design : WeightedDesign size rank) (hfree : ¬ HasParallelPair design) :
    HasStrictlyDominatingSubset design := by
  obtain ⟨anchor, hanchorFree, hanchorStrict⟩ :=
    UniformPositionBridge.exists_parallelFreeStrictAnchor (rank := rank) (size := size)
      (by omega) (by omega)
  exact strictlyDominating_of_hinge_of_reach hhinge
    (parallelFreeReachesAnchor_of_window hrank hwindow anchor hanchorFree) hanchorStrict
    design hfree

/-- **THE CONNECTEDNESS ROUTE AT EVERY WINDOW CELL, ON TWO INPUTS.**  The hinge
and the parallel branch give weighted GTZ.  No anchor, no reach, no
domination estimate appears in the hypotheses. -/
theorem gtzWeighted_of_hinge_of_parallelBranch {size rank : ℕ} (hrank : 3 ≤ rank)
    (hwindow : 2 * rank ≤ size) (hhinge : HingeHoldsAtSize size rank)
    (hparallelBranch : ∀ design : WeightedDesign size rank, HasParallelPair design →
      ∃ chosen : Finset (Fin size), chosen.card = rank ∧ Dominates design chosen) :
    GtzWeighted size rank := by
  intro design
  by_cases hparallel : HasParallelPair design
  · exact hparallelBranch design hparallel
  · exact hasDominatingSubset_of_strict
      (strictlyDominating_of_hinge_of_window hrank hwindow hhinge design hparallel)

/-- The rank-three bottom cell, where the parallel branch is a shipped theorem:
`GtzWeighted 6 3` rests on the hinge alone, with no reach hypothesis and no
named anchor. -/
theorem gtzWeighted_six_three_of_hinge (hhinge : HingeHoldsAtSize 6 3) : GtzWeighted 6 3 :=
  gtzWeighted_of_hinge_of_parallelBranch (by norm_num) (by norm_num) hhinge
    exists_dominating_triple_of_hasParallelPair_sixThree

/-! ## Cross-checks at named cells -/

/-- The reach pair at the rank-four window floor. -/
theorem exists_anchorReach_eight_four :
    ∃ anchor : WeightedDesign 8 4,
      HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor 8 4 anchor :=
  sharpWindowAnchorReach (by norm_num) 8 (by norm_num) (by norm_num)

/-- The reach pair at the rank-four top cell. -/
theorem exists_anchorReach_ten_four :
    ∃ anchor : WeightedDesign 10 4,
      HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor 10 4 anchor :=
  sharpWindowAnchorReach (by norm_num) 10 (by norm_num) (by norm_num)

/-- The reach pair at the rank-five window floor. -/
theorem exists_anchorReach_ten_five :
    ∃ anchor : WeightedDesign 10 5,
      HasStrictlyDominatingSubset anchor ∧ ParallelFreeReachesAnchor 10 5 anchor :=
  sharpWindowAnchorReach (by norm_num) 10 (by norm_num) (by norm_num)

/-- The reach at `(6,3)` for every parallel-free anchor, through the general
route rather than the rank-three walk. -/
theorem parallelFreeReachesAnchor_six_three_ofGeneral (anchor : WeightedDesign 6 3)
    (hanchorFree : ¬ HasParallelPair anchor) : ParallelFreeReachesAnchor 6 3 anchor :=
  parallelFreeReachesAnchor_of_window (by norm_num) (by norm_num) anchor hanchorFree

end GeneralRankReach
end Gtz
