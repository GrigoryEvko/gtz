/-
# The two-vanished (4,3)-boundary of branch (ii): the laws that close it

`TwoVanishedRigidBottomDominationSixThree` is the residual where two positive-side
weights of the diagonal endpoint gauge have been walked to zero, so exactly four
atoms still carry weight: the surviving positive atom and the three negative ones.
Its equality locus is the (4,3) TOTAL-TIE family, on which no bottom triple is
strictly dominating, so the theorem must produce a SPIKE triple -- one built from
a weightless atom, whose weight is gone but whose direction is not.

This file lands the general laws that drive that argument.  Every statement is
about arbitrary data; nothing is specialised to the residual, so each brick is
reusable.  Write `windowGap` for the positive definite base
`sum over the carrying labels of (1 - weight) * atomMatrix`, and
`pivotAgainst windowGap v = trace (windowGap⁻¹ * atomMatrix v)` for the self-pivot,
which is `v (windowGap⁻¹ v)` by the landed `pivot_eq_dot` dictionary.

THE FIVE LAWS.

1. `sum_stress_mul_pivotDefect_eq_zero` -- THE MASTER IDENTITY.  Against any
   invertible base, a zero-sum stress annihilates the pivot DEFECTS:
   `sum_l stress_l (pivot_l - 1) = 0`.  One line of trace linearity, and it is
   what pairs the two spikes: at a total tie the four bottom defects vanish, so
   the two spike defects carry opposite signs and the larger spike pivot is at
   least one.  This is the exact product identity the branch-(iii) mechanism
   asks for, and `le_total` on a single scalar selects the spike.

2. `sum_coweight_mul_pivot_eq_rank` -- THE BOTTOM CONSERVATION.  When the base is
   itself the coweighted atom sum, the coweighted pivots sum to the rank.  With
   four labels and weights summing to one the coweights sum to three, so
   `sum_l (1 - weight_l)(pivot_l - 1) = 0`: either some bottom pivot is strictly
   below one -- and then the landed `posDef_sub_vecMulVec_iff` hands over a
   strictly dominating bottom triple -- or every bottom pivot is exactly one.
   That dichotomy is the whole bottom lane, and it needs no whitening: it is
   stated against a general Gram.

3. `eq_zero_of_transpose_eq_of_isIdempotent_of_trace_eq_zero` -- THE PROJECTION
   BRICK.  A symmetric idempotent real matrix of zero trace is zero, because
   `trace (M Mᵀ)` is the sum of the squared entries and equals `trace M`.  Applied
   to `Q - alpha alphaᵀ` it identifies the corank-one tie frame: the P-Gram `C` of
   the four bottom atoms, the coweight diagonal `D` and the normalised dependency
   `alpha` satisfy `D C D + alpha alphaᵀ = D`, hence `alpha_l^2 = w_l (1 - w_l)`.
   No rank theory, no spectral theorem.

4. `weighted_sq_le_neg_mul_of_mean_zero` -- BHATIA-DAVIS.  A weighted mean-zero
   family has variance at most `(-min)(max)`, by expanding the manifestly
   nonnegative `sum w (value - min)(max - value)`.  The strict form
   `weighted_sq_lt_neg_mul_of_mean_zero_of_strict_between` fires as soon as one
   positively weighted entry lies strictly inside.  On the tie frame the spike
   criterion for the triple missing the pair `{k,l}` is exactly
   `-2 xi_k xi_l > 1 + q`, so Bhatia-Davis at the argmax/argmin pair turns
   `q > 1` into domination with room to spare.

5. `dotProduct_eq_zero_of_resolution` -- THE ORTHOGONALITY BRICK.  Three
   positively weighted rank-one atoms that resolve the identity are pairwise
   ORTHOGONAL.  Both stress sides of the endpoint gauge are such a triple, so
   the three negative atoms are mutually orthogonal -- and that single fact
   closes the last case: the Bhatia-Davis slack can only vanish when a spike is
   proportional to a sub-sum of the dependency, primitivity kills the one-element
   sums, and orthogonality of the negative atoms kills the two-element ones.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.TraceIdentity
import Gtz.Reduction.EndpointGaugeDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The pivot against a general base

The residual is stated against a general Gram, not a whitened one, so the
self-pivot is taken against an arbitrary invertible base rather than against
`subsetSum D Q - 1`.  `pivotAgainst_eq_dotProduct` is the dictionary back to the
landed `pivot_eq_dot` shape. -/

/-- The self-pivot of a direction against a base matrix, as a trace. -/
noncomputable def pivotAgainst {rank : ℕ} (base : Matrix (Fin rank) (Fin rank) ℝ)
    (direction : Fin rank → ℝ) : ℝ :=
  Matrix.trace (base⁻¹ * atomMatrix direction)

/-- The trace form of the pivot is the quadratic form of the inverse. -/
theorem pivotAgainst_eq_dotProduct {rank : ℕ} (base : Matrix (Fin rank) (Fin rank) ℝ)
    (direction : Fin rank → ℝ) :
    pivotAgainst base direction = direction ⬝ᵥ (base⁻¹ *ᵥ direction) := by
  unfold pivotAgainst atomMatrix
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun outer _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Trace is linear in the atom argument of the pivot. -/
theorem sum_smul_pivotAgainst {rank size : ℕ} (base : Matrix (Fin rank) (Fin rank) ℝ)
    (coeff : Fin size → ℝ) (atomFamily : Fin size → Fin rank → ℝ) :
    ∑ label, coeff label * pivotAgainst base (atomFamily label)
      = Matrix.trace (base⁻¹ * ∑ label, coeff label • atomMatrix (atomFamily label)) := by
  rw [Matrix.mul_sum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, pivotAgainst]

/-! ## Law 1: the master identity -/

/-- **THE MASTER IDENTITY.**  A zero-sum stress annihilates the pivot defects
against ANY base: `sum_l stress_l (pivot_l - 1) = 0`.  At a total tie the four
bottom defects are zero, so the two spike defects have opposite signs and the
larger spike pivot is at least one -- the single signed scalar on which
`le_total` selects the spike. -/
theorem sum_stress_mul_pivotDefect_eq_zero {rank size : ℕ}
    (base : Matrix (Fin rank) (Fin rank) ℝ) (stressCoeff : Fin size → ℝ)
    (atomFamily : Fin size → Fin rank → ℝ)
    (hstress : ∑ label, stressCoeff label • atomMatrix (atomFamily label) = 0)
    (hzeroSum : ∑ label, stressCoeff label = 0) :
    ∑ label, stressCoeff label * (pivotAgainst base (atomFamily label) - 1) = 0 := by
  have hexpand : ∀ label,
      stressCoeff label * (pivotAgainst base (atomFamily label) - 1)
        = stressCoeff label * pivotAgainst base (atomFamily label)
          - stressCoeff label := fun label => by ring
  rw [Finset.sum_congr rfl fun label _ => hexpand label, Finset.sum_sub_distrib,
    hzeroSum, sub_zero, sum_smul_pivotAgainst, hstress, Matrix.mul_zero,
    Matrix.trace_zero]

/-! ## Law 2: the bottom conservation -/

/-- **THE CONSERVATION LAW.**  When the base IS the coweighted atom sum, the
coweighted pivots sum to the rank.  Only invertibility of the base is used, so
the statement is Gram-general: no whitening step is required anywhere in the
two-vanished lane. -/
theorem sum_coweight_mul_pivot_eq_rank {rank size : ℕ}
    (coweight : Fin size → ℝ) (atomFamily : Fin size → Fin rank → ℝ)
    (base : Matrix (Fin rank) (Fin rank) ℝ)
    (hbase : base = ∑ label, coweight label • atomMatrix (atomFamily label))
    (hunit : IsUnit base.det) :
    ∑ label, coweight label * pivotAgainst base (atomFamily label) = (rank : ℝ) := by
  rw [sum_smul_pivotAgainst, ← hbase, Matrix.nonsing_inv_mul base hunit,
    Matrix.trace_one, Fintype.card_fin]

/-- The dichotomy the conservation law produces: with four labels whose weights
sum to one the coweights sum to three, so the pivot defects cannot all be
positive.  Either some bottom pivot is strictly below one -- a strictly
dominating bottom triple, by the landed rank-one Schur dictionary -- or every
one of them is exactly one, the TOTAL TIE. -/
theorem exists_pivot_lt_one_or_forall_pivot_eq_one {rank : ℕ}
    (weight : Fin 4 → ℝ) (atomFamily : Fin 4 → Fin rank → ℝ)
    (base : Matrix (Fin rank) (Fin rank) ℝ)
    (hbase : base = ∑ label, (1 - weight label) • atomMatrix (atomFamily label))
    (hunit : IsUnit base.det) (hrank : (rank : ℝ) = 3)
    (hweightSumOne : ∑ label, weight label = 1)
    (hcoweightPos : ∀ label, 0 < 1 - weight label) :
    (∃ label, pivotAgainst base (atomFamily label) < 1)
      ∨ (∀ label, pivotAgainst base (atomFamily label) = 1) := by
  classical
  by_cases hsome : ∃ label, pivotAgainst base (atomFamily label) < 1
  · exact Or.inl hsome
  · refine Or.inr fun label => ?_
    push Not at hsome
    have hconserve := sum_coweight_mul_pivot_eq_rank (fun index => 1 - weight index)
      atomFamily base hbase hunit
    have hcoweightSum : ∑ index, (1 - weight index) = (3 : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hweightSumOne, Finset.card_univ,
        Fintype.card_fin]
      norm_num
    have hdefect : ∑ index, (1 - weight index)
        * (pivotAgainst base (atomFamily index) - 1) = 0 := by
      have hsplit : ∀ index, (1 - weight index)
          * (pivotAgainst base (atomFamily index) - 1)
            = (1 - weight index) * pivotAgainst base (atomFamily index)
              - (1 - weight index) := fun index => by ring
      rw [Finset.sum_congr rfl fun index _ => hsplit index, Finset.sum_sub_distrib,
        hconserve, hcoweightSum, hrank, sub_self]
    have hterms : ∀ index ∈ (Finset.univ : Finset (Fin 4)),
        0 ≤ (1 - weight index) * (pivotAgainst base (atomFamily index) - 1) :=
      fun index _ => mul_nonneg (le_of_lt (hcoweightPos index))
        (by linarith [hsome index])
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hdefect label
      (Finset.mem_univ label)
    have hcoweightNe : (1 - weight label) ≠ 0 := ne_of_gt (hcoweightPos label)
    have := mul_eq_zero.mp hzero
    rcases this with hcontra | hdiff
    · exact absurd hcontra hcoweightNe
    · linarith

/-! ## Law 3: the projection brick -/

/-- The Frobenius reading of the trace: `trace (M Mᵀ)` is the sum of the squared
entries. -/
theorem trace_mul_transpose_eq_sum_sq {size : ℕ} (target : Matrix (Fin size) (Fin size) ℝ) :
    Matrix.trace (target * targetᵀ) = ∑ row, ∑ col, target row col ^ 2 := by
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun row _ => by
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun col _ => (sq (target row col)).symm

/-- **THE PROJECTION BRICK.**  A symmetric idempotent real matrix of zero trace
is zero: its Frobenius norm equals its trace.  This is what identifies the
corank-one tie frame -- applied to `Q - alpha alphaᵀ` it proves `Q = alpha alphaᵀ`
without any rank theory or spectral theorem, and hence pins the dependency to
`alpha_l^2 = w_l (1 - w_l)`. -/
theorem eq_zero_of_transpose_eq_of_isIdempotent_of_trace_eq_zero {size : ℕ}
    (target : Matrix (Fin size) (Fin size) ℝ) (hsymm : targetᵀ = target)
    (hidempotent : target * target = target) (htrace : Matrix.trace target = 0) :
    target = 0 := by
  have hfrobenius : ∑ row, ∑ col, target row col ^ 2 = 0 := by
    rw [← trace_mul_transpose_eq_sum_sq, hsymm, hidempotent, htrace]
  have houter : ∀ row ∈ (Finset.univ : Finset (Fin size)),
      0 ≤ ∑ col, target row col ^ 2 :=
    fun row _ => Finset.sum_nonneg fun col _ => sq_nonneg _
  ext row col
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg houter).mp hfrobenius row
    (Finset.mem_univ row)
  have hinner : ∀ index ∈ (Finset.univ : Finset (Fin size)),
      0 ≤ target row index ^ 2 := fun index _ => sq_nonneg _
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg hinner).mp hrow col
    (Finset.mem_univ col)
  rw [Matrix.zero_apply]
  exact sq_eq_zero_iff.mp hentry

/-! ### The scaled projection brick and the corank-one tie frame

The tie frame is read off a projection statement conjugated by the coweight
diagonal.  Doing it with `D` and `D⁻¹` rather than `D^{1/2}` keeps every step
square-root free, which is what makes the whole identity rational. -/

/-- The `scale`-weighted Frobenius reading of the trace. -/
theorem trace_scaledSquare_eq_sum_sq {size : ℕ} (scale : Fin size → ℝ)
    (target : Matrix (Fin size) (Fin size) ℝ) (hsymm : targetᵀ = target) :
    Matrix.trace (Matrix.diagonal scale * target * Matrix.diagonal scale * target)
      = ∑ row, ∑ col, scale row * scale col * target row col ^ 2 := by
  have hleft : Matrix.diagonal scale * target * Matrix.diagonal scale
      = Matrix.of fun row col => scale row * target row col * scale col := by
    ext row col
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
      Finset.sum_ite_eq', mul_comm, mul_left_comm]
  rw [hleft, Matrix.trace]
  refine Finset.sum_congr rfl fun row _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun col _ => ?_
  have hflip : target col row = target row col := by
    have := congrFun (congrFun hsymm row) col
    rwa [Matrix.transpose_apply] at this
  rw [hflip]
  ring

/-- **THE SCALED PROJECTION BRICK.**  A symmetric matrix that is idempotent for
the `diagonal scale` product and has zero `diagonal scale` trace is zero.  With
`scale` the reciprocal coweights this identifies the corank-one tie frame; with
`scale = 1` it is the plain statement that a symmetric idempotent of zero trace
vanishes. -/
theorem eq_zero_of_transpose_eq_of_scaledIdempotent_of_trace_eq_zero {size : ℕ}
    (scale : Fin size → ℝ) (hscalePos : ∀ index, 0 < scale index)
    (target : Matrix (Fin size) (Fin size) ℝ) (hsymm : targetᵀ = target)
    (hidempotent : target * Matrix.diagonal scale * target = target)
    (htrace : Matrix.trace (Matrix.diagonal scale * target) = 0) :
    target = 0 := by
  have hchain : Matrix.diagonal scale * target * Matrix.diagonal scale * target
      = Matrix.diagonal scale * target := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc target,
      hidempotent]
  have hsumZero : ∑ row, ∑ col, scale row * scale col * target row col ^ 2 = 0 := by
    rw [← trace_scaledSquare_eq_sum_sq scale target hsymm, hchain, htrace]
  have houter : ∀ row ∈ (Finset.univ : Finset (Fin size)),
      0 ≤ ∑ col, scale row * scale col * target row col ^ 2 :=
    fun row _ => Finset.sum_nonneg fun col _ =>
      mul_nonneg (mul_nonneg (le_of_lt (hscalePos row)) (le_of_lt (hscalePos col)))
        (sq_nonneg _)
  ext row col
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg houter).mp hsumZero row
    (Finset.mem_univ row)
  have hinner : ∀ index ∈ (Finset.univ : Finset (Fin size)),
      0 ≤ scale row * scale index * target row index ^ 2 :=
    fun index _ => mul_nonneg (mul_nonneg (le_of_lt (hscalePos row))
      (le_of_lt (hscalePos index))) (sq_nonneg _)
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg hinner).mp hrow col
    (Finset.mem_univ col)
  have hscaleNe : scale row * scale col ≠ 0 :=
    ne_of_gt (mul_pos (hscalePos row) (hscalePos col))
  rw [Matrix.zero_apply]
  rcases mul_eq_zero.mp hentry with hcontra | hsquare
  · exact absurd hcontra hscaleNe
  · exact sq_eq_zero_iff.mp hsquare

/-- **THE CORANK-ONE TIE FRAME.**  Let `pairing` be the Gram of the carrying
atoms in the metric of the window gap, `coweight` the positive coweights, and
`dependency` the linear dependency among the atoms, normalised so that
`dependency (diagonal coweight)⁻¹ dependency = 1`.  At a TOTAL TIE -- every
diagonal entry of `pairing` equal to one -- the frame is pinned:

  `diagonal coweight * pairing * diagonal coweight + dependency dependencyᵀ
     = diagonal coweight`.

Reading the diagonal gives `dependency_l ^ 2 = weight_l (1 - weight_l)`; reading
off the diagonal gives the pairings as the normalised outer product.  That is
the whole (4,3) total-tie family, one congruence class per weight vector. -/
theorem tieFrame_of_totalTie {size : ℕ} (coweight : Fin size → ℝ)
    (hcoweightPos : ∀ label, 0 < coweight label)
    (pairing : Matrix (Fin size) (Fin size) ℝ) (hsymm : pairingᵀ = pairing)
    (hdesign : pairing * Matrix.diagonal coweight * pairing = pairing)
    (htotalTie : ∀ label, pairing label label = 1)
    (hcoweightSum : ∑ label, coweight label = (size : ℝ) - 1)
    (dependency : Fin size → ℝ)
    (hannihilates : pairing *ᵥ dependency = 0)
    (hnormalised : ∑ label, (coweight label)⁻¹ * dependency label ^ 2 = 1) :
    Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
        + Matrix.vecMulVec dependency dependency = Matrix.diagonal coweight := by
  classical
  set scale : Fin size → ℝ := fun label => (coweight label)⁻¹ with hscaleDef
  have hscalePos : ∀ label, 0 < scale label :=
    fun label => inv_pos.mpr (hcoweightPos label)
  have hnormScale : ∑ label, scale label * dependency label ^ 2 = 1 := hnormalised
  have hdiagMul : Matrix.diagonal scale * Matrix.diagonal coweight = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    refine Matrix.diagonal_eq_diagonal_iff.mpr fun label => ?_
    exact inv_mul_cancel₀ (ne_of_gt (hcoweightPos label))
  have hdiagMulOther : Matrix.diagonal coweight * Matrix.diagonal scale = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    refine Matrix.diagonal_eq_diagonal_iff.mpr fun label => ?_
    exact mul_inv_cancel₀ (ne_of_gt (hcoweightPos label))
  set residual : Matrix (Fin size) (Fin size) ℝ :=
    Matrix.diagonal coweight
      - (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
          + Matrix.vecMulVec dependency dependency) with hresidualDef
  have hgoal : residual = 0 → Matrix.diagonal coweight * pairing
      * Matrix.diagonal coweight + Matrix.vecMulVec dependency dependency
      = Matrix.diagonal coweight := by
    intro hzero
    have := sub_eq_zero.mp (hresidualDef ▸ hzero)
    exact this.symm
  refine hgoal ?_
  -- residual is symmetric
  have hpairSymmSandwich : (Matrix.diagonal coweight * pairing
      * Matrix.diagonal coweight)ᵀ
      = Matrix.diagonal coweight * pairing * Matrix.diagonal coweight := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
      hsymm, Matrix.mul_assoc]
  have houterSymm : (Matrix.vecMulVec dependency dependency)ᵀ
      = Matrix.vecMulVec dependency dependency := by
    ext row col
    simp [Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hresidualSymm : residualᵀ = residual := by
    rw [hresidualDef, Matrix.transpose_sub, Matrix.transpose_add,
      Matrix.diagonal_transpose, hpairSymmSandwich, houterSymm]
  -- the outer product is scale-idempotent by the normalisation
  have houterIdem : Matrix.vecMulVec dependency dependency * Matrix.diagonal scale
      * Matrix.vecMulVec dependency dependency
      = Matrix.vecMulVec dependency dependency := by
    ext row col
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.diagonal_apply]
    have hstep : ∀ index : Fin size,
        (∑ other, dependency row * dependency other
            * (if other = index then scale other else 0))
          * (dependency index * dependency col)
          = (scale index * dependency index ^ 2)
              * (dependency row * dependency col) := by
      intro index
      rw [Finset.sum_eq_single_of_mem index (Finset.mem_univ index)
        (fun other _ hne => by simp only [if_neg hne, mul_zero])]
      rw [if_pos (rfl : index = index)]
      ring
    rw [Finset.sum_congr rfl fun index _ => hstep index, ← Finset.sum_mul,
      hnormScale, one_mul]
  -- the sandwich is scale-idempotent by the design relation
  have hsandwichIdem : Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
      * Matrix.diagonal scale
      * (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
      = Matrix.diagonal coweight * pairing * Matrix.diagonal coweight := by
    calc Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
            * Matrix.diagonal scale
            * (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
        = Matrix.diagonal coweight
            * (pairing * (Matrix.diagonal coweight * Matrix.diagonal scale)
              * (Matrix.diagonal coweight * pairing)) * Matrix.diagonal coweight := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal coweight * (pairing * Matrix.diagonal coweight * pairing)
            * Matrix.diagonal coweight := by
          rw [hdiagMulOther]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Matrix.diagonal coweight * pairing * Matrix.diagonal coweight := by
          rw [hdesign]
  -- the two blocks annihilate each other
  have hcross : Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
      * Matrix.diagonal scale * Matrix.vecMulVec dependency dependency = 0 := by
    have hstepDiag : Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
        * Matrix.diagonal scale = Matrix.diagonal coweight * pairing := by
      simp only [Matrix.mul_assoc, hdiagMulOther, Matrix.mul_one]
    rw [hstepDiag]
    have hzeroRow : ∀ label : Fin size,
        ∑ index, pairing label index * dependency index = 0 := by
      intro label
      have hrow : pairing label ⬝ᵥ dependency = 0 := congrFun hannihilates label
      simp only [dotProduct] at hrow
      exact hrow
    ext row col
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply,
      Matrix.diagonal_apply]
    have hstep : ∀ index : Fin size,
        (∑ other, (if row = other then coweight row else 0) * pairing other index)
          * (dependency index * dependency col)
          = coweight row * dependency col * (pairing row index * dependency index) := by
      intro index
      rw [Finset.sum_eq_single_of_mem row (Finset.mem_univ row)
        (fun other _ hne => by simp only [if_neg (Ne.symm hne), zero_mul])]
      rw [if_pos (rfl : row = row)]
      ring
    rw [Finset.sum_congr rfl fun index _ => hstep index, ← Finset.mul_sum,
      hzeroRow row, mul_zero]
  have hcrossOther : Matrix.vecMulVec dependency dependency * Matrix.diagonal scale
      * (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight) = 0 := by
    have htrans := congrArg Matrix.transpose hcross
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_zero,
      houterSymm, Matrix.diagonal_transpose, hpairSymmSandwich,
      Matrix.mul_assoc] at htrans
    simp only [Matrix.mul_assoc] at htrans ⊢
    exact htrans
  -- residual is scale-idempotent
  have hresidualIdem : residual * Matrix.diagonal scale * residual = residual := by
    have hunitLeft : Matrix.diagonal coweight * Matrix.diagonal scale
        * Matrix.diagonal coweight = Matrix.diagonal coweight := by
      rw [hdiagMulOther, Matrix.one_mul]
    have hdiagSandwichLeft : Matrix.diagonal coweight * Matrix.diagonal scale
        * (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
        = Matrix.diagonal coweight * pairing * Matrix.diagonal coweight := by
      rw [hdiagMulOther, Matrix.one_mul]
    have hdiagSandwichRight : Matrix.diagonal coweight * pairing
        * Matrix.diagonal coweight * Matrix.diagonal scale
        * Matrix.diagonal coweight
        = Matrix.diagonal coweight * pairing * Matrix.diagonal coweight := by
      simp only [Matrix.mul_assoc, hdiagMulOther, Matrix.one_mul]
    have hdiagOuterLeft : Matrix.diagonal coweight * Matrix.diagonal scale
        * Matrix.vecMulVec dependency dependency
        = Matrix.vecMulVec dependency dependency := by
      rw [hdiagMulOther, Matrix.one_mul]
    have hdiagOuterRight : Matrix.vecMulVec dependency dependency
        * Matrix.diagonal scale * Matrix.diagonal coweight
        = Matrix.vecMulVec dependency dependency := by
      rw [Matrix.mul_assoc, hdiagMul, Matrix.mul_one]
    rw [hresidualDef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      hunitLeft, hdiagSandwichLeft, hdiagOuterLeft, hdiagSandwichRight,
      hdiagOuterRight, hsandwichIdem, houterIdem, hcross, hcrossOther]
    abel
  -- residual has zero scale-trace
  have htraceResidual : Matrix.trace (Matrix.diagonal scale * residual) = 0 := by
    have hdiagTrace : Matrix.trace (Matrix.diagonal scale * Matrix.diagonal coweight)
        = (size : ℝ) := by
      rw [hdiagMul, Matrix.trace_one, Fintype.card_fin]
    have hsandwichTrace : Matrix.trace (Matrix.diagonal scale
        * (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight))
        = (size : ℝ) - 1 := by
      have hcollapse : Matrix.diagonal scale
          * (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
          = pairing * Matrix.diagonal coweight := by
        simp only [← Matrix.mul_assoc, hdiagMul, Matrix.one_mul]
      rw [hcollapse, Matrix.trace]
      have hentry : ∀ label, (pairing * Matrix.diagonal coweight) label label
          = coweight label := by
        intro label
        simp only [Matrix.mul_apply, Matrix.diagonal_apply]
        rw [Finset.sum_eq_single_of_mem label (Finset.mem_univ label)
          (fun other _ hne => by simp only [if_neg hne, mul_zero])]
        rw [if_pos (rfl : label = label), htotalTie label, one_mul]
      simp only [Matrix.diag_apply]
      rw [Finset.sum_congr rfl fun label _ => hentry label, hcoweightSum]
    have houterTrace : Matrix.trace (Matrix.diagonal scale
        * Matrix.vecMulVec dependency dependency) = 1 := by
      rw [Matrix.trace]
      have hentry : ∀ label, (Matrix.diagonal scale
          * Matrix.vecMulVec dependency dependency) label label
          = scale label * dependency label ^ 2 := by
        intro label
        simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
        rw [Finset.sum_eq_single_of_mem label (Finset.mem_univ label)
          (fun other _ hne => by simp only [if_neg (Ne.symm hne), zero_mul])]
        rw [if_pos (rfl : label = label)]
        ring
      simp only [Matrix.diag_apply]
      rw [Finset.sum_congr rfl fun label _ => hentry label]
      exact hnormalised
    rw [hresidualDef, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub,
      Matrix.trace_add, hdiagTrace, hsandwichTrace, houterTrace]
    ring
  exact eq_zero_of_transpose_eq_of_scaledIdempotent_of_trace_eq_zero scale hscalePos
    residual hresidualSymm hresidualIdem htraceResidual

/-- **THE DEPENDENCY SQUARE LAW.**  Reading the diagonal of the tie frame: the
normalised dependency coefficient at a label is the geometric mean of its
coweight and its weight.  With `coweight = 1 - weight` this is
`dependency_l ^ 2 = weight_l (1 - weight_l)` -- the closed form of the (4,3)
total-tie family, one congruence class for each weight vector. -/
theorem dependency_sq_eq_of_tieFrame {size : ℕ} (coweight : Fin size → ℝ)
    (pairing : Matrix (Fin size) (Fin size) ℝ) (dependency : Fin size → ℝ)
    (htotalTie : ∀ label, pairing label label = 1)
    (hframe : Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
      + Matrix.vecMulVec dependency dependency = Matrix.diagonal coweight)
    (label : Fin size) :
    dependency label ^ 2 = coweight label * (1 - coweight label) := by
  have hentry : (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
      label label + dependency label * dependency label = coweight label := by
    have hraw := congrFun (congrFun hframe label) label
    simpa [Matrix.add_apply, Matrix.vecMulVec_apply] using hraw
  have hsandwich : (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
      label label = coweight label * coweight label := by
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single_of_mem label (Finset.mem_univ label)
      (fun other _ hne => by simp only [if_neg hne, mul_zero])]
    rw [if_pos (rfl : label = label),
      Finset.sum_eq_single_of_mem label (Finset.mem_univ label)
        (fun other _ hne => by simp only [if_neg (Ne.symm hne), zero_mul])]
    rw [if_pos (rfl : label = label), htotalTie label]
    ring
  rw [hsandwich] at hentry
  nlinarith [hentry]

/-- **THE TIE PAIRING FORMULA.**  Reading the tie frame off the diagonal: every
pairing of two distinct carrying atoms in the window metric is the negated
normalised outer product of the dependency.  Together with the square law this
fixes the whole Gram of the total-tie family from the weights alone. -/
theorem pairing_eq_of_tieFrame {size : ℕ} (coweight : Fin size → ℝ)
    (pairing : Matrix (Fin size) (Fin size) ℝ) (dependency : Fin size → ℝ)
    (hframe : Matrix.diagonal coweight * pairing * Matrix.diagonal coweight
      + Matrix.vecMulVec dependency dependency = Matrix.diagonal coweight)
    {leftLabel rightLabel : Fin size} (hne : leftLabel ≠ rightLabel) :
    coweight leftLabel * coweight rightLabel * pairing leftLabel rightLabel
      = -(dependency leftLabel * dependency rightLabel) := by
  have hentry : (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
      leftLabel rightLabel + dependency leftLabel * dependency rightLabel = 0 := by
    have hraw := congrFun (congrFun hframe leftLabel) rightLabel
    simpa [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.diagonal_apply,
      if_neg hne] using hraw
  have hsandwich : (Matrix.diagonal coweight * pairing * Matrix.diagonal coweight)
      leftLabel rightLabel
      = coweight leftLabel * coweight rightLabel * pairing leftLabel rightLabel := by
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single_of_mem rightLabel (Finset.mem_univ rightLabel)
      (fun other _ hother => by simp only [if_neg hother, mul_zero])]
    rw [if_pos (rfl : rightLabel = rightLabel),
      Finset.sum_eq_single_of_mem leftLabel (Finset.mem_univ leftLabel)
        (fun other _ hother => by simp only [if_neg (Ne.symm hother), zero_mul])]
    rw [if_pos (rfl : leftLabel = leftLabel)]
    ring
  rw [hsandwich] at hentry
  linarith

/-! ## Law 4: Bhatia-Davis -/

/-- **BHATIA-DAVIS.**  A weighted mean-zero family has weighted mean square at
most `(-min)(max)`.  The proof is the nonnegativity of
`sum weight (value - lowValue)(highValue - value)`, expanded against the
mean-zero law.  On the tie frame the spike criterion reads
`-2 xi_k xi_l > 1 + variance` at the argmax/argmin pair, so this bound converts
`variance > 1` into strict domination. -/
theorem weighted_sq_le_neg_mul_of_mean_zero {index : Type*} [Fintype index]
    (weight value : index → ℝ) (lowIndex highIndex : index)
    (hweightNonneg : ∀ entry, 0 ≤ weight entry)
    (hmeanZero : ∑ entry, weight entry * value entry = 0)
    (hlow : ∀ entry, value lowIndex ≤ value entry)
    (high : ∀ entry, value entry ≤ value highIndex) :
    ∑ entry, weight entry * value entry ^ 2
      ≤ -(value lowIndex * value highIndex) * ∑ entry, weight entry := by
  have hslackNonneg : 0 ≤ ∑ entry, weight entry
      * ((value entry - value lowIndex) * (value highIndex - value entry)) :=
    Finset.sum_nonneg fun entry _ =>
      mul_nonneg (hweightNonneg entry)
        (mul_nonneg (by linarith [hlow entry]) (by linarith [high entry]))
  have hexpand : ∀ entry, weight entry
      * ((value entry - value lowIndex) * (value highIndex - value entry))
        = (value lowIndex + value highIndex) * (weight entry * value entry)
          - weight entry * value entry ^ 2
          - (value lowIndex * value highIndex) * weight entry := fun entry => by ring
  rw [Finset.sum_congr rfl fun entry _ => hexpand entry, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hmeanZero,
    mul_zero, zero_sub] at hslackNonneg
  linarith

/-- The strict form: one positively weighted entry sitting strictly between the
extremes makes the Bhatia-Davis slack positive.  This is the escape from the
degenerate slice where both spike pivots equal one exactly. -/
theorem weighted_sq_lt_neg_mul_of_mean_zero_of_strict_between {index : Type*}
    [Fintype index] (weight value : index → ℝ) (lowIndex highIndex insideIndex : index)
    (hweightNonneg : ∀ entry, 0 ≤ weight entry)
    (hmeanZero : ∑ entry, weight entry * value entry = 0)
    (hlow : ∀ entry, value lowIndex ≤ value entry)
    (high : ∀ entry, value entry ≤ value highIndex)
    (hinsideWeight : 0 < weight insideIndex)
    (hinsideAbove : value lowIndex < value insideIndex)
    (hinsideBelow : value insideIndex < value highIndex) :
    ∑ entry, weight entry * value entry ^ 2
      < -(value lowIndex * value highIndex) * ∑ entry, weight entry := by
  classical
  have hterms : ∀ entry ∈ (Finset.univ : Finset index), 0 ≤ weight entry
      * ((value entry - value lowIndex) * (value highIndex - value entry)) :=
    fun entry _ => mul_nonneg (hweightNonneg entry)
      (mul_nonneg (by linarith [hlow entry]) (by linarith [high entry]))
  have hwitness : 0 < weight insideIndex
      * ((value insideIndex - value lowIndex)
          * (value highIndex - value insideIndex)) :=
    mul_pos hinsideWeight (mul_pos (by linarith) (by linarith))
  have hslackPos : 0 < ∑ entry, weight entry
      * ((value entry - value lowIndex) * (value highIndex - value entry)) :=
    lt_of_lt_of_le hwitness
      (Finset.single_le_sum hterms (Finset.mem_univ insideIndex))
  have hexpand : ∀ entry, weight entry
      * ((value entry - value lowIndex) * (value highIndex - value entry))
        = (value lowIndex + value highIndex) * (weight entry * value entry)
          - weight entry * value entry ^ 2
          - (value lowIndex * value highIndex) * weight entry := fun entry => by ring
  rw [Finset.sum_congr rfl fun entry _ => hexpand entry, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hmeanZero,
    mul_zero, zero_sub] at hslackPos
  linarith

/-! ## Law 5: the orthogonality brick -/

/-- The frame matrix of a family: its columns are the atoms. -/
def frameOfFamily {rank : ℕ} (atomFamily : Fin rank → Fin rank → ℝ) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  Matrix.of fun row col => atomFamily col row

/-- The coweighted atom sum is the frame sandwiching the coefficient diagonal. -/
theorem sum_smul_atomMatrix_eq_frame_sandwich {rank : ℕ}
    (coeff : Fin rank → ℝ) (atomFamily : Fin rank → Fin rank → ℝ) :
    ∑ label, coeff label • atomMatrix (atomFamily label)
      = frameOfFamily atomFamily * Matrix.diagonal coeff
          * (frameOfFamily atomFamily)ᵀ := by
  ext row col
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, frameOfFamily,
    Matrix.of_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun outer _ => ?_
  rw [Finset.sum_eq_single_of_mem outer (Finset.mem_univ outer)
    (fun other _ hne => by simp only [if_neg hne, mul_zero])]
  rw [if_pos (rfl : outer = outer)]
  ring

/-- **THE ORTHOGONALITY BRICK.**  Rank-many positively weighted rank-one atoms
that resolve the identity are pairwise ORTHOGONAL, with squared norms the
reciprocal coefficients.  Both stress sides of the diagonal endpoint gauge are
such a family, so the three negative atoms are mutually orthogonal -- the fact
that closes the last case of the two-vanished lane. -/
theorem dotProduct_eq_zero_of_resolution {rank : ℕ}
    (coeff : Fin rank → ℝ) (atomFamily : Fin rank → Fin rank → ℝ)
    (hcoeffPos : ∀ label, 0 < coeff label)
    (hresolution : ∑ label, coeff label • atomMatrix (atomFamily label) = 1)
    {leftLabel rightLabel : Fin rank} (hne : leftLabel ≠ rightLabel) :
    atomFamily leftLabel ⬝ᵥ atomFamily rightLabel = 0 := by
  classical
  set frame := frameOfFamily atomFamily with hframeDef
  have hsandwich : frame * Matrix.diagonal coeff * frameᵀ = 1 := by
    rw [hframeDef, ← sum_smul_atomMatrix_eq_frame_sandwich]
    exact hresolution
  have hdiagUnit : IsUnit (Matrix.diagonal coeff).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      fun label _ => ne_of_gt (hcoeffPos label))
  have hframeUnit : IsUnit frame.det := by
    have hdet : frame.det * (Matrix.diagonal coeff).det * frameᵀ.det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.det_mul, hsandwich, Matrix.det_one]
    refine isUnit_iff_ne_zero.mpr fun hzero => ?_
    rw [hzero] at hdet
    simp at hdet
  -- from frame * diagonal * frameᵀ = 1 we get frameᵀ * frame = diagonal⁻¹
  have hinverse : frameᵀ = (Matrix.diagonal coeff)⁻¹ * frame⁻¹ := by
    have hleft : frame⁻¹ * (frame * Matrix.diagonal coeff * frameᵀ) = frame⁻¹ := by
      rw [hsandwich, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul frame hframeUnit, Matrix.one_mul] at hleft
    have := congrArg (fun target => (Matrix.diagonal coeff)⁻¹ * target) hleft
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdiagUnit] using this
  have hgram : frameᵀ * frame = (Matrix.diagonal coeff)⁻¹ := by
    rw [hinverse, Matrix.mul_assoc, Matrix.nonsing_inv_mul frame hframeUnit,
      Matrix.mul_one]
  have hentry := congrFun (congrFun hgram leftLabel) rightLabel
  rw [Matrix.mul_apply] at hentry
  have hleftSide : ∑ coord, frameᵀ leftLabel coord * frame coord rightLabel
      = atomFamily leftLabel ⬝ᵥ atomFamily rightLabel := by
    simp only [Matrix.transpose_apply, hframeDef, frameOfFamily, Matrix.of_apply,
      dotProduct]
  rw [hleftSide] at hentry
  rw [hentry, Matrix.inv_diagonal]
  simp only [Matrix.diagonal_apply, if_neg hne]


/-! # Part II: the full mechanization of the two-vanished residual

Everything below turns the Part I laws into the kernel theorem
`twoVanishedRigidBottomDomination_holds`.  The layers, bottom to top:
vector/matrix plumbing; the two-for-one exchange step (Sherman-Morrison by
explicit solution vectors, no inverse formula); the Bhatia-Davis selection
lemma; the two-valued spike decomposition; the geometric impossibility of a
doubly paired spike pair; the spike-lane engine; and the assembly. -/

/-! ## Plumbing: dot products, rank-one actions, weighted sums -/

/-- The inverse-metric pairing is symmetric whenever the matrix is. -/
theorem dotProduct_mulVec_comm_of_transpose_eq {rank : ℕ}
    {symmetricMat : Matrix (Fin rank) (Fin rank) ℝ}
    (hsymm : symmetricMatᵀ = symmetricMat) (leftVector rightVector : Fin rank → ℝ) :
    leftVector ⬝ᵥ (symmetricMat *ᵥ rightVector)
      = rightVector ⬝ᵥ (symmetricMat *ᵥ leftVector) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun colIdx _ => Finset.sum_congr rfl fun rowIdx _ => ?_
  have hentry : symmetricMat colIdx rowIdx = symmetricMat rowIdx colIdx := by
    have hflip := congrFun (congrFun hsymm rowIdx) colIdx
    rwa [Matrix.transpose_apply] at hflip
  rw [hentry]
  ring

/-- A rank-one matrix acts on a vector by pairing and scaling. -/
theorem vecMulVec_mulVec_eq_dotProduct_smul {rank : ℕ}
    (baseVector otherVector probeVector : Fin rank → ℝ) :
    Matrix.vecMulVec baseVector otherVector *ᵥ probeVector
      = (otherVector ⬝ᵥ probeVector) • baseVector := by
  funext rowIdx
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun colIdx _ => by ring

/-- An atom acts on a vector by pairing and scaling. -/
theorem atomMatrix_mulVec_eq_dotProduct_smul {rank : ℕ}
    (baseVector probeVector : Fin rank → ℝ) :
    atomMatrix baseVector *ᵥ probeVector = (baseVector ⬝ᵥ probeVector) • baseVector :=
  vecMulVec_mulVec_eq_dotProduct_smul baseVector baseVector probeVector

/-- The quadratic form of an atom is the squared pairing. -/
theorem dotProduct_atomMatrix_mulVec_eq_sq {rank : ℕ}
    (baseVector probeVector : Fin rank → ℝ) :
    probeVector ⬝ᵥ (atomMatrix baseVector *ᵥ probeVector)
      = (baseVector ⬝ᵥ probeVector) ^ 2 := by
  rw [atomMatrix_mulVec_eq_dotProduct_smul, dotProduct_smul, smul_eq_mul,
    dotProduct_comm]
  ring

/-- A matrix pushes through a weighted sum of vectors. -/
theorem mulVec_sum_smul {rank size : ℕ} (mat : Matrix (Fin rank) (Fin rank) ℝ)
    (coeff : Fin size → ℝ) (vecFamily : Fin size → Fin rank → ℝ) :
    mat *ᵥ (∑ idx, coeff idx • vecFamily idx)
      = ∑ idx, coeff idx • (mat *ᵥ vecFamily idx) := by
  funext rowIdx
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun idx _ => Finset.sum_congr rfl fun colIdx _ => by ring

/-- A weighted sum of vectors pairs against a target term by term. -/
theorem sum_smul_dotProduct {rank size : ℕ} (coeff : Fin size → ℝ)
    (vecFamily : Fin size → Fin rank → ℝ) (target : Fin rank → ℝ) :
    (∑ idx, coeff idx • vecFamily idx) ⬝ᵥ target
      = ∑ idx, coeff idx * (vecFamily idx ⬝ᵥ target) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun idx _ => Finset.sum_congr rfl fun coordIdx _ => by ring

/-- The bilinear form of a weighted atom sum: both slots see every atom. -/
theorem dotProduct_weightedAtomSum_mulVec {rank size : ℕ} (coeff : Fin size → ℝ)
    (atomFamily : Fin size → Fin rank → ℝ) (leftVector rightVector : Fin rank → ℝ) :
    leftVector ⬝ᵥ ((∑ idx, coeff idx • atomMatrix (atomFamily idx)) *ᵥ rightVector)
      = ∑ idx, coeff idx * (atomFamily idx ⬝ᵥ leftVector)
          * (atomFamily idx ⬝ᵥ rightVector) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, atomMatrix_mulVec_eq_dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm leftVector]
  ring

/-- A weighted atom sum is its own transpose. -/
theorem transpose_weightedAtomSum {rank size : ℕ} (coeff : Fin size → ℝ)
    (atomFamily : Fin size → Fin rank → ℝ) :
    (∑ idx, coeff idx • atomMatrix (atomFamily idx))ᵀ
      = ∑ idx, coeff idx • atomMatrix (atomFamily idx) := by
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [Matrix.transpose_smul,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (atomFamily idx)).1]

/-! ## Plumbing: index bookkeeping -/

/-- Two distinct indices of `Fin 3` leave exactly one survivor, and the three
of them cover. -/
theorem exists_thirdIndex_fin3 : ∀ (firstIdx secondIdx : Fin 3),
    firstIdx ≠ secondIdx → ∃ thirdIdx : Fin 3, thirdIdx ≠ firstIdx
      ∧ thirdIdx ≠ secondIdx
      ∧ ∀ anyIdx : Fin 3, anyIdx = firstIdx ∨ anyIdx = secondIdx ∨ anyIdx = thirdIdx := by
  decide

/-- A `Fin 3` sum splits into three named terms once a distinct cover is given. -/
theorem sum_eq_add_add_of_coverFin3 {carrier : Type*} [AddCommMonoid carrier]
    {firstIdx secondIdx thirdIdx : Fin 3}
    (hfirstSecond : firstIdx ≠ secondIdx) (hfirstThird : firstIdx ≠ thirdIdx)
    (hsecondThird : secondIdx ≠ thirdIdx)
    (hcover : ∀ anyIdx : Fin 3, anyIdx = firstIdx ∨ anyIdx = secondIdx ∨ anyIdx = thirdIdx)
    (summand : Fin 3 → carrier) :
    ∑ idx, summand idx = summand firstIdx + summand secondIdx + summand thirdIdx := by
  classical
  have huniv : (Finset.univ : Finset (Fin 3)) = {firstIdx, secondIdx, thirdIdx} := by
    ext anyIdx
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact hcover anyIdx
  rw [huniv, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hfirstSecond, hfirstThird⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hsecondThird),
    Finset.sum_singleton, add_assoc]

/-- A `Fin 6` sum splits along the two sign enumerations of a full-support
stress: positives first, negatives second. -/
theorem sum_fin6_eq_posSum_add_negSum {carrier : Type*} [AddCommMonoid carrier]
    {stressCoeff : Fin 6 → ℝ} {posEnum negEnum : Fin 3 → Fin 6}
    (hfull : ∀ label, stressCoeff label ≠ 0)
    (hposInjective : Function.Injective posEnum)
    (hposSign : ∀ posIdx, 0 < stressCoeff (posEnum posIdx))
    (hposOnto : ∀ label, 0 < stressCoeff label → ∃ posIdx, posEnum posIdx = label)
    (hnegInjective : Function.Injective negEnum)
    (hnegSign : ∀ negIdx, stressCoeff (negEnum negIdx) < 0)
    (hnegOnto : ∀ label, stressCoeff label < 0 → ∃ negIdx, negEnum negIdx = label)
    (summand : Fin 6 → carrier) :
    ∑ label, summand label
      = ∑ posIdx, summand (posEnum posIdx) + ∑ negIdx, summand (negEnum negIdx) := by
  classical
  have hdisjoint : Disjoint (Finset.univ.image posEnum) (Finset.univ.image negEnum) := by
    refine Finset.disjoint_left.mpr fun label hpos hneg => ?_
    obtain ⟨posIdx, _, hposEq⟩ := Finset.mem_image.mp hpos
    obtain ⟨negIdx, _, hnegEq⟩ := Finset.mem_image.mp hneg
    have hposVal := hposSign posIdx
    have hnegVal := hnegSign negIdx
    rw [hposEq] at hposVal
    rw [hnegEq] at hnegVal
    exact absurd (hposVal.trans hnegVal) (lt_irrefl 0)
  have hunion : Finset.univ.image posEnum ∪ Finset.univ.image negEnum
      = Finset.univ := by
    refine Finset.eq_univ_of_forall fun label => ?_
    rcases lt_or_gt_of_ne (Ne.symm (hfull label)) with hpos | hneg
    swap
    · obtain ⟨negIdx, hnegEq⟩ := hnegOnto label hneg
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨negIdx, Finset.mem_univ negIdx, hnegEq⟩)
    · obtain ⟨posIdx, hposEq⟩ := hposOnto label hpos
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨posIdx, Finset.mem_univ posIdx, hposEq⟩)
  rw [← hunion, Finset.sum_union hdisjoint,
    Finset.sum_image fun leftIdx _ rightIdx _ hEq => hposInjective hEq,
    Finset.sum_image fun leftIdx _ rightIdx _ hEq => hnegInjective hEq]


/-! ## The two-for-one exchange step

`twoRankOne_exchange_posDef` is the reusable kit lemma the coordinator asked
for: remove two unit-pivot rank-ones from a positive definite window and add
one incoming rank-one; the exchange stays positive definite exactly under a
single scalar criterion on the three inverse-metric pairings.  The proof runs
the landed rank-one Schur dictionary twice; each inverse evaluation is done by
EXHIBITING the solution vector of the corresponding linear system, so no
Sherman-Morrison matrix identity is ever needed. -/

/-- **THE TWO-FOR-ONE EXCHANGE.**  Let `window` be positive definite, let both
removed directions have unit self-pivot in the inverse metric, and write
`crossPair`, `crossFirst`, `crossSecond`, `selfIncoming` for the remaining
pairings.  If

  `crossPair ^ 2 * (1 + selfIncoming) < 2 * crossPair * crossFirst * crossSecond`

then `window - removedFirst removedFirstᵀ - removedSecond removedSecondᵀ
+ incoming incomingᵀ` is positive definite.  At a (4,3) total tie every bottom
triple sits at unit pivot, so this criterion is the exact gate of the spike
lane. -/
theorem twoRankOne_exchange_posDef {rank : ℕ}
    (window : Matrix (Fin rank) (Fin rank) ℝ) (hwindow : window.PosDef)
    (removedFirst removedSecond incoming : Fin rank → ℝ)
    (hfirstUnit : removedFirst ⬝ᵥ (window⁻¹ *ᵥ removedFirst) = 1)
    (hsecondUnit : removedSecond ⬝ᵥ (window⁻¹ *ᵥ removedSecond) = 1)
    (hincomingNonneg : 0 ≤ incoming ⬝ᵥ (window⁻¹ *ᵥ incoming))
    (hcriterion : (removedFirst ⬝ᵥ (window⁻¹ *ᵥ removedSecond)) ^ 2
          * (1 + incoming ⬝ᵥ (window⁻¹ *ᵥ incoming))
        < 2 * (removedFirst ⬝ᵥ (window⁻¹ *ᵥ removedSecond))
          * (removedFirst ⬝ᵥ (window⁻¹ *ᵥ incoming))
          * (removedSecond ⬝ᵥ (window⁻¹ *ᵥ incoming))) :
    (window - atomMatrix removedFirst - atomMatrix removedSecond
      + atomMatrix incoming).PosDef := by
  classical
  set crossPair := removedFirst ⬝ᵥ (window⁻¹ *ᵥ removedSecond) with hcrossPairDef
  set crossFirst := removedFirst ⬝ᵥ (window⁻¹ *ᵥ incoming) with hcrossFirstDef
  set crossSecond := removedSecond ⬝ᵥ (window⁻¹ *ᵥ incoming) with hcrossSecondDef
  set selfIncoming := incoming ⬝ᵥ (window⁻¹ *ᵥ incoming) with hselfDef
  have honePlus : 0 < 1 + selfIncoming := by linarith
  have hcrossFirstNe : crossFirst ≠ 0 := by
    intro hzero
    rw [hzero] at hcriterion
    nlinarith [sq_nonneg crossPair, honePlus]
  have hcrossSecondNe : crossSecond ≠ 0 := by
    intro hzero
    rw [hzero] at hcriterion
    nlinarith [sq_nonneg crossPair, honePlus]
  -- the symmetric inverse pairing
  have hwindowSymm : windowᵀ = window := PosDef.transpose_eq hwindow
  have hinvSymm : (window⁻¹)ᵀ = window⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hwindowSymm]
  have hpairComm : ∀ leftVector rightVector : Fin rank → ℝ,
      leftVector ⬝ᵥ (window⁻¹ *ᵥ rightVector)
        = rightVector ⬝ᵥ (window⁻¹ *ᵥ leftVector) :=
    dotProduct_mulVec_comm_of_transpose_eq hinvSymm
  have hdetWindow : IsUnit window.det := isUnit_iff_ne_zero.mpr (ne_of_gt hwindow.det_pos)
  have hwindowInvAction : ∀ probeVector : Fin rank → ℝ,
      window *ᵥ (window⁻¹ *ᵥ probeVector) = probeVector := fun probeVector => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetWindow, Matrix.one_mulVec]
  -- the augmented window
  set augmented := window + atomMatrix incoming with haugmentedDef
  have haugmentedPosDef : augmented.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨hwindow.1.add (posSemidef_atomMatrix incoming).1, fun probeVector hprobe => ?_⟩
    rw [star_trivial, haugmentedDef, Matrix.add_mulVec, dotProduct_add,
      dotProduct_atomMatrix_mulVec_eq_sq]
    have hbase := (Matrix.posDef_iff_dotProduct_mulVec.mp hwindow).2 hprobe
    rw [star_trivial] at hbase
    nlinarith [sq_nonneg (incoming ⬝ᵥ probeVector)]
  have hdetAugmented : IsUnit augmented.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt haugmentedPosDef.det_pos)
  -- solve the augmented system at the first removed direction
  set lamFirst := crossFirst / (1 + selfIncoming) with hlamFirstDef
  set solFirst := window⁻¹ *ᵥ removedFirst - lamFirst • (window⁻¹ *ᵥ incoming)
    with hsolFirstDef
  have hincomingDotSolFirst : incoming ⬝ᵥ solFirst = lamFirst := by
    rw [hsolFirstDef, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hpairComm incoming removedFirst, ← hcrossFirstDef, ← hselfDef, hlamFirstDef]
    field_simp
    ring
  have hsolveFirst : augmented *ᵥ solFirst = removedFirst := by
    rw [haugmentedDef, Matrix.add_mulVec, hsolFirstDef, Matrix.mulVec_sub,
      Matrix.mulVec_smul, hwindowInvAction, hwindowInvAction,
      atomMatrix_mulVec_eq_dotProduct_smul, ← hsolFirstDef, hincomingDotSolFirst]
    abel
  have hinvAugFirst : augmented⁻¹ *ᵥ removedFirst = solFirst := by
    rw [← hsolveFirst, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetAugmented,
      Matrix.one_mulVec]
  have hfirstPivotAug : removedFirst ⬝ᵥ (augmented⁻¹ *ᵥ removedFirst)
      = 1 - crossFirst ^ 2 / (1 + selfIncoming) := by
    rw [hinvAugFirst, hsolFirstDef, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hfirstUnit, ← hcrossFirstDef, hlamFirstDef]
    ring
  have hfirstDefectPos : 0 < crossFirst ^ 2 / (1 + selfIncoming) :=
    div_pos (lt_of_le_of_ne (sq_nonneg crossFirst)
      (Ne.symm (pow_ne_zero 2 hcrossFirstNe))) honePlus
  have hstepOne : (augmented - Matrix.vecMulVec removedFirst removedFirst).PosDef :=
    (posDef_sub_vecMulVec_iff augmented haugmentedPosDef removedFirst).mpr
      (by rw [hfirstPivotAug]; linarith)
  set deflated := augmented - atomMatrix removedFirst with hdeflatedDef
  have hdeflatedPosDef : deflated.PosDef := hstepOne
  have hdetDeflated : IsUnit deflated.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hdeflatedPosDef.det_pos)
  -- solve the augmented system at the second removed direction
  set lamSecond := crossSecond / (1 + selfIncoming) with hlamSecondDef
  set solSecondAug := window⁻¹ *ᵥ removedSecond - lamSecond • (window⁻¹ *ᵥ incoming)
    with hsolSecondAugDef
  have hincomingDotSolSecondAug : incoming ⬝ᵥ solSecondAug = lamSecond := by
    rw [hsolSecondAugDef, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hpairComm incoming removedSecond, ← hcrossSecondDef, ← hselfDef, hlamSecondDef]
    field_simp
    ring
  have hsolveSecondAug : augmented *ᵥ solSecondAug = removedSecond := by
    rw [haugmentedDef, Matrix.add_mulVec, hsolSecondAugDef, Matrix.mulVec_sub,
      Matrix.mulVec_smul, hwindowInvAction, hwindowInvAction,
      atomMatrix_mulVec_eq_dotProduct_smul, ← hsolSecondAugDef,
      hincomingDotSolSecondAug]
    abel
  -- the off-diagonal entry and the first defect
  set offDiag := crossPair - crossFirst * crossSecond / (1 + selfIncoming)
    with hoffDiagDef
  set defectFirst := crossFirst ^ 2 / (1 + selfIncoming) with hdefectFirstDef
  have hdefectFirstPos : 0 < defectFirst := hfirstDefectPos
  have hfirstDotSolSecondAug : removedFirst ⬝ᵥ solSecondAug = offDiag := by
    rw [hsolSecondAugDef, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      ← hcrossPairDef, ← hcrossFirstDef, hoffDiagDef, hlamSecondDef]
    ring
  have hfirstDotSolFirst : removedFirst ⬝ᵥ solFirst = 1 - defectFirst := by
    rw [hsolFirstDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfirstUnit,
      ← hcrossFirstDef, hlamFirstDef, hdefectFirstDef]
    ring
  -- solve the deflated system at the second removed direction
  set solSecond := solSecondAug + (offDiag / defectFirst) • solFirst
    with hsolSecondDef
  have hfirstDotSolSecond : removedFirst ⬝ᵥ solSecond
      = offDiag + (offDiag / defectFirst) * (1 - defectFirst) := by
    rw [hsolSecondDef, dotProduct_add, dotProduct_smul, smul_eq_mul,
      hfirstDotSolSecondAug, hfirstDotSolFirst]
  have hsolveSecond : deflated *ᵥ solSecond = removedSecond := by
    rw [hdeflatedDef, Matrix.sub_mulVec, hsolSecondDef, Matrix.mulVec_add,
      Matrix.mulVec_smul, hsolveFirst, hsolveSecondAug,
      atomMatrix_mulVec_eq_dotProduct_smul, ← hsolSecondDef, hfirstDotSolSecond]
    have hcoeff : offDiag / defectFirst
        - (offDiag + offDiag / defectFirst * (1 - defectFirst)) = 0 := by
      field_simp
      ring
    have hcollect : removedSecond + (offDiag / defectFirst) • removedFirst
        - (offDiag + offDiag / defectFirst * (1 - defectFirst)) • removedFirst
        = removedSecond
          + (offDiag / defectFirst
              - (offDiag + offDiag / defectFirst * (1 - defectFirst))) • removedFirst := by
      rw [sub_smul]
      abel
    rw [hcollect, hcoeff, zero_smul, add_zero]
  have hinvDeflSecond : deflated⁻¹ *ᵥ removedSecond = solSecond := by
    rw [← hsolveSecond, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetDeflated,
      Matrix.one_mulVec]
  have hsecondDotSolSecondAug : removedSecond ⬝ᵥ solSecondAug
      = 1 - crossSecond ^ 2 / (1 + selfIncoming) := by
    rw [hsolSecondAugDef, dotProduct_sub, dotProduct_smul, smul_eq_mul, hsecondUnit,
      ← hcrossSecondDef, hlamSecondDef]
    ring
  have hsecondDotSolFirst : removedSecond ⬝ᵥ solFirst = offDiag := by
    rw [hsolFirstDef, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hpairComm removedSecond removedFirst, ← hcrossPairDef, ← hcrossSecondDef,
      hoffDiagDef, hlamFirstDef]
    ring
  have hsecondPivotDefl : removedSecond ⬝ᵥ (deflated⁻¹ *ᵥ removedSecond)
      = 1 - crossSecond ^ 2 / (1 + selfIncoming) + offDiag ^ 2 / defectFirst := by
    rw [hinvDeflSecond, hsolSecondDef, dotProduct_add, dotProduct_smul, smul_eq_mul,
      hsecondDotSolSecondAug, hsecondDotSolFirst]
    ring
  -- the criterion pays for the second defect
  have hoffScaled : offDiag * (1 + selfIncoming)
      = crossPair * (1 + selfIncoming) - crossFirst * crossSecond := by
    rw [hoffDiagDef]
    field_simp
  have hkey : (crossPair * (1 + selfIncoming) - crossFirst * crossSecond) ^ 2
      < (crossFirst * crossSecond) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hcriterion honePlus]
  have hsecondLt : removedSecond ⬝ᵥ (deflated⁻¹ *ᵥ removedSecond) < 1 := by
    rw [hsecondPivotDefl]
    have hscaledSq : (offDiag * (1 + selfIncoming)) ^ 2
        < (crossFirst * crossSecond) ^ 2 := by
      rw [hoffScaled]
      exact hkey
    have hdefectValue : offDiag ^ 2 / defectFirst
        = offDiag ^ 2 * (1 + selfIncoming) / crossFirst ^ 2 := by
      rw [hdefectFirstDef]
      field_simp
    have hcompare : offDiag ^ 2 * (1 + selfIncoming) / crossFirst ^ 2
        < crossSecond ^ 2 / (1 + selfIncoming) := by
      rw [div_lt_div_iff₀ (lt_of_le_of_ne (sq_nonneg crossFirst)
        (Ne.symm (pow_ne_zero 2 hcrossFirstNe))) honePlus]
      nlinarith [hscaledSq]
    rw [hdefectValue]
    linarith
  have hstepTwo : (deflated - Matrix.vecMulVec removedSecond removedSecond).PosDef :=
    (posDef_sub_vecMulVec_iff deflated hdeflatedPosDef removedSecond).mpr hsecondLt
  have hfinal : window - atomMatrix removedFirst - atomMatrix removedSecond
      + atomMatrix incoming
      = deflated - Matrix.vecMulVec removedSecond removedSecond := by
    rw [hdeflatedDef, haugmentedDef,
      show Matrix.vecMulVec removedSecond removedSecond = atomMatrix removedSecond
        from rfl]
    abel
  rw [hfinal]
  exact hstepTwo


/-! ## The Bhatia-Davis selection and the two-valued decomposition -/

/-- **THE SELECTION LEMMA.**  A positively weighted mean-zero family on four
indices with weighted mean square `varianceVal >= 1` either exposes an extreme
pair satisfying the spike criterion `1 + varianceVal + 2 xi_k xi_l < 0`, or
`varianceVal <= 1` and the family is TWO-VALUED -- every entry sits at the
minimum or at the maximum.  The first branch is non-strict Bhatia-Davis when
the variance is strict and strict Bhatia-Davis when an interior point exists;
the second branch is all that survives of the equality case. -/
theorem exists_criterionPair_or_twoValued (weightVal xiVal : Fin 4 → ℝ)
    (varianceVal : ℝ) (hweightPos : ∀ idx, 0 < weightVal idx)
    (hweightSum : ∑ idx, weightVal idx = 1)
    (hmeanZero : ∑ idx, weightVal idx * xiVal idx = 0)
    (hvariance : ∑ idx, weightVal idx * xiVal idx ^ 2 = varianceVal)
    (hvarianceGe : 1 ≤ varianceVal) :
    (∃ highIdx lowIdx : Fin 4, highIdx ≠ lowIdx
        ∧ 1 + varianceVal + 2 * (xiVal highIdx * xiVal lowIdx) < 0)
      ∨ (varianceVal ≤ 1 ∧ ∃ lowValue highValue : ℝ, lowValue ≠ highValue
          ∧ ∀ idx, xiVal idx = lowValue ∨ xiVal idx = highValue) := by
  classical
  obtain ⟨highIdx, hhigh⟩ := Finite.exists_max xiVal
  obtain ⟨lowIdx, hlow⟩ := Finite.exists_min xiVal
  have hvaluesLt : xiVal lowIdx < xiVal highIdx := by
    rcases lt_or_eq_of_le (hlow highIdx) with hstrict | hflat
    · exact hstrict
    · exfalso
      have hallEqual : ∀ idx, xiVal idx = xiVal lowIdx :=
        fun idx => le_antisymm (by rw [hflat]; exact hhigh idx) (hlow idx)
      have hmeanCollapse : xiVal lowIdx = 0 := by
        have hsum := hmeanZero
        rw [Finset.sum_congr rfl fun idx _ => by rw [hallEqual idx]] at hsum
        rw [← Finset.sum_mul, hweightSum, one_mul] at hsum
        exact hsum
      have hvarCollapse : varianceVal = 0 := by
        rw [← hvariance]
        exact Finset.sum_eq_zero fun idx _ => by
          rw [hallEqual idx, hmeanCollapse]
          ring
      linarith
  have hindexNe : highIdx ≠ lowIdx := fun hEq => by
    rw [hEq] at hvaluesLt
    exact lt_irrefl _ hvaluesLt
  have hbhatiaWeak : varianceVal ≤ -(xiVal lowIdx * xiVal highIdx) := by
    have hbound := weighted_sq_le_neg_mul_of_mean_zero weightVal xiVal lowIdx highIdx
      (fun idx => le_of_lt (hweightPos idx)) hmeanZero hlow hhigh
    rw [hweightSum, mul_one, hvariance] at hbound
    exact hbound
  rcases lt_or_ge 1 varianceVal with hvarStrict | hvarWeak
  · exact Or.inl ⟨highIdx, lowIdx, hindexNe, by nlinarith [hbhatiaWeak]⟩
  · by_cases hinterior : ∃ insideIdx, xiVal lowIdx < xiVal insideIdx
        ∧ xiVal insideIdx < xiVal highIdx
    · obtain ⟨insideIdx, hinsideLow, hinsideHigh⟩ := hinterior
      have hbhatiaStrict := weighted_sq_lt_neg_mul_of_mean_zero_of_strict_between
        weightVal xiVal lowIdx highIdx insideIdx
        (fun idx => le_of_lt (hweightPos idx)) hmeanZero hlow hhigh
        (hweightPos insideIdx) hinsideLow hinsideHigh
      rw [hweightSum, mul_one, hvariance] at hbhatiaStrict
      exact Or.inl ⟨highIdx, lowIdx, hindexNe, by nlinarith [hbhatiaStrict]⟩
    · push Not at hinterior
      refine Or.inr ⟨hvarWeak, xiVal lowIdx, xiVal highIdx, ne_of_lt hvaluesLt,
        fun idx => ?_⟩
      rcases lt_or_eq_of_le (hlow idx) with hstrictLow | hflatLow
      · exact Or.inr (le_antisymm (hhigh idx) (hinterior idx hstrictLow))
      · exact Or.inl hflatLow.symm

/-- **THE TWO-VALUED DECOMPOSITION.**  A spike reconstructed through a
two-valued profile against a dependent atom family collapses, modulo the
dependency, to a scalar multiple of ONE atom or to a two-term combination that
can always be normalised to pass through slot `0`.  The sixteen sign patterns
reduce to exactly these shapes. -/
theorem spike_decomposition_of_twoValued {rank : ℕ}
    (atomFamily : Fin 4 → Fin rank → ℝ) (alphaDep xiVal : Fin 4 → ℝ)
    (spikeVec : Fin rank → ℝ) (lowValue highValue : ℝ)
    (hspike : spikeVec = ∑ idx, (xiVal idx * alphaDep idx) • atomFamily idx)
    (hdependency : ∑ idx, alphaDep idx • atomFamily idx = 0)
    (htwoValued : ∀ idx, xiVal idx = lowValue ∨ xiVal idx = highValue)
    (hvaluesNe : lowValue ≠ highValue) (halphaNe : ∀ idx, alphaDep idx ≠ 0) :
    (∃ (slot : Fin 4) (ratio : ℝ), spikeVec = ratio • atomFamily slot)
      ∨ (∃ pairedSlot : Fin 4, pairedSlot ≠ 0 ∧ ∃ scaleZero scalePaired : ℝ,
          scaleZero ≠ 0 ∧ scalePaired ≠ 0
          ∧ spikeVec = scaleZero • atomFamily 0 + scalePaired • atomFamily pairedSlot) := by
  classical
  have hgapNe : highValue - lowValue ≠ 0 := sub_ne_zero_of_ne (Ne.symm hvaluesNe)
  have hgapNe' : lowValue - highValue ≠ 0 := sub_ne_zero_of_ne hvaluesNe
  have hspikeCoord : ∀ coordIdx, spikeVec coordIdx
      = xiVal 0 * alphaDep 0 * atomFamily 0 coordIdx
        + xiVal 1 * alphaDep 1 * atomFamily 1 coordIdx
        + xiVal 2 * alphaDep 2 * atomFamily 2 coordIdx
        + xiVal 3 * alphaDep 3 * atomFamily 3 coordIdx := by
    intro coordIdx
    have hrow := congrFun hspike coordIdx
    rw [hrow]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  have hdepCoord : ∀ coordIdx, alphaDep 0 * atomFamily 0 coordIdx
      + alphaDep 1 * atomFamily 1 coordIdx + alphaDep 2 * atomFamily 2 coordIdx
      + alphaDep 3 * atomFamily 3 coordIdx = 0 := by
    intro coordIdx
    have hrow := congrFun hdependency coordIdx
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four,
      Pi.zero_apply] at hrow
    exact hrow
  rcases htwoValued 0 with hzeroLow | hzeroHigh <;>
    rcases htwoValued 1 with honeLow | honeHigh <;>
    rcases htwoValued 2 with htwoLow | htwoHigh <;>
    rcases htwoValued 3 with hthreeLow | hthreeHigh
  -- pattern (L, L, L, L): the spike is the zero vector
  · refine Or.inl ⟨0, 0, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeLow, htwoLow, hthreeLow] at hval
    simp only [Pi.smul_apply, smul_eq_mul, zero_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (L, L, L, H): singleton high at slot 3
  · refine Or.inl ⟨3, (highValue - lowValue) * alphaDep 3, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeLow, htwoLow, hthreeHigh] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (L, L, H, L): singleton high at slot 2
  · refine Or.inl ⟨2, (highValue - lowValue) * alphaDep 2, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeLow, htwoHigh, hthreeLow] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (L, L, H, H): complement pair {0, 1}
  · refine Or.inr ⟨1, by decide, (lowValue - highValue) * alphaDep 0,
      (lowValue - highValue) * alphaDep 1, mul_ne_zero hgapNe' (halphaNe 0),
      mul_ne_zero hgapNe' (halphaNe 1), funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeLow, htwoHigh, hthreeHigh] at hval
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hval + highValue * hdepCoord coordIdx
  -- pattern (L, H, L, L): singleton high at slot 1
  · refine Or.inl ⟨1, (highValue - lowValue) * alphaDep 1, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeHigh, htwoLow, hthreeLow] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (L, H, L, H): complement pair {0, 2}
  · refine Or.inr ⟨2, by decide, (lowValue - highValue) * alphaDep 0,
      (lowValue - highValue) * alphaDep 2, mul_ne_zero hgapNe' (halphaNe 0),
      mul_ne_zero hgapNe' (halphaNe 2), funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeHigh, htwoLow, hthreeHigh] at hval
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hval + highValue * hdepCoord coordIdx
  -- pattern (L, H, H, L): complement pair {0, 3}
  · refine Or.inr ⟨3, by decide, (lowValue - highValue) * alphaDep 0,
      (lowValue - highValue) * alphaDep 3, mul_ne_zero hgapNe' (halphaNe 0),
      mul_ne_zero hgapNe' (halphaNe 3), funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeHigh, htwoHigh, hthreeLow] at hval
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hval + highValue * hdepCoord coordIdx
  -- pattern (L, H, H, H): complement singleton at slot 0
  · refine Or.inl ⟨0, (lowValue - highValue) * alphaDep 0, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroLow, honeHigh, htwoHigh, hthreeHigh] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + highValue * hdepCoord coordIdx
  -- pattern (H, L, L, L): singleton high at slot 0
  · refine Or.inl ⟨0, (highValue - lowValue) * alphaDep 0, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeLow, htwoLow, hthreeLow] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (H, L, L, H): direct pair {0, 3}
  · refine Or.inr ⟨3, by decide, (highValue - lowValue) * alphaDep 0,
      (highValue - lowValue) * alphaDep 3, mul_ne_zero hgapNe (halphaNe 0),
      mul_ne_zero hgapNe (halphaNe 3), funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeLow, htwoLow, hthreeHigh] at hval
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (H, L, H, L): direct pair {0, 2}
  · refine Or.inr ⟨2, by decide, (highValue - lowValue) * alphaDep 0,
      (highValue - lowValue) * alphaDep 2, mul_ne_zero hgapNe (halphaNe 0),
      mul_ne_zero hgapNe (halphaNe 2), funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeLow, htwoHigh, hthreeLow] at hval
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (H, L, H, H): complement singleton at slot 1
  · refine Or.inl ⟨1, (lowValue - highValue) * alphaDep 1, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeLow, htwoHigh, hthreeHigh] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + highValue * hdepCoord coordIdx
  -- pattern (H, H, L, L): direct pair {0, 1}
  · refine Or.inr ⟨1, by decide, (highValue - lowValue) * alphaDep 0,
      (highValue - lowValue) * alphaDep 1, mul_ne_zero hgapNe (halphaNe 0),
      mul_ne_zero hgapNe (halphaNe 1), funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeHigh, htwoLow, hthreeLow] at hval
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hval + lowValue * hdepCoord coordIdx
  -- pattern (H, H, L, H): complement singleton at slot 2
  · refine Or.inl ⟨2, (lowValue - highValue) * alphaDep 2, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeHigh, htwoLow, hthreeHigh] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + highValue * hdepCoord coordIdx
  -- pattern (H, H, H, L): complement singleton at slot 3
  · refine Or.inl ⟨3, (lowValue - highValue) * alphaDep 3, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeHigh, htwoHigh, hthreeLow] at hval
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination hval + highValue * hdepCoord coordIdx
  -- pattern (H, H, H, H): the spike is the zero vector
  · refine Or.inl ⟨0, 0, funext fun coordIdx => ?_⟩
    have hval := hspikeCoord coordIdx
    rw [hzeroHigh, honeHigh, htwoHigh, hthreeHigh] at hval
    simp only [Pi.smul_apply, smul_eq_mul, zero_mul]
    linear_combination hval + highValue * hdepCoord coordIdx


/-! ## The geometric impossibility of a doubly paired spike pair

If BOTH weightless spikes of the two-vanished stratum decompose through the
survivor and one negative atom, the diagonal gauge collapses: equal negative
slots force a negative atom onto the survivor axis (killed by primitivity),
and distinct slots force a vanishing survivor coordinate (killed by the
full-support dependency).  This is the exact mechanism that makes the
Bhatia-Davis slack strictly positive on the degenerate slice. -/

theorem no_doubly_paired_spikes
    {axisFirst axisSecond axisSurvivor : Fin 3}
    (hsumThree : ∀ valueOf : Fin 3 → ℝ,
      ∑ coordIdx, valueOf coordIdx
        = valueOf axisFirst + valueOf axisSecond + valueOf axisSurvivor)
    {survivorAtom : Fin 3 → ℝ}
    (hsurvivorAtFirst : survivorAtom axisFirst = 0)
    (hsurvivorAtSecond : survivorAtom axisSecond = 0)
    (hsurvivorAtAxis : survivorAtom axisSurvivor ≠ 0)
    {negAtom : Fin 3 → Fin 3 → ℝ}
    (hnegOrthogonal : ∀ leftIdx rightIdx, leftIdx ≠ rightIdx →
      negAtom leftIdx ⬝ᵥ negAtom rightIdx = 0)
    (hnegSurvivorCoord : ∀ negIdx, negAtom negIdx axisSurvivor ≠ 0)
    {firstSpike secondSpike : Fin 3 → ℝ}
    (hfirstSpikeAtSecond : firstSpike axisSecond = 0)
    (hfirstSpikeAtAxis : firstSpike axisSurvivor = 0)
    (hsecondSpikeAtFirst : secondSpike axisFirst = 0)
    (hnotParallel : ∀ (negIdx : Fin 3) (ratio : ℝ), negAtom negIdx ≠ ratio • survivorAtom)
    {pairedFirst pairedSecond : Fin 3} {scaleFZ scaleFN scaleGZ scaleGN : ℝ}
    (hscaleFZ : scaleFZ ≠ 0) (hscaleFN : scaleFN ≠ 0) (hscaleGN : scaleGN ≠ 0)
    (hfirstEq : firstSpike = scaleFZ • survivorAtom + scaleFN • negAtom pairedFirst)
    (hsecondEq : secondSpike = scaleGZ • survivorAtom + scaleGN • negAtom pairedSecond)
    (hcoverCoord : ∀ coordIdx : Fin 3,
      coordIdx = axisFirst ∨ coordIdx = axisSecond ∨ coordIdx = axisSurvivor) :
    False := by
  classical
  -- the first paired negative loses its second-axis coordinate
  have hpairedFirstAtSecond : negAtom pairedFirst axisSecond = 0 := by
    have hcoord := congrFun hfirstEq axisSecond
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfirstSpikeAtSecond,
      hsurvivorAtSecond, mul_zero, zero_add] at hcoord
    rcases mul_eq_zero.mp hcoord.symm with hcontra | hzero
    · exact absurd hcontra hscaleFN
    · exact hzero
  -- the second paired negative loses its first-axis coordinate
  have hpairedSecondAtFirst : negAtom pairedSecond axisFirst = 0 := by
    have hcoord := congrFun hsecondEq axisFirst
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsecondSpikeAtFirst,
      hsurvivorAtFirst, mul_zero, zero_add] at hcoord
    rcases mul_eq_zero.mp hcoord.symm with hcontra | hzero
    · exact absurd hcontra hscaleGN
    · exact hzero
  by_cases hsameSlot : pairedFirst = pairedSecond
  · -- equal slots: the negative atom lives on the survivor axis
    have hpairedFirstAtFirst : negAtom pairedFirst axisFirst = 0 := by
      rw [hsameSlot]
      exact hpairedSecondAtFirst
    refine hnotParallel pairedFirst
      (negAtom pairedFirst axisSurvivor / survivorAtom axisSurvivor)
      (funext fun coordIdx => ?_)
    rcases hcoverCoord coordIdx with hisFirst | hisSecond | hisSurvivor
    · rw [hisFirst, hpairedFirstAtFirst]
      simp only [Pi.smul_apply, smul_eq_mul, hsurvivorAtFirst, mul_zero]
    · rw [hisSecond, hpairedFirstAtSecond]
      simp only [Pi.smul_apply, smul_eq_mul, hsurvivorAtSecond, mul_zero]
    · rw [hisSurvivor]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hsurvivorAtAxis]
  · -- distinct slots: pair the first spike against the second paired negative
    have hdotVanishes : firstSpike ⬝ᵥ negAtom pairedSecond = 0 := by
      simp only [dotProduct]
      rw [hsumThree fun coordIdx => firstSpike coordIdx * negAtom pairedSecond coordIdx,
        hfirstSpikeAtSecond, hfirstSpikeAtAxis, hpairedSecondAtFirst]
      ring
    have hdotExpands : firstSpike ⬝ᵥ negAtom pairedSecond
        = scaleFZ * (survivorAtom axisSurvivor * negAtom pairedSecond axisSurvivor) := by
      rw [hfirstEq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
        smul_eq_mul, hnegOrthogonal pairedFirst pairedSecond hsameSlot, mul_zero,
        add_zero]
      congr 1
      simp only [dotProduct]
      rw [hsumThree fun coordIdx => survivorAtom coordIdx * negAtom pairedSecond coordIdx,
        hsurvivorAtFirst, hsurvivorAtSecond]
      ring
    rw [hdotVanishes] at hdotExpands
    rcases mul_eq_zero.mp hdotExpands.symm with hcontra | hproduct
    · exact absurd hcontra hscaleFZ
    · rcases mul_eq_zero.mp hproduct with hcontra | hzero
      · exact absurd hcontra hsurvivorAtAxis
      · exact absurd hzero (hnegSurvivorCoord pairedSecond)


/-! ## The spike-lane engine

One weightless spike against a total-tie bottom: either an exchange triple is
strictly positive definite, or the spike pivot is at most one and the spike
decomposes through the survivor slot.  All tie-frame inputs arrive as
hypotheses, so the engine runs unchanged for both spikes. -/

theorem spike_lane_engine {rank : ℕ}
    (window : Matrix (Fin rank) (Fin rank) ℝ) (hwindow : window.PosDef)
    (atomFamily : Fin 4 → Fin rank → ℝ) (weightVal coweightVal alphaDep : Fin 4 → ℝ)
    (hweightPos : ∀ idx, 0 < weightVal idx)
    (hweightSum : ∑ idx, weightVal idx = 1)
    (hwindowDef : window = ∑ idx, coweightVal idx • atomMatrix (atomFamily idx))
    (halphaVec : ∑ idx, alphaDep idx • atomFamily idx = 0)
    (halphaSq : ∀ idx, alphaDep idx ^ 2 = coweightVal idx * weightVal idx)
    (halphaNe : ∀ idx, alphaDep idx ≠ 0)
    (hunitPivot : ∀ idx, atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ atomFamily idx) = 1)
    (hpairing : ∀ leftIdx rightIdx, leftIdx ≠ rightIdx →
      coweightVal leftIdx * coweightVal rightIdx
          * (atomFamily leftIdx ⬝ᵥ (window⁻¹ *ᵥ atomFamily rightIdx))
        = -(alphaDep leftIdx * alphaDep rightIdx))
    (spikeVec : Fin rank → ℝ)
    (hspikePivot : 1 ≤ spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) :
    (∃ highIdx lowIdx : Fin 4, highIdx ≠ lowIdx
        ∧ (window - atomMatrix (atomFamily highIdx) - atomMatrix (atomFamily lowIdx)
            + atomMatrix spikeVec).PosDef)
      ∨ (spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec) ≤ 1
          ∧ ((∃ (slot : Fin 4) (ratio : ℝ), spikeVec = ratio • atomFamily slot)
            ∨ (∃ pairedSlot : Fin 4, pairedSlot ≠ 0 ∧ ∃ scaleZero scalePaired : ℝ,
                scaleZero ≠ 0 ∧ scalePaired ≠ 0
                ∧ spikeVec = scaleZero • atomFamily 0
                    + scalePaired • atomFamily pairedSlot))) := by
  classical
  have hcoweightPos : ∀ idx, 0 < coweightVal idx := by
    intro idx
    have hsqPos : 0 < alphaDep idx ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (halphaNe idx)))
    rw [halphaSq idx] at hsqPos
    rcases mul_pos_iff.mp hsqPos with ⟨hcw, _⟩ | ⟨_, hwneg⟩
    · exact hcw
    · exact absurd (hweightPos idx) (not_lt_of_gt hwneg)
  have hdetWindow : IsUnit window.det := isUnit_iff_ne_zero.mpr (ne_of_gt hwindow.det_pos)
  have hwindowInvAction : ∀ probeVector : Fin rank → ℝ,
      window *ᵥ (window⁻¹ *ᵥ probeVector) = probeVector := fun probeVector => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetWindow, Matrix.one_mulVec]
  have hwindowAction : ∀ probeVector : Fin rank → ℝ, window *ᵥ probeVector
      = ∑ idx, (coweightVal idx * (atomFamily idx ⬝ᵥ probeVector)) • atomFamily idx := by
    intro probeVector
    conv_lhs => rw [hwindowDef]
    rw [Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun idx _ => by
      rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_dotProduct_smul, smul_smul]
  -- reconstruction of the spike through the window resolution
  have hrecon : spikeVec = ∑ idx,
      (coweightVal idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))) • atomFamily idx := by
    conv_lhs => rw [← hwindowInvAction spikeVec]
    rw [hwindowAction]
  -- the pivot as the coweighted square sum
  have hpivotSum : ∑ idx, coweightVal idx
        * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
        * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
      = spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec) := by
    have hbilinear := dotProduct_weightedAtomSum_mulVec coweightVal atomFamily
      (window⁻¹ *ᵥ spikeVec) (window⁻¹ *ᵥ spikeVec)
    rw [← hwindowDef, hwindowInvAction, dotProduct_comm] at hbilinear
    exact hbilinear.symm
  -- the whitened profile
  set xiVal : Fin 4 → ℝ := fun idx =>
    (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) * coweightVal idx / alphaDep idx
    with hxiDef
  have hxiAlpha : ∀ idx, xiVal idx * alphaDep idx
      = coweightVal idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) := by
    intro idx
    simp only [hxiDef]
    rw [div_mul_cancel₀ _ (halphaNe idx)]
    ring
  -- the mean-zero law
  have hmeanTerms : ∀ idx, weightVal idx * xiVal idx
      = alphaDep idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) := by
    intro idx
    have hmulled : weightVal idx * xiVal idx * alphaDep idx
        = alphaDep idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) * alphaDep idx := by
      calc weightVal idx * xiVal idx * alphaDep idx
          = weightVal idx * (xiVal idx * alphaDep idx) := by ring
        _ = weightVal idx * (coweightVal idx
              * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))) := by rw [hxiAlpha idx]
        _ = (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
              * (coweightVal idx * weightVal idx) := by ring
        _ = (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) * alphaDep idx ^ 2 := by
              rw [← halphaSq idx]
        _ = alphaDep idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
              * alphaDep idx := by ring
    exact mul_right_cancel₀ (halphaNe idx) hmulled
  have hmean : ∑ idx, weightVal idx * xiVal idx = 0 := by
    have hzeroDot : (∑ idx, alphaDep idx • atomFamily idx)
        ⬝ᵥ (window⁻¹ *ᵥ spikeVec) = 0 := by
      rw [halphaVec, zero_dotProduct]
    rw [sum_smul_dotProduct] at hzeroDot
    rw [Finset.sum_congr rfl fun idx _ => hmeanTerms idx]
    exact hzeroDot
  -- the variance law
  have hvarTerms : ∀ idx, weightVal idx * xiVal idx ^ 2
      = coweightVal idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
        * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) := by
    intro idx
    have hmulled : weightVal idx * xiVal idx ^ 2 * alphaDep idx ^ 2
        = coweightVal idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
          * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) * alphaDep idx ^ 2 := by
      calc weightVal idx * xiVal idx ^ 2 * alphaDep idx ^ 2
          = weightVal idx * (xiVal idx * alphaDep idx) ^ 2 := by ring
        _ = weightVal idx * (coweightVal idx
              * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))) ^ 2 := by rw [hxiAlpha idx]
        _ = coweightVal idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
              * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
              * (coweightVal idx * weightVal idx) := by ring
        _ = coweightVal idx * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
              * (atomFamily idx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) * alphaDep idx ^ 2 := by
              rw [← halphaSq idx]
    exact mul_right_cancel₀ (pow_ne_zero 2 (halphaNe idx)) hmulled
  have hvariance : ∑ idx, weightVal idx * xiVal idx ^ 2
      = spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec) := by
    rw [Finset.sum_congr rfl fun idx _ => hvarTerms idx]
    exact hpivotSum
  -- the selection dichotomy
  rcases exists_criterionPair_or_twoValued weightVal xiVal
      (spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) hweightPos hweightSum hmean hvariance
      hspikePivot with
    ⟨highIdx, lowIdx, hindexNe, hbracketNeg⟩
      | ⟨hpivotLe, lowValue, highValue, hvaluesNe, htwoValued⟩
  · -- the exchange lane
    left
    refine ⟨highIdx, lowIdx, hindexNe, ?_⟩
    have hCval : atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ atomFamily lowIdx)
        = -(alphaDep highIdx * alphaDep lowIdx)
          / (coweightVal highIdx * coweightVal lowIdx) := by
      rw [eq_div_iff (ne_of_gt (mul_pos (hcoweightPos highIdx) (hcoweightPos lowIdx)))]
      linear_combination hpairing highIdx lowIdx hindexNe
    have hmkval : atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)
        = xiVal highIdx * alphaDep highIdx / coweightVal highIdx := by
      rw [hxiAlpha highIdx, mul_div_cancel_left₀ _ (ne_of_gt (hcoweightPos highIdx))]
    have hmlval : atomFamily lowIdx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)
        = xiVal lowIdx * alphaDep lowIdx / coweightVal lowIdx := by
      rw [hxiAlpha lowIdx, mul_div_cancel_left₀ _ (ne_of_gt (hcoweightPos lowIdx))]
    have halphaProdSqPos : 0 < (alphaDep highIdx * alphaDep lowIdx) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2
        (mul_ne_zero (halphaNe highIdx) (halphaNe lowIdx))))
    have hdiffEq : (atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ atomFamily lowIdx)) ^ 2
          * (1 + spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
        - 2 * (atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ atomFamily lowIdx))
          * (atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
          * (atomFamily lowIdx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
        = (alphaDep highIdx * alphaDep lowIdx) ^ 2
            * (1 + spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec)
                + 2 * (xiVal highIdx * xiVal lowIdx))
          / (coweightVal highIdx * coweightVal lowIdx) ^ 2 := by
      rw [hCval, hmkval, hmlval]
      field_simp
      ring
    have hrhsNeg : (alphaDep highIdx * alphaDep lowIdx) ^ 2
          * (1 + spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec)
              + 2 * (xiVal highIdx * xiVal lowIdx))
        / (coweightVal highIdx * coweightVal lowIdx) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg halphaProdSqPos hbracketNeg)
        (pow_pos (mul_pos (hcoweightPos highIdx) (hcoweightPos lowIdx)) 2)
    have hcriterionFinal : (atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ atomFamily lowIdx)) ^ 2
          * (1 + spikeVec ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
        < 2 * (atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ atomFamily lowIdx))
          * (atomFamily highIdx ⬝ᵥ (window⁻¹ *ᵥ spikeVec))
          * (atomFamily lowIdx ⬝ᵥ (window⁻¹ *ᵥ spikeVec)) := by
      nlinarith [hdiffEq, hrhsNeg]
    exact twoRankOne_exchange_posDef window hwindow (atomFamily highIdx)
      (atomFamily lowIdx) spikeVec (hunitPivot highIdx) (hunitPivot lowIdx)
      (by linarith) hcriterionFinal
  · -- the two-valued lane
    right
    refine ⟨hpivotLe, ?_⟩
    have hspikeXi : spikeVec = ∑ idx, (xiVal idx * alphaDep idx) • atomFamily idx := by
      rw [hrecon]
      exact Finset.sum_congr rfl fun idx _ => by rw [hxiAlpha idx]
    exact spike_decomposition_of_twoValued atomFamily alphaDep xiVal spikeVec
      lowValue highValue hspikeXi halphaVec htwoValued hvaluesNe halphaNe


/-! ## The residual and its proof

The residual `TwoVanishedRigidBottomDominationSixThree` is the one defined in
`Gtz.Reduction.EndpointGaugeDescent`, so the theorem
`twoVanishedRigidBottomDomination_holds` plugs directly into
`forall_gtzOriginal_rank_three_of_tieExclusion_twoVanished_stressFreeHinge`
without any bridging. -/

/-- The coordinate axis direction, as a vector. -/
def axisVector {rank : ℕ} (axisIdx : Fin rank) : Fin rank → ℝ :=
  fun coordIdx => if coordIdx = axisIdx then 1 else 0

/-- Pairing against an axis reads off the coordinate. -/
theorem dotProduct_axisVector {rank : ℕ} (vec : Fin rank → ℝ) (axisIdx : Fin rank) :
    vec ⬝ᵥ axisVector axisIdx = vec axisIdx := by
  simp only [dotProduct, axisVector, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ axisIdx vec]
  simp

/-- **THE TWO-VANISHED RESIDUAL HOLDS.**  The coweighted window is positive
definite because the negative side resolves the identity; the conservation law
either hands a strictly dominating bottom triple or pins a TOTAL TIE; at a
total tie the corank-one frame identifies the dependency squares and pairings,
the master identity gives the two spike defects opposite signs, `le_total`
picks the spike, Bhatia-Davis picks the exchanged pair, and the two-for-one
exchange concludes.  On the degenerate slice where both spike pivots are
exactly one, a failed selection forces both spikes to decompose through the
survivor slot, and the diagonal-gauge geometry refutes that outright. -/
theorem twoVanishedRigidBottomDomination_holds :
    TwoVanishedRigidBottomDominationSixThree := by
  intro baseAtom weight stressCoeff posEnum negEnum firstVanishedIdx secondVanishedIdx
    hvanNe hweightNonneg hweightSumOne hweightNegSide hfirstZero hsecondZero hothersPos
    hfull hposInjective hposSign hposOnto hnegInjective hnegSign hnegOnto hdiagonal
    hposSide hnegSide hzeroSum hprimitive _hrigid
  classical
  -- the third positive index and the label scaffold
  obtain ⟨survivorIdx, hsurvNeFirst, hsurvNeSecond, hcoverFin3⟩ :=
    exists_thirdIndex_fin3 firstVanishedIdx secondVanishedIdx hvanNe
  have hposNegNe : ∀ posIdx negIdx, posEnum posIdx ≠ negEnum negIdx := by
    intro posIdx negIdx hEq
    have hposVal := hposSign posIdx
    rw [hEq] at hposVal
    exact absurd (hposVal.trans (hnegSign negIdx)) (lt_irrefl 0)
  set survivorLabel := posEnum survivorIdx with hsurvivorLabelDef
  set bottomLabel : Fin 4 → Fin 6 := Fin.cons survivorLabel negEnum with hbottomLabelDef
  set bAtom : Fin 4 → Fin 3 → ℝ := fun slotIdx => baseAtom (bottomLabel slotIdx)
    with hbAtomDef
  set bWeight : Fin 4 → ℝ := fun slotIdx => weight (bottomLabel slotIdx) with hbWeightDef
  set coweightFour : Fin 4 → ℝ := fun slotIdx => 1 - bWeight slotIdx with hcoweightFourDef
  have hbAtomZero : bAtom 0 = baseAtom survivorLabel := by
    simp only [hbAtomDef, hbottomLabelDef, Fin.cons_zero]
  have hbAtomSucc : ∀ negIdx : Fin 3,
      bAtom (Fin.succ negIdx) = baseAtom (negEnum negIdx) := by
    intro negIdx
    simp only [hbAtomDef, hbottomLabelDef, Fin.cons_succ]
  have hbWeightZero : bWeight 0 = weight survivorLabel := by
    simp only [hbWeightDef, hbottomLabelDef, Fin.cons_zero]
  have hbWeightSucc : ∀ negIdx : Fin 3,
      bWeight (Fin.succ negIdx) = weight (negEnum negIdx) := by
    intro negIdx
    simp only [hbWeightDef, hbottomLabelDef, Fin.cons_succ]
  have hbottomInjective : Function.Injective bottomLabel := by
    intro leftIdx rightIdx hEq
    rcases Fin.eq_zero_or_eq_succ leftIdx with hleftZero | ⟨leftNeg, hleftSucc⟩ <;>
      rcases Fin.eq_zero_or_eq_succ rightIdx with hrightZero | ⟨rightNeg, hrightSucc⟩
    · rw [hleftZero, hrightZero]
    · exfalso
      rw [hleftZero, hrightSucc] at hEq
      simp only [hbottomLabelDef, Fin.cons_zero, Fin.cons_succ, hsurvivorLabelDef] at hEq
      exact hposNegNe survivorIdx rightNeg hEq
    · exfalso
      rw [hleftSucc, hrightZero] at hEq
      simp only [hbottomLabelDef, Fin.cons_zero, Fin.cons_succ, hsurvivorLabelDef] at hEq
      exact hposNegNe survivorIdx leftNeg hEq.symm
    · rw [hleftSucc, hrightSucc] at hEq ⊢
      simp only [hbottomLabelDef, Fin.cons_succ] at hEq
      rw [hnegInjective hEq]
  have hbottomNeFirstSpike : ∀ slotIdx : Fin 4,
      bottomLabel slotIdx ≠ posEnum firstVanishedIdx := by
    intro slotIdx
    rcases Fin.eq_zero_or_eq_succ slotIdx with hzero | ⟨negIdx, hsucc⟩
    · rw [hzero]
      simp only [hbottomLabelDef, Fin.cons_zero, hsurvivorLabelDef]
      exact fun hEq => hsurvNeFirst (hposInjective hEq)
    · rw [hsucc]
      simp only [hbottomLabelDef, Fin.cons_succ]
      exact (hposNegNe firstVanishedIdx negIdx).symm
  have hbottomNeSecondSpike : ∀ slotIdx : Fin 4,
      bottomLabel slotIdx ≠ posEnum secondVanishedIdx := by
    intro slotIdx
    rcases Fin.eq_zero_or_eq_succ slotIdx with hzero | ⟨negIdx, hsucc⟩
    · rw [hzero]
      simp only [hbottomLabelDef, Fin.cons_zero, hsurvivorLabelDef]
      exact fun hEq => hsurvNeSecond (hposInjective hEq)
    · rw [hsucc]
      simp only [hbottomLabelDef, Fin.cons_succ]
      exact (hposNegNe secondVanishedIdx negIdx).symm
  -- the weights of the bottom
  have hbWeightPos : ∀ slotIdx : Fin 4, 0 < bWeight slotIdx := by
    intro slotIdx
    rcases Fin.eq_zero_or_eq_succ slotIdx with hzero | ⟨negIdx, hsucc⟩
    · rw [hzero, hbWeightZero, hsurvivorLabelDef]
      exact hothersPos survivorIdx hsurvNeFirst hsurvNeSecond
    · rw [hsucc, hbWeightSucc]
      exact hweightNegSide _ (hnegSign negIdx)
  have hsplitSix : ∀ {carrier : Type} [AddCommMonoid carrier] (summand : Fin 6 → carrier),
      ∑ label, summand label
        = ∑ posIdx, summand (posEnum posIdx) + ∑ negIdx, summand (negEnum negIdx) :=
    fun summand => sum_fin6_eq_posSum_add_negSum hfull hposInjective hposSign hposOnto
      hnegInjective hnegSign hnegOnto summand
  have hsplitThree : ∀ {carrier : Type} [AddCommMonoid carrier] (summand : Fin 3 → carrier),
      ∑ posIdx, summand posIdx
        = summand firstVanishedIdx + summand secondVanishedIdx + summand survivorIdx :=
    fun summand => sum_eq_add_add_of_coverFin3 hvanNe (Ne.symm hsurvNeFirst)
      (Ne.symm hsurvNeSecond) hcoverFin3 summand
  have hbWeightSum : ∑ slotIdx, bWeight slotIdx = 1 := by
    have hsix := hsplitSix (carrier := ℝ) weight
    rw [hsplitThree (carrier := ℝ) (fun posIdx => weight (posEnum posIdx)), hfirstZero,
      hsecondZero, hweightSumOne, ← hsurvivorLabelDef] at hsix
    rw [Fin.sum_univ_succ, hbWeightZero,
      Finset.sum_congr rfl fun negIdx _ => hbWeightSucc negIdx]
    linarith [hsix]
  have hbWeightLt : ∀ slotIdx : Fin 4, bWeight slotIdx < 1 := by
    intro slotIdx
    have hother : ∀ anyIdx : Fin 4, ∃ otherIdx : Fin 4, otherIdx ≠ anyIdx := by decide
    obtain ⟨otherIdx, hotherNe⟩ := hother slotIdx
    have hsplitWeight := Finset.add_sum_erase Finset.univ bWeight (Finset.mem_univ slotIdx)
    have herasePos : 0 < ∑ otherSlot ∈ Finset.univ.erase slotIdx, bWeight otherSlot :=
      Finset.sum_pos (fun otherSlot _ => hbWeightPos otherSlot)
        ⟨otherIdx, Finset.mem_erase.mpr ⟨hotherNe, Finset.mem_univ otherIdx⟩⟩
    rw [hbWeightSum] at hsplitWeight
    linarith
  have hcoweightPosFour : ∀ slotIdx : Fin 4, 0 < coweightFour slotIdx := by
    intro slotIdx
    simp only [hcoweightFourDef]
    linarith [hbWeightLt slotIdx]
  -- the Gram and the window
  set gram := ∑ label, weight label • atomMatrix (baseAtom label) with hgramDef
  have hgramBottom : gram = ∑ slotIdx, bWeight slotIdx • atomMatrix (bAtom slotIdx) := by
    have hrhs : ∑ slotIdx, bWeight slotIdx • atomMatrix (bAtom slotIdx)
        = weight survivorLabel • atomMatrix (baseAtom survivorLabel)
          + ∑ negIdx, weight (negEnum negIdx) • atomMatrix (baseAtom (negEnum negIdx)) := by
      rw [Fin.sum_univ_succ, hbWeightZero, hbAtomZero]
      congr 1
    rw [hgramDef, hsplitSix (carrier := Matrix (Fin 3) (Fin 3) ℝ)
        (fun label => weight label • atomMatrix (baseAtom label)),
      hsplitThree (carrier := Matrix (Fin 3) (Fin 3) ℝ)
        (fun posIdx => weight (posEnum posIdx) • atomMatrix (baseAtom (posEnum posIdx))),
      hfirstZero, hsecondZero, zero_smul, zero_smul, zero_add, zero_add,
      ← hsurvivorLabelDef, hrhs]
  set windowMat := ∑ slotIdx, coweightFour slotIdx • atomMatrix (bAtom slotIdx)
    with hwindowMatDef
  have hwindowAlt : windowMat = (∑ slotIdx, atomMatrix (bAtom slotIdx)) - gram := by
    rw [hwindowMatDef, hgramBottom, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun slotIdx _ => ?_
    simp only [hcoweightFourDef]
    rw [sub_smul, one_smul]
  -- the window is positive definite: the negative side resolves the identity
  have hprobeZero : ∀ probeVec : Fin 3 → ℝ,
      (∀ negIdx : Fin 3, baseAtom (negEnum negIdx) ⬝ᵥ probeVec = 0) → probeVec = 0 := by
    intro probeVec horth
    have hquad : probeVec ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probeVec)
        = ∑ negIdx, (-stressCoeff (negEnum negIdx))
            * (baseAtom (negEnum negIdx) ⬝ᵥ probeVec)
            * (baseAtom (negEnum negIdx) ⬝ᵥ probeVec) := by
      rw [← hnegSide]
      exact dotProduct_weightedAtomSum_mulVec _ _ probeVec probeVec
    rw [Matrix.one_mulVec] at hquad
    have hzero : probeVec ⬝ᵥ probeVec = 0 := by
      rw [hquad]
      exact Finset.sum_eq_zero fun negIdx _ => by rw [horth negIdx]; ring
    exact dotProduct_self_eq_zero.mp hzero
  have hwindowPosDef : windowMat.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq (by
        rw [hwindowMatDef]
        exact transpose_weightedAtomSum coweightFour bAtom), fun probeVec hprobe => ?_⟩
    rw [star_trivial, hwindowMatDef,
      dotProduct_weightedAtomSum_mulVec coweightFour bAtom probeVec probeVec]
    have hterms : ∀ slotIdx ∈ (Finset.univ : Finset (Fin 4)),
        0 ≤ coweightFour slotIdx * (bAtom slotIdx ⬝ᵥ probeVec)
          * (bAtom slotIdx ⬝ᵥ probeVec) := by
      intro slotIdx _
      rw [mul_assoc]
      exact mul_nonneg (le_of_lt (hcoweightPosFour slotIdx)) (mul_self_nonneg _)
    have hwitness : ∃ slotIdx ∈ (Finset.univ : Finset (Fin 4)),
        0 < coweightFour slotIdx * (bAtom slotIdx ⬝ᵥ probeVec)
          * (bAtom slotIdx ⬝ᵥ probeVec) := by
      by_contra hnone
      push Not at hnone
      refine hprobe (hprobeZero probeVec fun negIdx => ?_)
      have hle := hnone (Fin.succ negIdx) (Finset.mem_univ _)
      rw [hbAtomSucc negIdx, mul_assoc] at hle
      have hcwPos := hcoweightPosFour (Fin.succ negIdx)
      have hpairSq : (baseAtom (negEnum negIdx) ⬝ᵥ probeVec)
          * (baseAtom (negEnum negIdx) ⬝ᵥ probeVec) ≤ 0 := by
        nlinarith [hle, hcwPos]
      exact mul_self_eq_zero.mp (le_antisymm hpairSq (mul_self_nonneg _))
    exact Finset.sum_pos' hterms hwitness
  have hwindowDetUnit : IsUnit windowMat.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hwindowPosDef.det_pos)
  have hbaseForm : windowMat
      = ∑ slotIdx, (1 - bWeight slotIdx) • atomMatrix (bAtom slotIdx) := by
    rw [hwindowMatDef]
  rcases exists_pivot_lt_one_or_forall_pivot_eq_one bWeight bAtom windowMat hbaseForm
      hwindowDetUnit (by norm_num) hbWeightSum
      (fun slotIdx => by linarith [hbWeightLt slotIdx]) with
    ⟨lowSlot, hlowSlot⟩ | hallOne
  · -- CASE A: a bottom pivot below one, the complement bottom triple wins
    set selectedBottom := Finset.univ.image bottomLabel with hselectedBottomDef
    have hmemLow : bottomLabel lowSlot ∈ selectedBottom :=
      Finset.mem_image.mpr ⟨lowSlot, Finset.mem_univ lowSlot, rfl⟩
    have hcardBottom : selectedBottom.card = 4 := by
      rw [hselectedBottomDef, Finset.card_image_of_injective _ hbottomInjective,
        Finset.card_univ, Fintype.card_fin]
    refine ⟨selectedBottom.erase (bottomLabel lowSlot), ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hmemLow, hcardBottom]
    · have himage : ∑ label ∈ selectedBottom, atomMatrix (baseAtom label)
          = ∑ slotIdx, atomMatrix (bAtom slotIdx) := by
        rw [hselectedBottomDef, Finset.sum_image fun leftIdx _ rightIdx _ hEq =>
          hbottomInjective hEq]
      have hpeel := Finset.sum_erase_add selectedBottom
        (fun label => atomMatrix (baseAtom label)) hmemLow
      rw [himage] at hpeel
      have hlowConv : atomMatrix (baseAtom (bottomLabel lowSlot))
          = atomMatrix (bAtom lowSlot) := by simp only [hbAtomDef]
      rw [hlowConv] at hpeel
      have hgapEq : (∑ label ∈ selectedBottom.erase (bottomLabel lowSlot),
            atomMatrix (baseAtom label)) - gram
          = windowMat - atomMatrix (bAtom lowSlot) := by
        rw [eq_sub_of_add_eq hpeel, hwindowAlt]
        abel
      rw [hgapEq]
      have hpivotDict : bAtom lowSlot ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom lowSlot) < 1 := by
        rw [← pivotAgainst_eq_dotProduct]
        exact hlowSlot
      exact (posDef_sub_vecMulVec_iff windowMat hwindowPosDef (bAtom lowSlot)).mpr
        hpivotDict
  · -- CASE B: all bottom pivots equal one, the total tie
    have hunitPivot : ∀ slotIdx : Fin 4,
        bAtom slotIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom slotIdx) = 1 := by
      intro slotIdx
      rw [← pivotAgainst_eq_dotProduct]
      exact hallOne slotIdx
    have hwindowSymm : windowMatᵀ = windowMat := PosDef.transpose_eq hwindowPosDef
    have hinvSymm : (windowMat⁻¹)ᵀ = windowMat⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hwindowSymm]
    have hpairComm : ∀ leftVec rightVec : Fin 3 → ℝ,
        leftVec ⬝ᵥ (windowMat⁻¹ *ᵥ rightVec)
          = rightVec ⬝ᵥ (windowMat⁻¹ *ᵥ leftVec) :=
      dotProduct_mulVec_comm_of_transpose_eq hinvSymm
    have hwindowInvAction : ∀ probeVec : Fin 3 → ℝ,
        windowMat *ᵥ (windowMat⁻¹ *ᵥ probeVec) = probeVec := fun probeVec => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hwindowDetUnit,
        Matrix.one_mulVec]
    -- the pairing matrix and the tie frame
    set pairingMat : Matrix (Fin 4) (Fin 4) ℝ :=
      Matrix.of fun leftIdx rightIdx => bAtom leftIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom rightIdx)
      with hpairingMatDef
    have hpairingApp : ∀ leftIdx rightIdx, pairingMat leftIdx rightIdx
        = bAtom leftIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom rightIdx) := by
      intro leftIdx rightIdx
      simp only [hpairingMatDef, Matrix.of_apply]
    have hpairingSymm : pairingMatᵀ = pairingMat := by
      ext leftIdx rightIdx
      rw [Matrix.transpose_apply, hpairingApp, hpairingApp]
      exact hpairComm _ _
    have hdesignEntry : ∀ leftIdx rightIdx : Fin 4,
        ∑ midIdx, pairingMat leftIdx midIdx * coweightFour midIdx
            * pairingMat midIdx rightIdx
          = pairingMat leftIdx rightIdx := by
      intro leftIdx rightIdx
      have hbil := dotProduct_weightedAtomSum_mulVec coweightFour bAtom
        (windowMat⁻¹ *ᵥ bAtom leftIdx) (windowMat⁻¹ *ᵥ bAtom rightIdx)
      rw [← hwindowMatDef, hwindowInvAction] at hbil
      calc ∑ midIdx, pairingMat leftIdx midIdx * coweightFour midIdx
              * pairingMat midIdx rightIdx
          = ∑ midIdx, coweightFour midIdx
              * (bAtom midIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom leftIdx))
              * (bAtom midIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom rightIdx)) := by
            refine Finset.sum_congr rfl fun midIdx _ => ?_
            rw [hpairingApp, hpairingApp, hpairComm (bAtom leftIdx) (bAtom midIdx)]
            ring
        _ = (windowMat⁻¹ *ᵥ bAtom leftIdx) ⬝ᵥ bAtom rightIdx := hbil.symm
        _ = pairingMat leftIdx rightIdx := by
            rw [dotProduct_comm, hpairComm (bAtom rightIdx) (bAtom leftIdx),
              hpairingApp]
    have hCDdesign : pairingMat * Matrix.diagonal coweightFour * pairingMat
        = pairingMat := by
      ext leftIdx rightIdx
      rw [Matrix.mul_apply]
      rw [Finset.sum_congr rfl fun midIdx _ => by rw [Matrix.mul_diagonal]]
      exact hdesignEntry leftIdx rightIdx
    have htotalTie : ∀ slotIdx, pairingMat slotIdx slotIdx = 1 := fun slotIdx => by
      rw [hpairingApp]
      exact hunitPivot slotIdx
    have hcoweightSumThree : ∑ slotIdx, coweightFour slotIdx = ((4 : ℕ) : ℝ) - 1 := by
      have hsub : ∑ slotIdx, coweightFour slotIdx = 4 - ∑ slotIdx, bWeight slotIdx := by
        simp only [hcoweightFourDef]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num
      rw [hsub, hbWeightSum]
      norm_num
    -- the survivor axis data
    set survivorCoord := baseAtom survivorLabel survivorIdx with hsurvivorCoordDef
    have hposDiagNe : ∀ posIdx : Fin 3, baseAtom (posEnum posIdx) posIdx ≠ 0 := by
      intro posIdx hzero
      have hentry := congrFun (congrFun hposSide posIdx) posIdx
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
        Matrix.vecMulVec_apply, Matrix.one_apply_eq] at hentry
      rw [Finset.sum_eq_single_of_mem posIdx (Finset.mem_univ posIdx)
        (fun otherIdx _ hne => by
          rw [hdiagonal otherIdx posIdx (Ne.symm hne)]
          ring)] at hentry
      rw [hzero] at hentry
      simp at hentry
    have hsurvivorCoordNe : survivorCoord ≠ 0 := by
      rw [hsurvivorCoordDef, hsurvivorLabelDef]
      exact hposDiagNe survivorIdx
    have hsurvivorAxis : baseAtom survivorLabel
        = survivorCoord • axisVector survivorIdx := by
      funext coordIdx
      rcases hcoverFin3 coordIdx with hisFirst | hisSecond | hisSurv
      · rw [hisFirst]
        have hlhs : baseAtom survivorLabel firstVanishedIdx = 0 := by
          rw [hsurvivorLabelDef]
          exact hdiagonal survivorIdx firstVanishedIdx (Ne.symm hsurvNeFirst)
        rw [hlhs]
        simp only [Pi.smul_apply, axisVector, smul_eq_mul]
        rw [if_neg (Ne.symm hsurvNeFirst), mul_zero]
      · rw [hisSecond]
        have hlhs : baseAtom survivorLabel secondVanishedIdx = 0 := by
          rw [hsurvivorLabelDef]
          exact hdiagonal survivorIdx secondVanishedIdx (Ne.symm hsurvNeSecond)
        rw [hlhs]
        simp only [Pi.smul_apply, axisVector, smul_eq_mul]
        rw [if_neg (Ne.symm hsurvNeSecond), mul_zero]
      · rw [hisSurv]
        simp only [Pi.smul_apply, axisVector, smul_eq_mul]
        rw [if_true, mul_one, hsurvivorCoordDef]
    have haxisResolve : ∑ negIdx, ((-stressCoeff (negEnum negIdx))
          * (baseAtom (negEnum negIdx) ⬝ᵥ axisVector survivorIdx))
          • baseAtom (negEnum negIdx)
        = axisVector survivorIdx := by
      have happly := congrArg (fun mat => mat *ᵥ axisVector survivorIdx) hnegSide
      rw [Matrix.sum_mulVec, Matrix.one_mulVec] at happly
      calc ∑ negIdx, ((-stressCoeff (negEnum negIdx))
              * (baseAtom (negEnum negIdx) ⬝ᵥ axisVector survivorIdx))
              • baseAtom (negEnum negIdx)
          = ∑ negIdx, ((-stressCoeff (negEnum negIdx))
              • atomMatrix (baseAtom (negEnum negIdx))) *ᵥ axisVector survivorIdx := by
            refine Finset.sum_congr rfl fun negIdx _ => ?_
            rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_dotProduct_smul, smul_smul]
        _ = axisVector survivorIdx := happly
    -- the raw dependency and its normalisation
    set rawDep : Fin 4 → ℝ := Fin.cons 1 (fun negIdx =>
      -(survivorCoord * ((-stressCoeff (negEnum negIdx))
          * (baseAtom (negEnum negIdx) ⬝ᵥ axisVector survivorIdx)))) with hrawDepDef
    have hrawDepZero : rawDep 0 = 1 := by simp only [hrawDepDef, Fin.cons_zero]
    have hrawDepSucc : ∀ negIdx : Fin 3, rawDep (Fin.succ negIdx)
        = -(survivorCoord * ((-stressCoeff (negEnum negIdx))
            * (baseAtom (negEnum negIdx) ⬝ᵥ axisVector survivorIdx))) := by
      intro negIdx
      simp only [hrawDepDef, Fin.cons_succ]
    have hrawVec : ∑ slotIdx, rawDep slotIdx • bAtom slotIdx = 0 := by
      rw [Fin.sum_univ_succ, hrawDepZero, hbAtomZero, one_smul]
      have hsummand : ∀ negIdx : Fin 3,
          rawDep (Fin.succ negIdx) • bAtom (Fin.succ negIdx)
          = -(survivorCoord • (((-stressCoeff (negEnum negIdx))
              * (baseAtom (negEnum negIdx) ⬝ᵥ axisVector survivorIdx))
                • baseAtom (negEnum negIdx))) := by
        intro negIdx
        rw [hrawDepSucc negIdx, hbAtomSucc negIdx, smul_smul, neg_smul]
      rw [Finset.sum_congr rfl fun negIdx _ => hsummand negIdx, Finset.sum_neg_distrib,
        ← Finset.smul_sum, haxisResolve, hsurvivorAxis, add_neg_cancel]
    set normVal := ∑ slotIdx, (coweightFour slotIdx)⁻¹ * rawDep slotIdx ^ 2
      with hnormValDef
    have hnormPos : 0 < normVal := by
      rw [hnormValDef]
      refine Finset.sum_pos' (fun slotIdx _ => mul_nonneg (le_of_lt (inv_pos.mpr
        (hcoweightPosFour slotIdx))) (sq_nonneg _)) ⟨0, Finset.mem_univ 0, ?_⟩
      rw [hrawDepZero]
      simp only [one_pow, mul_one]
      exact inv_pos.mpr (hcoweightPosFour 0)
    set sqrtNorm := Real.sqrt normVal with hsqrtNormDef
    have hsqrtPos : 0 < sqrtNorm := Real.sqrt_pos.mpr hnormPos
    have hsqrtSq : sqrtNorm ^ 2 = normVal := Real.sq_sqrt (le_of_lt hnormPos)
    set alphaDepFour : Fin 4 → ℝ := fun slotIdx => sqrtNorm⁻¹ * rawDep slotIdx
      with halphaDepDef
    have halphaVecFour : ∑ slotIdx, alphaDepFour slotIdx • bAtom slotIdx = 0 := by
      have hsummand : ∀ slotIdx, alphaDepFour slotIdx • bAtom slotIdx
          = sqrtNorm⁻¹ • (rawDep slotIdx • bAtom slotIdx) := fun slotIdx => by
        simp only [halphaDepDef]
        rw [smul_smul]
      rw [Finset.sum_congr rfl fun slotIdx _ => hsummand slotIdx, ← Finset.smul_sum,
        hrawVec, smul_zero]
    have halphaNormFour : ∑ slotIdx, (coweightFour slotIdx)⁻¹
        * alphaDepFour slotIdx ^ 2 = 1 := by
      have hterm : ∀ slotIdx, (coweightFour slotIdx)⁻¹ * alphaDepFour slotIdx ^ 2
          = (sqrtNorm ^ 2)⁻¹ * ((coweightFour slotIdx)⁻¹ * rawDep slotIdx ^ 2) := by
        intro slotIdx
        simp only [halphaDepDef]
        ring
      rw [Finset.sum_congr rfl fun slotIdx _ => hterm slotIdx, ← Finset.mul_sum,
        ← hnormValDef, hsqrtSq]
      exact inv_mul_cancel₀ (ne_of_gt hnormPos)
    have halphaAnni : pairingMat *ᵥ alphaDepFour = 0 := by
      funext rowIdx
      have hrowVal : (pairingMat *ᵥ alphaDepFour) rowIdx
          = ∑ slotIdx, alphaDepFour slotIdx
              * (bAtom rowIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom slotIdx)) := by
        simp only [Matrix.mulVec, dotProduct, hpairingMatDef, Matrix.of_apply]
        exact Finset.sum_congr rfl fun slotIdx _ => by ring
      rw [hrowVal, Pi.zero_apply]
      calc ∑ slotIdx, alphaDepFour slotIdx
              * (bAtom rowIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom slotIdx))
          = bAtom rowIdx ⬝ᵥ (∑ slotIdx, alphaDepFour slotIdx
              • (windowMat⁻¹ *ᵥ bAtom slotIdx)) := by
            rw [dotProduct_sum]
            exact Finset.sum_congr rfl fun slotIdx _ => by
              rw [dotProduct_smul, smul_eq_mul]
        _ = bAtom rowIdx ⬝ᵥ (windowMat⁻¹
              *ᵥ (∑ slotIdx, alphaDepFour slotIdx • bAtom slotIdx)) := by
            rw [mulVec_sum_smul]
        _ = 0 := by rw [halphaVecFour, Matrix.mulVec_zero, dotProduct_zero]
    -- the tie frame fires
    have hframe := tieFrame_of_totalTie coweightFour hcoweightPosFour pairingMat
      hpairingSymm hCDdesign htotalTie hcoweightSumThree alphaDepFour halphaAnni
      halphaNormFour
    have halphaSqFour : ∀ slotIdx, alphaDepFour slotIdx ^ 2
        = coweightFour slotIdx * bWeight slotIdx := by
      intro slotIdx
      have hsq := dependency_sq_eq_of_tieFrame coweightFour pairingMat alphaDepFour
        htotalTie hframe slotIdx
      rw [hsq]
      have hconv : 1 - coweightFour slotIdx = bWeight slotIdx := by
        simp only [hcoweightFourDef]
        ring
      rw [hconv]
    have halphaNeFour : ∀ slotIdx, alphaDepFour slotIdx ≠ 0 := by
      intro slotIdx hzero
      have hsq := halphaSqFour slotIdx
      rw [hzero] at hsq
      have hzeroSq : (0 : ℝ) = coweightFour slotIdx * bWeight slotIdx := by
        rw [← hsq]
        ring
      linarith [mul_pos (hcoweightPosFour slotIdx) (hbWeightPos slotIdx)]
    have hpairingFour : ∀ leftIdx rightIdx, leftIdx ≠ rightIdx →
        coweightFour leftIdx * coweightFour rightIdx
            * (bAtom leftIdx ⬝ᵥ (windowMat⁻¹ *ᵥ bAtom rightIdx))
          = -(alphaDepFour leftIdx * alphaDepFour rightIdx) := by
      intro leftIdx rightIdx hne
      have hpaired := pairing_eq_of_tieFrame coweightFour pairingMat alphaDepFour
        hframe hne
      rw [hpairingApp] at hpaired
      exact hpaired
    -- the negative survivor coordinates never vanish at the tie
    have hnegSurvivorNe : ∀ negIdx : Fin 3,
        baseAtom (negEnum negIdx) ⬝ᵥ axisVector survivorIdx ≠ 0 := by
      intro negIdx hzeroCoord
      have halphaNeVal := halphaNeFour (Fin.succ negIdx)
      simp only [halphaDepDef] at halphaNeVal
      have hrawNe : rawDep (Fin.succ negIdx) ≠ 0 := by
        intro hrawZero
        rw [hrawZero, mul_zero] at halphaNeVal
        exact halphaNeVal rfl
      rw [hrawDepSucc negIdx, hzeroCoord] at hrawNe
      simp at hrawNe
    -- the stress relation and the master identity
    have hstressMat : ∑ label, stressCoeff label • atomMatrix (baseAtom label) = 0 := by
      rw [hsplitSix (carrier := Matrix (Fin 3) (Fin 3) ℝ)
        (fun label => stressCoeff label • atomMatrix (baseAtom label)), hposSide]
      have hnegSum : ∑ negIdx, stressCoeff (negEnum negIdx)
          • atomMatrix (baseAtom (negEnum negIdx)) = -1 := by
        have hterm : ∀ negIdx : Fin 3, stressCoeff (negEnum negIdx)
            • atomMatrix (baseAtom (negEnum negIdx))
            = -((-stressCoeff (negEnum negIdx))
                • atomMatrix (baseAtom (negEnum negIdx))) := by
          intro negIdx
          rw [neg_smul, neg_neg]
        rw [Finset.sum_congr rfl fun negIdx _ => hterm negIdx, Finset.sum_neg_distrib,
          hnegSide]
      rw [hnegSum, add_neg_cancel]
    have hmaster := sum_stress_mul_pivotDefect_eq_zero windowMat stressCoeff baseAtom
      hstressMat hzeroSum
    rw [hsplitSix (carrier := ℝ) (fun label => stressCoeff label
        * (pivotAgainst windowMat (baseAtom label) - 1)),
      hsplitThree (carrier := ℝ) (fun posIdx => stressCoeff (posEnum posIdx)
        * (pivotAgainst windowMat (baseAtom (posEnum posIdx)) - 1)),
      ← hsurvivorLabelDef] at hmaster
    have hpvSurvivor : pivotAgainst windowMat (baseAtom survivorLabel) = 1 := by
      have hzeroSlot := hallOne 0
      rw [hbAtomZero] at hzeroSlot
      exact hzeroSlot
    have hpvNegative : ∀ negIdx : Fin 3,
        pivotAgainst windowMat (baseAtom (negEnum negIdx)) = 1 := by
      intro negIdx
      have hsuccSlot := hallOne (Fin.succ negIdx)
      rw [hbAtomSucc negIdx] at hsuccSlot
      exact hsuccSlot
    have hnegPartZero : ∑ negIdx, stressCoeff (negEnum negIdx)
        * (pivotAgainst windowMat (baseAtom (negEnum negIdx)) - 1) = 0 :=
      Finset.sum_eq_zero fun negIdx _ => by rw [hpvNegative negIdx]; ring
    have hsurvTermZero : stressCoeff survivorLabel
        * (pivotAgainst windowMat (baseAtom survivorLabel) - 1) = 0 := by
      rw [hpvSurvivor]
      ring
    rw [hnegPartZero, add_zero, hsurvTermZero, add_zero] at hmaster
    -- hmaster : sigmaF * (pvF - 1) + sigmaG * (pvG - 1) = 0
    have hsigmaFirstPos := hposSign firstVanishedIdx
    have hsigmaSecondPos := hposSign secondVanishedIdx
    set pvFirst := pivotAgainst windowMat (baseAtom (posEnum firstVanishedIdx))
      with hpvFirstDef
    set pvSecond := pivotAgainst windowMat (baseAtom (posEnum secondVanishedIdx))
      with hpvSecondDef
    have hpvFirstDot : pvFirst = baseAtom (posEnum firstVanishedIdx)
        ⬝ᵥ (windowMat⁻¹ *ᵥ baseAtom (posEnum firstVanishedIdx)) := by
      rw [hpvFirstDef]
      exact pivotAgainst_eq_dotProduct _ _
    have hpvSecondDot : pvSecond = baseAtom (posEnum secondVanishedIdx)
        ⬝ᵥ (windowMat⁻¹ *ᵥ baseAtom (posEnum secondVanishedIdx)) := by
      rw [hpvSecondDef]
      exact pivotAgainst_eq_dotProduct _ _
    -- the finish helper: an exchange PosDef becomes the selected Finset
    have hfinishExchange : ∀ spikeLabel : Fin 6,
        (∀ slotIdx : Fin 4, bottomLabel slotIdx ≠ spikeLabel) →
        (∃ highIdx lowIdx : Fin 4, highIdx ≠ lowIdx
          ∧ (windowMat - atomMatrix (bAtom highIdx) - atomMatrix (bAtom lowIdx)
              + atomMatrix (baseAtom spikeLabel)).PosDef) →
        ∃ selected : Finset (Fin 6), selected.card = 3
          ∧ ((∑ label ∈ selected, atomMatrix (baseAtom label)) - gram).PosDef := by
      rintro spikeLabel hnotBottom ⟨highIdx, lowIdx, hne, hposdef⟩
      have hmemHigh : bottomLabel highIdx ∈ Finset.univ.image bottomLabel :=
        Finset.mem_image.mpr ⟨highIdx, Finset.mem_univ highIdx, rfl⟩
      have hmemLowErase : bottomLabel lowIdx
          ∈ (Finset.univ.image bottomLabel).erase (bottomLabel highIdx) :=
        Finset.mem_erase.mpr ⟨fun hEq => Ne.symm hne (hbottomInjective hEq),
          Finset.mem_image.mpr ⟨lowIdx, Finset.mem_univ lowIdx, rfl⟩⟩
      have hspikeNotMem : spikeLabel
          ∉ ((Finset.univ.image bottomLabel).erase (bottomLabel highIdx)).erase
              (bottomLabel lowIdx) := by
        intro hmem
        obtain ⟨slotIdx, _, hslotEq⟩ := Finset.mem_image.mp
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
        exact hnotBottom slotIdx hslotEq
      refine ⟨insert spikeLabel (((Finset.univ.image bottomLabel).erase
        (bottomLabel highIdx)).erase (bottomLabel lowIdx)), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hspikeNotMem,
          Finset.card_erase_of_mem hmemLowErase, Finset.card_erase_of_mem hmemHigh,
          Finset.card_image_of_injective _ hbottomInjective, Finset.card_univ,
          Fintype.card_fin]
      · have himage : ∑ label ∈ Finset.univ.image bottomLabel,
            atomMatrix (baseAtom label) = ∑ slotIdx, atomMatrix (bAtom slotIdx) := by
          rw [Finset.sum_image fun leftIdx _ rightIdx _ hEq => hbottomInjective hEq]
        have hpeelHigh := Finset.sum_erase_add (Finset.univ.image bottomLabel)
          (fun label => atomMatrix (baseAtom label)) hmemHigh
        rw [himage] at hpeelHigh
        have hconvHigh : atomMatrix (baseAtom (bottomLabel highIdx))
            = atomMatrix (bAtom highIdx) := by simp only [hbAtomDef]
        rw [hconvHigh] at hpeelHigh
        have hpeelLow := Finset.sum_erase_add
          ((Finset.univ.image bottomLabel).erase (bottomLabel highIdx))
          (fun label => atomMatrix (baseAtom label)) hmemLowErase
        rw [eq_sub_of_add_eq hpeelHigh] at hpeelLow
        have hconvLow : atomMatrix (baseAtom (bottomLabel lowIdx))
            = atomMatrix (bAtom lowIdx) := by simp only [hbAtomDef]
        rw [hconvLow] at hpeelLow
        have hgapEq : (∑ label ∈ insert spikeLabel
              (((Finset.univ.image bottomLabel).erase (bottomLabel highIdx)).erase
                (bottomLabel lowIdx)), atomMatrix (baseAtom label)) - gram
            = windowMat - atomMatrix (bAtom highIdx) - atomMatrix (bAtom lowIdx)
              + atomMatrix (baseAtom spikeLabel) := by
          rw [Finset.sum_insert hspikeNotMem, eq_sub_of_add_eq hpeelLow, hwindowAlt]
          abel
        rw [hgapEq]
        exact hposdef
    -- the engine, instantiated with the tie-frame data
    have hengine : ∀ spikeVec : Fin 3 → ℝ,
        1 ≤ spikeVec ⬝ᵥ (windowMat⁻¹ *ᵥ spikeVec) →
        (∃ highIdx lowIdx : Fin 4, highIdx ≠ lowIdx
            ∧ (windowMat - atomMatrix (bAtom highIdx) - atomMatrix (bAtom lowIdx)
                + atomMatrix spikeVec).PosDef)
          ∨ (spikeVec ⬝ᵥ (windowMat⁻¹ *ᵥ spikeVec) ≤ 1
              ∧ ((∃ (slot : Fin 4) (ratio : ℝ), spikeVec = ratio • bAtom slot)
                ∨ (∃ pairedSlot : Fin 4, pairedSlot ≠ 0
                    ∧ ∃ scaleZero scalePaired : ℝ, scaleZero ≠ 0 ∧ scalePaired ≠ 0
                    ∧ spikeVec = scaleZero • bAtom 0 + scalePaired • bAtom pairedSlot))) :=
      fun spikeVec hpivotGe => spike_lane_engine windowMat hwindowPosDef bAtom bWeight
        coweightFour alphaDepFour hbWeightPos hbWeightSum hwindowMatDef halphaVecFour
        halphaSqFour halphaNeFour hunitPivot hpairingFour spikeVec hpivotGe
    -- the ratio fallback dies on primitivity
    have hkillRatio : ∀ spikeIdx : Fin 3,
        (∀ slotIdx : Fin 4, bottomLabel slotIdx ≠ posEnum spikeIdx) →
        ∀ (slot : Fin 4) (ratio : ℝ),
          baseAtom (posEnum spikeIdx) = ratio • bAtom slot → False := by
      intro spikeIdx hnotBottom slot ratio hEq
      refine hprimitive (bottomLabel slot) (posEnum spikeIdx) ratio (hnotBottom slot) ?_
      rw [hEq]
    -- the geometric data for the doubly paired case
    have hsurvAtFirst : baseAtom survivorLabel firstVanishedIdx = 0 := by
      rw [hsurvivorLabelDef]
      exact hdiagonal survivorIdx firstVanishedIdx (Ne.symm hsurvNeFirst)
    have hsurvAtSecond : baseAtom survivorLabel secondVanishedIdx = 0 := by
      rw [hsurvivorLabelDef]
      exact hdiagonal survivorIdx secondVanishedIdx (Ne.symm hsurvNeSecond)
    have hsurvCoordNeRaw : baseAtom survivorLabel survivorIdx ≠ 0 := by
      rw [← hsurvivorCoordDef]
      exact hsurvivorCoordNe
    have hnegOrthogonal : ∀ leftIdx rightIdx : Fin 3, leftIdx ≠ rightIdx →
        baseAtom (negEnum leftIdx) ⬝ᵥ baseAtom (negEnum rightIdx) = 0 :=
      fun leftIdx rightIdx hne =>
        dotProduct_eq_zero_of_resolution (fun negIdx => -stressCoeff (negEnum negIdx))
          (fun negIdx => baseAtom (negEnum negIdx))
          (fun negIdx => by linarith [hnegSign negIdx]) hnegSide hne
    have hnegSurvCoordNe : ∀ negIdx : Fin 3,
        baseAtom (negEnum negIdx) survivorIdx ≠ 0 := by
      intro negIdx
      have hpairNe := hnegSurvivorNe negIdx
      rwa [dotProduct_axisVector] at hpairNe
    have hfirstSpikeAtSecond : baseAtom (posEnum firstVanishedIdx) secondVanishedIdx = 0 :=
      hdiagonal firstVanishedIdx secondVanishedIdx (Ne.symm hvanNe)
    have hfirstSpikeAtSurv : baseAtom (posEnum firstVanishedIdx) survivorIdx = 0 :=
      hdiagonal firstVanishedIdx survivorIdx hsurvNeFirst
    have hsecondSpikeAtFirst : baseAtom (posEnum secondVanishedIdx) firstVanishedIdx = 0 :=
      hdiagonal secondVanishedIdx firstVanishedIdx hvanNe
    have hnotParallelNeg : ∀ (negIdx : Fin 3) (ratio : ℝ),
        baseAtom (negEnum negIdx) ≠ ratio • baseAtom survivorLabel := by
      intro negIdx ratio hEq
      rw [hsurvivorLabelDef] at hEq
      exact hprimitive (posEnum survivorIdx) (negEnum negIdx) ratio
        (hposNegNe survivorIdx negIdx) hEq
    have hsumThreeReal : ∀ valueOf : Fin 3 → ℝ, ∑ coordIdx, valueOf coordIdx
        = valueOf firstVanishedIdx + valueOf secondVanishedIdx + valueOf survivorIdx :=
      fun valueOf => hsplitThree (carrier := ℝ) valueOf
    -- the trichotomy on the first spike pivot
    rcases lt_trichotomy pvFirst 1 with hFirstLt | hFirstEq | hFirstGt
    · -- the second spike pivot exceeds one; its exchange lane cannot fail
      have hSecondGt : 1 < pvSecond := by
        have hprodNeg : stressCoeff (posEnum firstVanishedIdx) * (pvFirst - 1) < 0 :=
          mul_neg_of_pos_of_neg hsigmaFirstPos (by linarith)
        by_contra hle
        push Not at hle
        have hprodNonpos : stressCoeff (posEnum secondVanishedIdx) * (pvSecond - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hsigmaSecondPos) (by linarith)
        linarith [hmaster]
      rcases hengine (baseAtom (posEnum secondVanishedIdx))
          (by rw [← hpvSecondDot]; linarith) with hexch | ⟨hle, _⟩
      · exact hfinishExchange (posEnum secondVanishedIdx) hbottomNeSecondSpike hexch
      · exfalso
        rw [← hpvSecondDot] at hle
        linarith
    · -- both spike pivots equal one: run both engines, then the geometry
      have hSecondEq : pvSecond = 1 := by
        have hzeroFirst : stressCoeff (posEnum firstVanishedIdx) * (pvFirst - 1) = 0 := by
          rw [hFirstEq]
          ring
        have hzeroSecond : stressCoeff (posEnum secondVanishedIdx) * (pvSecond - 1) = 0 := by
          linarith [hmaster]
        rcases mul_eq_zero.mp hzeroSecond with hcontra | hdiff
        · exact absurd hcontra (ne_of_gt hsigmaSecondPos)
        · linarith
      rcases hengine (baseAtom (posEnum firstVanishedIdx))
          (by rw [← hpvFirstDot]; exact le_of_eq hFirstEq.symm) with hexchF | ⟨_, hfallF⟩
      · exact hfinishExchange (posEnum firstVanishedIdx) hbottomNeFirstSpike hexchF
      · rcases hfallF with ⟨slot, ratio, hEqRatio⟩
          | ⟨slotF, hslotFNe, scaleFZ, scaleFN, hscaleFZ, hscaleFN, hEqF⟩
        · exact (hkillRatio firstVanishedIdx hbottomNeFirstSpike slot ratio hEqRatio).elim
        · rcases hengine (baseAtom (posEnum secondVanishedIdx))
              (by rw [← hpvSecondDot]; exact le_of_eq hSecondEq.symm) with
            hexchG | ⟨_, hfallG⟩
          · exact hfinishExchange (posEnum secondVanishedIdx) hbottomNeSecondSpike hexchG
          · rcases hfallG with ⟨slot, ratio, hEqRatio⟩
              | ⟨slotG, hslotGNe, scaleGZ, scaleGN, hscaleGZ, hscaleGN, hEqG⟩
            · exact (hkillRatio secondVanishedIdx hbottomNeSecondSpike slot ratio
                hEqRatio).elim
            · exfalso
              obtain ⟨negF, hnegF⟩ :=
                (Fin.eq_zero_or_eq_succ slotF).resolve_left hslotFNe
              obtain ⟨negG, hnegG⟩ :=
                (Fin.eq_zero_or_eq_succ slotG).resolve_left hslotGNe
              rw [hnegF, hbAtomZero, hbAtomSucc negF] at hEqF
              rw [hnegG, hbAtomZero, hbAtomSucc negG] at hEqG
              exact no_doubly_paired_spikes hsumThreeReal hsurvAtFirst hsurvAtSecond
                hsurvCoordNeRaw hnegOrthogonal hnegSurvCoordNe hfirstSpikeAtSecond
                hfirstSpikeAtSurv hsecondSpikeAtFirst hnotParallelNeg hscaleFZ hscaleFN
                hscaleGN hEqF hEqG hcoverFin3
    · -- the first spike pivot exceeds one; its exchange lane cannot fail
      rcases hengine (baseAtom (posEnum firstVanishedIdx))
          (by rw [← hpvFirstDot]; linarith) with hexch | ⟨hle, _⟩
      · exact hfinishExchange (posEnum firstVanishedIdx) hbottomNeFirstSpike hexch
      · exfalso
        rw [← hpvFirstDot] at hle
        linarith


end Gtz
