/-
# Corank one, field-generically: the trace budget and the Jensen chart

At `size = rank + 1` every weighted design has a dominating `rank`-subset, over ℝ
and over ℂ alike.  This file proves it twice over — once as the operative proof
(a TRACE budget), once as the chart reading the campaign brief calls A4 (the
Jensen quantity `p_c`) — and pins the equality case to the repository's
corank-one leverage law.

**THE OPERATIVE PROOF: a trace budget, not Jensen.**  Let
`coParsevalOperator = Σ_c (1 - t_c) g_c g_cᴴ`, positive definite for `2 ≤ size`,
and let

    coParsevalPivotScalar c = g_cᴴ coParsevalOperator⁻¹ g_c
                            = tr(coParsevalOperator⁻¹ g_c g_cᴴ).

One trace computation gives `Σ_c (1 - t_c) · pivot c = tr(1) = rank`, while
`Σ_c (1 - t_c) = size - 1`.  At `size = rank + 1` the two agree, so the pivots
have co-weighted mean exactly one and some pivot is at most one; the rank-one
Schur criterion then says the erasure of that atom dominates, and the erasure has
size exactly `rank`.

No kernel vector, no projection chart, no Naimark duality, no whitening, no
matrix square root.  Over ℝ this is `Gtz.descent_identity`
(`Gtz/Reduction/DescentLadder.lean`), whose own header already records that the
identity "is field-blind by construction", plus
`Gtz.erase_dominates_iff_pivot_le_one` (`Gtz/Design/TraceIdentity.lean` — the
`Ties` layer only CONSUMES it).  What is new here is the ℂ instance, which
nothing in `Gtz/Complex/` had.

**THE TOTAL TIE, and why it needs no strict Schur criterion.**  A fourth section
below proves that at corank one the value is EXACTLY one whenever it is at most
one: if every erasure dominates then the budget forces every pivot to equal one,
and pivot one hands over an EXPLICIT null vector `coParsevalOperator⁻¹ g_c` of the
erasure gap, so the gap is positive semidefinite but not positive definite.  That
matters because Mathlib v4.32's Schur-complement criteria
(`Matrix.PosDef.fromBlocks₁₁/₂₂`) conclude PosSemidef only — there is no strict
twin to invoke, and none is needed.

**A4 (the Jensen chart), and exactly what it costs.**  A4 works with
`p_c = |z_c|²/(1 - t_c)` where `z` spans `ker Vᴴ`, using `P = 1 - z zᴴ`.  Only
the DIAGONAL of that identity is needed to define `p_c`, and the diagonal of `P`
is `t_c · leverage_c` for free (`Gtz.projectionChart_diagonal`).  So `p_c` is
defined here WITHOUT any kernel vector as

    jensenRatio c = (1 - t_c · leverage_c) / (1 - t_c),

and `jensenRatio_eq_kernelNormSq_div_coWeight` proves it agrees with A4's
`|z_c|²/(1 - t_c)` for ANY `z` realising `P = 1 - z zᴴ`.  On that definition:

  * A4(i)   normalisation — `sum_jensenRatio_mul_coWeight` : `Σ_c p_c (1 - t_c) = size - rank`,
    hence `Σ_c p_c - Σ_c t_c p_c = 1` at corank one;
  * A4(iii) max-at-least-weighted-average — `exists_jensenRatio_ge_weightedAverage`,
    and its consequence `sum_erase_jensenRatio_le_one`;
  * A4(iv)  the equality case — `jensenRatio_eq_inv_rank_iff_leverageIdentity` :
    `p_c = 1/rank ↔ rank · t_c · leverage_c = (rank - 1) + t_c`, which is
    VERBATIM the repository's corank-one tie law
    `Gtz.isTie_iff_leverage_identity` (`Gtz/Ties/CorankOneTieCriterion.lean`).
    The agreement with `Gtz.IsTie` itself is proved over ℝ in
    `Gtz/Complex/SizeAxis.lean`, which may import the `Ties` layer.

**THE ONE PIECE OF A4 THAT IS NOT HERE, named.**  A4(ii) is the domination
criterion.  In the PIVOT chart it is proved unconditionally and at every size:
`fieldDominates_erase_iff_coParsevalPivot_le_one`.  In the JENSEN chart it reads
`Dominates (univ.erase c₀) ↔ Σ_{c ≠ c₀} p_c ≤ 1`, and that form needs a unit
vector `z` with `1 - projectionChart = z zᴴ` — i.e. uniqueness of rank-one
Hermitian idempotents, which Mathlib v4.32 does not package (over ℝ the
repository runs it by hand via Householder in `Gtz/Ties/CorankOneTieExistence.lean`,
at a cost of some 380 lines).  It is therefore NOT PROVED here.  It is instead
NAMED — `JensenErasureCriterion` is the statement, left as an open proposition —
and the reduction to it is shipped: given any `z` realising the projector
identity, `jensenSum_eq_kernel_schur_quantity` rewrites the Jensen sum
`Σ_{c ≠ c₀} p_c` as the rank-one Schur quantity `Σ_{c ≠ c₀} |z_c|²/(1 - t_c)` that
`Gtz.posSemidef_sub_fieldAtom_iff` consumes.  Nothing below assumes the projector
exists, and `fieldGtzWeighted_corank_one` does not depend on any of it.

**AND THE CRITERION IS INDEXED BY THE CORANK-ONE SHAPE, NOT BY AN ARBITRARY
SIZE — because size-generically it is FALSE.**  A4(ii)'s derivation needs
`projectionChart = 1 - z zᴴ`, which is a corank-one fact; at other sizes the
correction has higher rank and the single-index sum is simply the wrong
expression.  The failure is concrete and shipped, not merely warned about: at
`size = rank = 1` the erasure is the empty subset, so the right-hand side is an
empty sum satisfying `0 ≤ 1` while the left-hand side asks the `1 × 1` matrix
`-1` to be positive semidefinite.  That is
`not_jensenErasureCriterion_at_singleton`, built from the same
`Gtz.degenerateSingletonDesign` that refutes an unconditional A2.  So
`JensenErasureCriterion` takes the RANK as its only numeric parameter and
quantifies over `FieldWeightedDesign Scalar (rank + 1) rank`; a future lane
aiming at it is aiming at a true target.
-/
import Mathlib
import Gtz.Field.WeightedDesign
import Gtz.Design.ProjectionChart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix
open scoped ComplexOrder

variable {Scalar : Type*} [RCLike Scalar]

/-! ## The trace bridge -/

/-- `tr(base · g gᴴ) = gᴴ base g`: the pivot is a trace. -/
theorem trace_mul_fieldAtom {rank : ℕ} (base : Matrix (Fin rank) (Fin rank) Scalar)
    (vector : Fin rank → Scalar) :
    Matrix.trace (base * fieldAtom vector) = star vector ⬝ᵥ (base *ᵥ vector) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, fieldAtom,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The pivot of an atom against the co-Parseval resolvent, as a field scalar. -/
noncomputable def coParsevalPivotScalar {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (atomIndex : Fin size) : Scalar :=
  star (design.atom atomIndex)
    ⬝ᵥ ((coParsevalOperator design)⁻¹ *ᵥ design.atom atomIndex)

/-- **THE BUDGET IDENTITY.**  The co-weighted pivots sum to the rank.  One trace
computation: `Σ_c (1-t_c) tr(W⁻¹ g_c g_cᴴ) = tr(W⁻¹ W) = tr(1) = rank`. -/
theorem sum_coWeight_mul_coParsevalPivotScalar {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size) :
    ∑ atomIndex, ((1 - design.weight atomIndex : ℝ) : Scalar)
        * coParsevalPivotScalar design atomIndex
      = ((rank : ℝ) : Scalar) := by
  classical
  have hposDef := coParsevalOperator_posDef design hsize
  have hinvmul : (coParsevalOperator design)⁻¹ * coParsevalOperator design = 1 :=
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hposDef.isUnit)
  calc ∑ atomIndex, ((1 - design.weight atomIndex : ℝ) : Scalar)
          * coParsevalPivotScalar design atomIndex
      = ∑ atomIndex, Matrix.trace ((coParsevalOperator design)⁻¹
          * (((1 - design.weight atomIndex : ℝ) : Scalar)
              • fieldAtom (design.atom atomIndex))) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, coParsevalPivotScalar,
          trace_mul_fieldAtom]
    _ = Matrix.trace ((coParsevalOperator design)⁻¹ * coParsevalOperator design) := by
        rw [coParsevalOperator, Matrix.mul_sum, Matrix.trace_sum]
    _ = ((rank : ℝ) : Scalar) := by
        rw [hinvmul, Matrix.trace_one, Fintype.card_fin]
        norm_cast

/-- The real shadow of the pivot. -/
noncomputable def coParsevalPivotValue {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (atomIndex : Fin size) : ℝ :=
  RCLike.re (coParsevalPivotScalar design atomIndex)

theorem coParsevalPivotScalar_nonneg {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size)
    (atomIndex : Fin size) : 0 ≤ coParsevalPivotScalar design atomIndex :=
  (coParsevalOperator_posDef design hsize).inv.posSemidef.dotProduct_mulVec_nonneg
    (design.atom atomIndex)

/-- The pivot is a nonnegative real embedded in the field, so its real shadow
carries all the information. -/
theorem coParsevalPivotScalar_eq_ofReal {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size)
    (atomIndex : Fin size) :
    coParsevalPivotScalar design atomIndex
      = ((coParsevalPivotValue design atomIndex : ℝ) : Scalar) := by
  have hselfAdjoint : IsSelfAdjoint (coParsevalPivotScalar design atomIndex) :=
    IsSelfAdjoint.of_nonneg (coParsevalPivotScalar_nonneg design hsize atomIndex)
  have hconj : (starRingEnd Scalar) (coParsevalPivotScalar design atomIndex)
      = coParsevalPivotScalar design atomIndex := hselfAdjoint
  exact (RCLike.conj_eq_iff_re.mp hconj).symm

/-- The budget identity, pushed down to the reals. -/
theorem sum_coWeight_mul_coParsevalPivotValue {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size) :
    ∑ atomIndex, (1 - design.weight atomIndex) * coParsevalPivotValue design atomIndex
      = (rank : ℝ) := by
  calc ∑ atomIndex, (1 - design.weight atomIndex) * coParsevalPivotValue design atomIndex
      = ∑ atomIndex, RCLike.re (((1 - design.weight atomIndex : ℝ) : Scalar)
          * coParsevalPivotScalar design atomIndex) := by
        refine Finset.sum_congr rfl fun atomIndex _ => ?_
        rw [RCLike.re_ofReal_mul, coParsevalPivotValue]
    _ = RCLike.re (∑ atomIndex, ((1 - design.weight atomIndex : ℝ) : Scalar)
          * coParsevalPivotScalar design atomIndex) := (map_sum _ _ _).symm
    _ = RCLike.re (((rank : ℝ) : Scalar)) := by
        rw [sum_coWeight_mul_coParsevalPivotScalar design hsize]
    _ = (rank : ℝ) := RCLike.ofReal_re _

/-! ## A4(ii) in the pivot chart: the erasure criterion -/

/-- The excess of erasing one atom is the co-Parseval operator minus that atom.
The subset arithmetic is `Finset.univ.erase`, never an order embedding. -/
theorem erasureGap_eq {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    (dropped : Fin size) :
    fieldSubsetSum design (Finset.univ.erase dropped) - 1
      = coParsevalOperator design - fieldAtom (design.atom dropped) := by
  classical
  have hsplit : fieldSubsetSum design (Finset.univ.erase dropped)
      + fieldAtom (design.atom dropped) = fieldSubsetSum design Finset.univ := by
    rw [fieldSubsetSum, fieldSubsetSum]
    exact Finset.sum_erase_add Finset.univ _ (Finset.mem_univ dropped)
  rw [coParsevalOperator_eq_universalGap, ← hsplit]
  abel

/-- **A4(ii) in the pivot chart**, unconditional and at EVERY size: erasing one
atom dominates exactly when that atom's co-Parseval pivot is at most one.  This
is the field-generic `Gtz.erase_dominates_iff_pivot_le_one`. -/
theorem fieldDominates_erase_iff_coParsevalPivot_le_one {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size)
    (dropped : Fin size) :
    FieldDominates design (Finset.univ.erase dropped)
      ↔ coParsevalPivotValue design dropped ≤ 1 := by
  classical
  have hcriterion := posSemidef_sub_fieldAtom_iff (coParsevalOperator design)
    (coParsevalOperator_posDef design hsize) (design.atom dropped)
  rw [FieldDominates, erasureGap_eq, hcriterion,
    show star (design.atom dropped) ⬝ᵥ ((coParsevalOperator design)⁻¹ *ᵥ design.atom dropped)
      = coParsevalPivotScalar design dropped from rfl,
    coParsevalPivotScalar_eq_ofReal design hsize dropped]
  constructor
  · intro hle
    have hcast : ((coParsevalPivotValue design dropped : ℝ) : Scalar) ≤ ((1 : ℝ) : Scalar) := by
      rwa [RCLike.ofReal_one]
    exact RCLike.ofReal_le_ofReal.mp hcast
  · intro hle
    calc ((coParsevalPivotValue design dropped : ℝ) : Scalar)
        ≤ ((1 : ℝ) : Scalar) := RCLike.ofReal_le_ofReal.mpr hle
      _ = 1 := RCLike.ofReal_one

/-! ## A4(iii): corank one, over both fields -/

/-- **The pigeonhole.**  At `size = rank + 1` the co-weights sum to `rank` and the
co-weighted pivots sum to `rank`, so the pivots have co-weighted mean exactly one
and cannot all exceed it. -/
theorem exists_coParsevalPivotValue_le_one {rank : ℕ} (hrank : 1 ≤ rank)
    (design : FieldWeightedDesign Scalar (rank + 1) rank) :
    ∃ dropped : Fin (rank + 1), coParsevalPivotValue design dropped ≤ 1 := by
  by_contra hall
  push Not at hall
  have hsize : 2 ≤ rank + 1 := by omega
  have hbudget := sum_coWeight_mul_coParsevalPivotValue design hsize
  have hmass := sum_coWeight (Scalar := Scalar) design
  have hcast : ((rank + 1 : ℕ) : ℝ) - 1 = (rank : ℝ) := by push_cast; ring
  rw [hcast] at hmass
  have hexcess : ∑ atomIndex, (1 - design.weight atomIndex)
      * (coParsevalPivotValue design atomIndex - 1) = 0 := by
    have hsplit : ∀ atomIndex : Fin (rank + 1),
        (1 - design.weight atomIndex) * (coParsevalPivotValue design atomIndex - 1)
          = (1 - design.weight atomIndex) * coParsevalPivotValue design atomIndex
            - (1 - design.weight atomIndex) := fun atomIndex => by ring
    simp only [hsplit]
    rw [Finset.sum_sub_distrib, hbudget, hmass, sub_self]
  have hpos : 0 < ∑ atomIndex, (1 - design.weight atomIndex)
      * (coParsevalPivotValue design atomIndex - 1) := by
    refine Finset.sum_pos (fun atomIndex _ => ?_) ⟨0, Finset.mem_univ 0⟩
    have hcoweight : 0 < 1 - design.weight atomIndex := by
      linarith [fieldWeight_lt_one design hsize atomIndex]
    exact mul_pos hcoweight (by linarith [hall atomIndex])
  rw [hexcess] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **A4(iii): CORANK ONE HOLDS OVER EVERY `RCLike` FIELD.**  Instantiating at ℂ
is the missing positive half of the complex size-axis description; instantiating
at ℝ reproves the shipped `Gtz.gtzWeighted_corank_one` without Naimark duality. -/
theorem fieldGtzWeighted_corank_one (rank : ℕ) (hrank : 1 ≤ rank) :
    FieldGtzWeighted Scalar (rank + 1) rank := by
  classical
  intro design
  have hsize : 2 ≤ rank + 1 := by omega
  obtain ⟨dropped, hdropped⟩ := exists_coParsevalPivotValue_le_one hrank design
  refine ⟨Finset.univ.erase dropped, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_univ dropped), Finset.card_univ, Fintype.card_fin]
    omega
  · exact (fieldDominates_erase_iff_coParsevalPivot_le_one design hsize dropped).mpr hdropped

/-! ## The total tie: at corank one the value is EXACTLY one, over every field

`fieldGtzWeighted_corank_one` says the value is at MOST one.  This section says
that whenever every erasure dominates, the value is exactly one — the excess is
positive semidefinite but never positive definite — and it says so over any
`RCLike` field with no strict Schur criterion, because Mathlib v4.32 has none.
Two steps.  First the budget: co-weighted pivots summing to the rank with every
pivot at most one and every co-weight strictly positive forces every pivot to
equal one.  Second an EXPLICIT null vector: pivot one makes
`coParsevalOperator⁻¹ g_c` a nonzero kernel vector of the erasure gap.

This is what settles, in the kernel rather than by citation, whether the corank-one
value one is attained.  The real-side existence of such designs is
`Gtz.exists_isTie_of_weights` and the complex-side transport is
`Gtz/Complex/SizeAxis.lean`. -/

/-- An atom acts on a vector by projecting onto its own direction:
`g gᴴ u = ⟨g, u⟩ · g`. -/
theorem fieldAtom_mulVec {rank : ℕ} (vector target : Fin rank → Scalar) :
    fieldAtom vector *ᵥ target = (star vector ⬝ᵥ target) • vector := by
  funext coordinate
  simp only [fieldAtom, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul, Pi.star_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- A positive definite matrix kills only the zero vector, so an exhibited nonzero
kernel vector refutes positive definiteness.  This is the strict-criterion
substitute: Mathlib v4.32's `Matrix.PosDef.fromBlocks₁₁/₂₂` conclude PosSemidef
only, and no strict Schur twin is needed. -/
theorem not_posDef_of_mulVec_eq_zero {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) Scalar}
    {witness : Fin rank → Scalar} (hkill : form *ᵥ witness = 0) (hnonzero : witness ≠ 0) :
    ¬ form.PosDef := by
  intro hposDef
  refine hnonzero (Matrix.mulVec_injective_of_isUnit hposDef.isUnit ?_)
  rw [hkill, Matrix.mulVec_zero]

/-- **Pivot one means the erasure sits at `λ_min = 1` exactly.**  The witness is
`coParsevalOperator⁻¹ g_c`: the gap sends it to `g_c - pivot · g_c = 0`, and it is
nonzero because pairing it against `g_c` returns the pivot, which is one. -/
theorem not_posDef_erasureGap_of_coParsevalPivot_eq_one {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size) (dropped : Fin size)
    (hpivot : coParsevalPivotValue design dropped = 1) :
    ¬ (fieldSubsetSum design (Finset.univ.erase dropped) - 1).PosDef := by
  have hposDef := coParsevalOperator_posDef design hsize
  have hdet : IsUnit (coParsevalOperator design).det :=
    Matrix.isUnit_iff_isUnit_det _ |>.mp hposDef.isUnit
  set witness : Fin rank → Scalar :=
    (coParsevalOperator design)⁻¹ *ᵥ design.atom dropped with hwitness
  have hscalar : star (design.atom dropped) ⬝ᵥ witness = 1 := by
    rw [hwitness, show star (design.atom dropped)
        ⬝ᵥ ((coParsevalOperator design)⁻¹ *ᵥ design.atom dropped)
      = coParsevalPivotScalar design dropped from rfl,
      coParsevalPivotScalar_eq_ofReal design hsize dropped, hpivot, RCLike.ofReal_one]
  have hkill : (coParsevalOperator design - fieldAtom (design.atom dropped)) *ᵥ witness = 0 := by
    rw [Matrix.sub_mulVec, fieldAtom_mulVec, hscalar, one_smul, hwitness, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, sub_self]
  have hnonzero : witness ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hscalar
    exact absurd hscalar.symm one_ne_zero
  rw [erasureGap_eq]
  exact not_posDef_of_mulVec_eq_zero hkill hnonzero

/-- **The budget forces equality.**  At corank one the co-weighted pivots sum to
the rank and the co-weights themselves sum to the rank, so if no pivot exceeds one
then none falls below it either.

`1 ≤ rank` is load-bearing, not decoration: at rank zero the co-Parseval operator
is the `0 × 0` matrix, every pivot is `0`, and the hypothesis holds vacuously while
the conclusion fails. -/
theorem forall_coParsevalPivotValue_eq_one_of_forall_fieldDominates {rank : ℕ}
    (hrank : 1 ≤ rank) (design : FieldWeightedDesign Scalar (rank + 1) rank)
    (hall : ∀ dropped : Fin (rank + 1), FieldDominates design (Finset.univ.erase dropped))
    (dropped : Fin (rank + 1)) : coParsevalPivotValue design dropped = 1 := by
  have hsize : 2 ≤ rank + 1 := by omega
  have hle : ∀ index : Fin (rank + 1), coParsevalPivotValue design index ≤ 1 :=
    fun index => (fieldDominates_erase_iff_coParsevalPivot_le_one design hsize index).mp (hall index)
  have hbudget := sum_coWeight_mul_coParsevalPivotValue design hsize
  have hmass := sum_coWeight (Scalar := Scalar) design
  have hcast : ((rank + 1 : ℕ) : ℝ) - 1 = (rank : ℝ) := by push_cast; ring
  rw [hcast] at hmass
  have hdeficit : ∑ index, (1 - design.weight index)
      * (1 - coParsevalPivotValue design index) = 0 := by
    have hsplit : ∀ index : Fin (rank + 1),
        (1 - design.weight index) * (1 - coParsevalPivotValue design index)
          = (1 - design.weight index)
            - (1 - design.weight index) * coParsevalPivotValue design index :=
      fun index => by ring
    simp only [hsplit]
    rw [Finset.sum_sub_distrib, hbudget, hmass, sub_self]
  have hterms : ∀ index ∈ Finset.univ, (0 : ℝ) ≤ (1 - design.weight index)
      * (1 - coParsevalPivotValue design index) := by
    intro index _
    have hcoweight : 0 < 1 - design.weight index := by
      linarith [fieldWeight_lt_one design hsize index]
    exact mul_nonneg hcoweight.le (by linarith [hle index])
  have hvanish := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hdeficit dropped (Finset.mem_univ _)
  have hcoweight : 0 < 1 - design.weight dropped := by
    linarith [fieldWeight_lt_one design hsize dropped]
  rcases mul_eq_zero.mp hvanish with hzero | hzero
  · exact absurd hzero (ne_of_gt hcoweight)
  · linarith

/-- **THE TOTAL TIE, field-generically.**  At corank one, if every erasure
dominates then every erasure sits at `λ_min = 1` EXACTLY: it dominates and it does
not dominate strictly.  This is the field-generic counterpart of the real
`Gtz.corankOne_isTie_exactlyTied` (`Gtz/Ties/TotalTieCorankOne.lean`), reached
without the leverage law and without a kernel vector. -/
theorem forall_erasure_exactlyTied_of_forall_fieldDominates {rank : ℕ} (hrank : 1 ≤ rank)
    (design : FieldWeightedDesign Scalar (rank + 1) rank)
    (hall : ∀ dropped : Fin (rank + 1), FieldDominates design (Finset.univ.erase dropped))
    (dropped : Fin (rank + 1)) :
    FieldDominates design (Finset.univ.erase dropped)
      ∧ ¬ (fieldSubsetSum design (Finset.univ.erase dropped) - 1).PosDef :=
  ⟨hall dropped, not_posDef_erasureGap_of_coParsevalPivot_eq_one design (by omega) dropped
    (forall_coParsevalPivotValue_eq_one_of_forall_fieldDominates hrank design hall dropped)⟩

/-! ## A4 in the Jensen chart

The brief's `p_c = |z_c|²/(1 - t_c)` needs only the DIAGONAL of `P = 1 - z zᴴ`,
and the diagonal of the chart is the weighted leverage.  So define `p_c` from the
leverage and prove the agreement with any kernel vector separately. -/

/-- **A4's quantity `p_c`**, defined without a kernel vector:
`jensenRatio c = (1 - t_c · leverage_c) / (1 - t_c)`. -/
noncomputable def jensenRatio {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (atomIndex : Fin size) : ℝ :=
  (1 - design.weight atomIndex * fieldLeverageOf (design.atom atomIndex))
    / (1 - design.weight atomIndex)

theorem jensenRatio_mul_coWeight {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size)
    (atomIndex : Fin size) :
    jensenRatio design atomIndex * (1 - design.weight atomIndex)
      = 1 - design.weight atomIndex * fieldLeverageOf (design.atom atomIndex) := by
  rw [jensenRatio, div_mul_cancel₀]
  exact sub_ne_zero_of_ne (Ne.symm (fieldWeight_lt_one design hsize atomIndex).ne)

/-- **A4(i), the normalisation.**  `Σ_c p_c (1 - t_c) = size - rank`, because the
weighted leverages sum to the rank.  At `size = rank + 1` the right side is one,
which is A4(i) as the brief states it. -/
theorem sum_jensenRatio_mul_coWeight {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size) :
    ∑ atomIndex, jensenRatio design atomIndex * (1 - design.weight atomIndex)
      = (size : ℝ) - (rank : ℝ) := by
  rw [Finset.sum_congr rfl fun atomIndex _ => jensenRatio_mul_coWeight design hsize atomIndex,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sum_weight_mul_fieldLeverage design]

/-- A4(i) at corank one, in the brief's exact shape
`Σ_c p_c − Σ_c t_c p_c = 1`. -/
theorem sum_jensenRatio_sub_weighted_corank_one {rank : ℕ} (hrank : 1 ≤ rank)
    (design : FieldWeightedDesign Scalar (rank + 1) rank) :
    (∑ atomIndex, jensenRatio design atomIndex)
        - ∑ atomIndex, design.weight atomIndex * jensenRatio design atomIndex = 1 := by
  have hsize : 2 ≤ rank + 1 := by omega
  have hnormalisation := sum_jensenRatio_mul_coWeight design hsize
  have hcast : ((rank + 1 : ℕ) : ℝ) - (rank : ℝ) = 1 := by push_cast; ring
  rw [hcast] at hnormalisation
  rw [← hnormalisation, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **A4(iii), the maximum is at least the weighted average.**  Field-blind, and
the only thing it uses about the weights is that they are nonnegative and sum to
one. -/
theorem exists_jensenRatio_ge_weightedAverage {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 0 < size) :
    ∃ argmax : Fin size,
      ∑ atomIndex, design.weight atomIndex * jensenRatio design atomIndex
        ≤ jensenRatio design argmax := by
  classical
  haveI : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp hsize
  obtain ⟨argmax, hargmax⟩ := Finite.exists_max (jensenRatio design)
  refine ⟨argmax, ?_⟩
  calc ∑ atomIndex, design.weight atomIndex * jensenRatio design atomIndex
      ≤ ∑ atomIndex, design.weight atomIndex * jensenRatio design argmax := by
        refine Finset.sum_le_sum fun atomIndex _ => ?_
        exact mul_le_mul_of_nonneg_left (hargmax atomIndex) (design.weight_pos atomIndex).le
    _ = jensenRatio design argmax := by
        rw [← Finset.sum_mul, design.weight_sum_one, one_mul]

/-- **A4's selector inequality.**  At corank one the complement of the argmax has
`Σ_{c ≠ argmax} p_c ≤ 1` — which is A4(ii)'s right-hand side.  Pure arithmetic
from A4(i) and A4(iii); no chart, no kernel vector. -/
theorem sum_erase_jensenRatio_le_one {rank : ℕ} (hrank : 1 ≤ rank)
    (design : FieldWeightedDesign Scalar (rank + 1) rank) :
    ∃ argmax : Fin (rank + 1),
      ∑ atomIndex ∈ Finset.univ.erase argmax, jensenRatio design atomIndex ≤ 1 := by
  classical
  obtain ⟨argmax, hargmax⟩ :=
    exists_jensenRatio_ge_weightedAverage design (Nat.succ_pos rank)
  refine ⟨argmax, ?_⟩
  have hsplit : (∑ atomIndex ∈ Finset.univ.erase argmax, jensenRatio design atomIndex)
      + jensenRatio design argmax = ∑ atomIndex, jensenRatio design atomIndex :=
    Finset.sum_erase_add Finset.univ _ (Finset.mem_univ argmax)
  have hnormalisation := sum_jensenRatio_sub_weighted_corank_one hrank design
  linarith [hsplit, hnormalisation, hargmax]

/-! ### A4(iv): the equality case IS the repository's corank-one leverage law -/

/-- **A4(iv).**  `p_c = 1/rank` exactly when
`rank · t_c · leverage_c = (rank − 1) + t_c`.  The right-hand side is VERBATIM
the relation in `Gtz.isTie_iff_leverage_identity`; the identification with
`Gtz.IsTie` itself is `Gtz/Complex/SizeAxis.lean`. -/
theorem jensenRatio_eq_inv_rank_iff_leverageIdentity {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) (hsize : 2 ≤ size) (hrank : 1 ≤ rank)
    (atomIndex : Fin size) :
    jensenRatio design atomIndex = 1 / (rank : ℝ)
      ↔ (rank : ℝ) * design.weight atomIndex * fieldLeverageOf (design.atom atomIndex)
          = ((rank : ℝ) - 1) + design.weight atomIndex := by
  have hcoweight : (0 : ℝ) < 1 - design.weight atomIndex := by
    linarith [fieldWeight_lt_one design hsize atomIndex]
  have hrankPos : (0 : ℝ) < (rank : ℝ) := by
    have : (1 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
    linarith
  rw [jensenRatio, div_eq_div_iff hcoweight.ne' hrankPos.ne']
  constructor
  · intro hcross; nlinarith [hcross]
  · intro hlaw; nlinarith [hlaw]

/-- All the `p_c` equal forces the common value `1/rank` at corank one: the
normalisation `Σ_c p_c (1 - t_c) = 1` and `Σ_c (1 - t_c) = rank` pin it. -/
theorem jensenRatio_eq_inv_rank_of_forall_eq {rank : ℕ} (hrank : 1 ≤ rank)
    (design : FieldWeightedDesign Scalar (rank + 1) rank)
    (hconstant : ∀ leftIndex rightIndex : Fin (rank + 1),
      jensenRatio design leftIndex = jensenRatio design rightIndex)
    (atomIndex : Fin (rank + 1)) : jensenRatio design atomIndex = 1 / (rank : ℝ) := by
  classical
  have hsize : 2 ≤ rank + 1 := by omega
  have hrankPos : (0 : ℝ) < (rank : ℝ) := by
    have : (1 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
    linarith
  have hnormalisation := sum_jensenRatio_mul_coWeight design hsize
  have hcast : ((rank + 1 : ℕ) : ℝ) - (rank : ℝ) = 1 := by push_cast; ring
  rw [hcast] at hnormalisation
  have hmass := sum_coWeight (Scalar := Scalar) design
  have hmassCast : ((rank + 1 : ℕ) : ℝ) - 1 = (rank : ℝ) := by push_cast; ring
  rw [hmassCast] at hmass
  have hpull : ∑ index, jensenRatio design index * (1 - design.weight index)
      = jensenRatio design atomIndex * ∑ index, (1 - design.weight index) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun index _ => by rw [hconstant atomIndex index]
  rw [hpull, hmass] at hnormalisation
  field_simp at hnormalisation ⊢
  linarith [hnormalisation]

/-! ### The kernel-vector bridge: `p_c` IS A4's `|z_c|²/(1 - t_c)` -/

/-- **The bridge to A4's own definition.**  If `z` realises the corank-one
projector identity `projectionChart = 1 - z zᴴ`, then `|z_c|² = 1 - t_c·leverage_c`
and hence `jensenRatio c = |z_c|²/(1 - t_c)` — the brief's `p_c` exactly.  Only
the DIAGONAL of the identity is used, which is why `jensenRatio` needs no `z` to
be defined. -/
theorem kernelNormSq_eq_one_sub_weighted_leverage {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {kernelVector : Fin size → Scalar}
    (hprojector : projectionChart design = 1 - fieldAtom kernelVector)
    (atomIndex : Fin size) :
    ‖kernelVector atomIndex‖ ^ 2
      = 1 - design.weight atomIndex * fieldLeverageOf (design.atom atomIndex) := by
  have hdiagonal := congrFun (congrFun hprojector atomIndex) atomIndex
  rw [projectionChart_diagonal, Matrix.sub_apply, Matrix.one_apply_eq, fieldAtom_apply,
    RCLike.star_def, RCLike.mul_conj] at hdiagonal
  have hreal : design.weight atomIndex * fieldLeverageOf (design.atom atomIndex)
      = 1 - ‖kernelVector atomIndex‖ ^ 2 := by
    have hcast : ((design.weight atomIndex * fieldLeverageOf (design.atom atomIndex) : ℝ) : Scalar)
        = ((1 - ‖kernelVector atomIndex‖ ^ 2 : ℝ) : Scalar) := by
      rw [hdiagonal, RCLike.ofReal_sub, RCLike.ofReal_one, RCLike.ofReal_pow]
    exact_mod_cast hcast
  rw [hreal]; ring

theorem jensenRatio_eq_kernelNormSq_div_coWeight {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {kernelVector : Fin size → Scalar}
    (hprojector : projectionChart design = 1 - fieldAtom kernelVector)
    (atomIndex : Fin size) :
    jensenRatio design atomIndex
      = ‖kernelVector atomIndex‖ ^ 2 / (1 - design.weight atomIndex) := by
  rw [jensenRatio, kernelNormSq_eq_one_sub_weighted_leverage design hprojector atomIndex]

/-! ### A4(ii) in the Jensen chart: SHIPPED AS A HYPOTHESIS, gap named

The Jensen form of the domination criterion needs the projector identity
`1 - projectionChart = z zᴴ` for a unit `z` spanning the kernel — uniqueness of
rank-one Hermitian idempotents.  Mathlib v4.32 has no such lemma; over ℝ the
repository builds it by hand (Householder, `Gtz/Ties/CorankOneTieExistence.lean`).
The statement below therefore takes the identity as an argument.  The corank-one
theorem `fieldGtzWeighted_corank_one` does NOT depend on it. -/

/-- The Jensen-chart erasure criterion, as a named proposition so the gap is
visible rather than buried: `Dominates (univ.erase c₀) ↔ Σ_{c ≠ c₀} p_c ≤ 1`.

Indexed by the RANK alone, so the designs it quantifies over are exactly the
corank-one ones.  That restriction is not cosmetic: stated over an arbitrary size
the proposition is refutable, and the refutation is
`not_jensenErasureCriterion_at_singleton` below. -/
def JensenErasureCriterion (Scalar : Type*) [RCLike Scalar] (rank : ℕ) : Prop :=
  ∀ (design : FieldWeightedDesign Scalar (rank + 1) rank) (dropped : Fin (rank + 1)),
    FieldDominates design (Finset.univ.erase dropped)
      ↔ ∑ atomIndex ∈ Finset.univ.erase dropped, jensenRatio design atomIndex ≤ 1

/-- At `size = rank = 1` the erasure of the single atom is the EMPTY subset, whose
atom sum is zero, so the erasure gap is the `1 × 1` matrix `-1`. -/
theorem fieldSubsetSum_erase_degenerateSingleton :
    fieldSubsetSum (degenerateSingletonDesign (Scalar := Scalar)) (Finset.univ.erase 0) - 1
      = -1 := by
  classical
  have hempty : Finset.univ.erase (0 : Fin 1) = (∅ : Finset (Fin 1)) := by
    apply Finset.eq_empty_of_forall_notMem
    intro candidate hcandidate
    exact (Finset.mem_erase.mp hcandidate).1 (Subsingleton.elim candidate 0)
  rw [fieldSubsetSum, hempty, Finset.sum_empty, zero_sub]

/-- The Jensen sum over that empty erasure is zero, so the criterion's right-hand
side holds. -/
theorem sum_erase_jensenRatio_degenerateSingleton :
    ∑ atomIndex ∈ Finset.univ.erase (0 : Fin 1),
      jensenRatio (degenerateSingletonDesign (Scalar := Scalar)) atomIndex = 0 := by
  classical
  have hempty : Finset.univ.erase (0 : Fin 1) = (∅ : Finset (Fin 1)) := by
    apply Finset.eq_empty_of_forall_notMem
    intro candidate hcandidate
    exact (Finset.mem_erase.mp hcandidate).1 (Subsingleton.elim candidate 0)
  rw [hempty, Finset.sum_empty]

/-- **THE SHAPE OF `JensenErasureCriterion` IS LOAD-BEARING.**  Stated at an
arbitrary size the criterion is FALSE, and `size = rank = 1` is the witness: the
Jensen side is an empty sum below one while the domination side asks `-1` to be
positive semidefinite.  Shipped as a theorem so nobody can widen the indexing back
out by accident. -/
theorem not_jensenErasureCriterion_at_singleton :
    ¬ ∀ (design : FieldWeightedDesign Scalar 1 1) (dropped : Fin 1),
        FieldDominates design (Finset.univ.erase dropped)
          ↔ ∑ atomIndex ∈ Finset.univ.erase dropped, jensenRatio design atomIndex ≤ 1 := by
  intro hcriterion
  have hdominates : FieldDominates (degenerateSingletonDesign (Scalar := Scalar))
      (Finset.univ.erase 0) :=
    (hcriterion degenerateSingletonDesign 0).mpr
      (by rw [sum_erase_jensenRatio_degenerateSingleton]; norm_num)
  rw [FieldDominates, fieldSubsetSum_erase_degenerateSingleton] at hdominates
  have hdiagonal : (0 : Scalar) ≤ (-1 : Matrix (Fin 1) (Fin 1) Scalar) 0 0 :=
    hdominates.diag_nonneg (i := 0)
  rw [Matrix.neg_apply, Matrix.one_apply_eq] at hdiagonal
  exact absurd hdiagonal (by norm_num)

/-- **What A4(ii) is missing, stated exactly.**  Given a unit kernel vector
realising the corank-one projector identity, A4's `p_c` is `|z_c|²/(1 - t_c)` and
the Jensen sum `Σ_{c ≠ c₀} p_c` is the rank-one Schur quantity of `z_C` against
`diag(1 - t)_C`.  The remaining step — that this Schur quantity being at most one
is equivalent to domination — is `Gtz.posSemidef_sub_fieldAtom_iff` applied to the
chart block, and it needs the projector identity, not just its diagonal.  Nothing
here asserts the identity holds; `Gtz.exists_isTie_of_weights`
(`Gtz/Ties/CorankOneTieExistence.lean`) is the real-side evidence that
constructing such a `z` is roughly a 380-line Householder argument. -/
theorem jensenSum_eq_kernel_schur_quantity {size rank : ℕ}
    (design : FieldWeightedDesign Scalar size rank) {kernelVector : Fin size → Scalar}
    (hprojector : projectionChart design = 1 - fieldAtom kernelVector)
    (dropped : Fin size) :
    ∑ atomIndex ∈ Finset.univ.erase dropped, jensenRatio design atomIndex
      = ∑ atomIndex ∈ Finset.univ.erase dropped,
          ‖kernelVector atomIndex‖ ^ 2 / (1 - design.weight atomIndex) :=
  Finset.sum_congr rfl fun atomIndex _ =>
    jensenRatio_eq_kernelNormSq_div_coWeight design hprojector atomIndex

/-! ## A6 (corank two): the two cheap bricks, and the reduction NAMED not proved

A6 says corank two reduces to rank two.  Two of its ingredients are pure
`Finset` algebra and are proved here.  The reduction itself is NOT proved, and
this section records exactly why that is the right call rather than a shortfall.

**WHY A6 BUYS NOTHING OVER ℂ.**  Over ℂ the size `rank + 2` is already REFUTED at
every rank at least two — `Gtz.not_complexGtzWeighted_of_rank_add_two_le_size`,
consumed by `Gtz.complexGtzWeighted_iff_size_le_rank_add_one` in
`Gtz/Complex/SizeAxis.lean`.  A6's reduction is field-blind, but its INGREDIENT
(rank two) is a real theorem that is false over ℂ, so instantiating A6 at ℂ
yields a true implication with a false hypothesis.  The complex size axis is
already complete without it.

**WHY A6 BUYS NOTHING OVER ℝ EITHER.**  `Gtz.gtzWeighted_corank_two`
(`Gtz/Reduction/Reductions.lean`) is already shipped, rank-generically, riding
`Gtz.weighted_naimark_duality` and `Gtz.gtz_rank_two`.  A generic A6 would be a
third proof of a shipped real theorem with no new instance.

**THE RESCALING, recorded so the trap is visible.**  A6's own normalisation is
`Σ_c (1 - t_c) w_c w_cᴴ = 1₂`, whereas `Gtz.gtz_rank_two` consumes
`Σ_c s_c h_c h_cᴴ = 1₂`.  These are DIFFERENT, and the bridge is

    T := Σ_c t_c w_c w_cᴴ,    h_c := T^{-1/2} w_c,    s_c := t_c  (WEIGHTS UNCHANGED),

so that `Σ_c t_c h_c h_cᴴ = T^{-1/2} T T^{-1/2} = 1₂` exactly and
`h_a h_aᴴ + h_b h_bᴴ ⪰ 1₂ ↔ w_a w_aᴴ + w_b w_bᴴ ⪰ T`, which is A6's criterion.
`T` is always invertible because a null vector of `T` is a null vector of
`Σ_c (1 - t_c) w_c w_cᴴ = 1₂`.  Setting `s_c := 1 - t_c`, or whitening by `1`
instead of by `T`, produces a FALSE lemma; the `(1 - t_c)` normalisation is used
only to derive the flip and is not what feeds rank two. -/

/-- The complement of two distinct indices in `Fin (rank + 2)` has exactly `rank`
elements.  `Finset.erase` twice; no order embedding, no `Fin.succAbove`. -/
theorem card_erase_pair {rank : ℕ} (dropFirst dropSecond : Fin (rank + 2))
    (hdistinct : dropFirst ≠ dropSecond) :
    ((Finset.univ.erase dropFirst).erase dropSecond).card = rank := by
  classical
  rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨Ne.symm hdistinct, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ dropFirst), Finset.card_univ, Fintype.card_fin]
  omega

/-- **A6's flip engine in the atom chart**: the excess of erasing a PAIR is the
co-Parseval operator minus the two dropped atoms.  This is the corank-two twin of
`erasureGap_eq`, and it is the only part of A6 that is cheap. -/
theorem pairErasureGap_eq {size rank : ℕ} (design : FieldWeightedDesign Scalar size rank)
    (dropFirst dropSecond : Fin size) (hdistinct : dropFirst ≠ dropSecond) :
    fieldSubsetSum design ((Finset.univ.erase dropFirst).erase dropSecond) - 1
      = coParsevalOperator design - fieldAtom (design.atom dropSecond)
          - fieldAtom (design.atom dropFirst) := by
  classical
  have hsplit : (fieldSubsetSum design ((Finset.univ.erase dropFirst).erase dropSecond)
        + fieldAtom (design.atom dropSecond)) + fieldAtom (design.atom dropFirst)
      = fieldSubsetSum design Finset.univ := by
    rw [fieldSubsetSum, fieldSubsetSum]
    rw [Finset.sum_erase_add _ _
        (Finset.mem_erase.mpr ⟨Ne.symm hdistinct, Finset.mem_univ _⟩),
      Finset.sum_erase_add _ _ (Finset.mem_univ dropFirst)]
  rw [coParsevalOperator_eq_universalGap, ← hsplit]
  abel

/-- **A6, NAMED — and open only in the generic `Scalar`.**  The corank-two
reduction: rank-two weighted GTZ at every size implies corank-two weighted GTZ at
every rank at least two.

The honest label: BOTH instantiations that this campaign cares about are
DISCHARGED, in `Gtz/Complex/SizeAxis.lean`, and neither needs the `T^{-1/2}`
whitening — `fieldCorankTwoReducesToRankTwo_real` reads the conclusion off the
shipped `Gtz.gtzWeighted_corank_two` through the transport, and
`fieldCorankTwoReducesToRankTwo_complex` is vacuous because its hypothesis fails
(rank two is refuted over ℂ at size four).  What remains genuinely open is only the
uniform statement over an arbitrary `RCLike` field, and that is the statement whose
proof would need the whitening recorded above — the one step where an incorrect
rescaling produces a false lemma. -/
def FieldCorankTwoReducesToRankTwo (Scalar : Type*) [RCLike Scalar] : Prop :=
  (∀ size : ℕ, FieldGtzWeighted Scalar size 2) →
    ∀ rank : ℕ, 2 ≤ rank → FieldGtzWeighted Scalar (rank + 2) rank

/-! ## The two instantiations of the positive half -/

/-- A5 at ℂ. -/
theorem complexFieldGtzWeighted_square (rank : ℕ) : FieldGtzWeighted ℂ rank rank :=
  fieldGtzWeighted_square rank

/-- A5 at ℝ. -/
theorem realFieldGtzWeighted_square (rank : ℕ) : FieldGtzWeighted ℝ rank rank :=
  fieldGtzWeighted_square rank

/-- A4(iii) at ℂ — the genuinely new rung. -/
theorem complexFieldGtzWeighted_corank_one (rank : ℕ) (hrank : 1 ≤ rank) :
    FieldGtzWeighted ℂ (rank + 1) rank :=
  fieldGtzWeighted_corank_one rank hrank

/-- A4(iii) at ℝ — a second, Naimark-free proof of the shipped
`Gtz.gtzWeighted_corank_one`. -/
theorem realFieldGtzWeighted_corank_one (rank : ℕ) (hrank : 1 ≤ rank) :
    FieldGtzWeighted ℝ (rank + 1) rank :=
  fieldGtzWeighted_corank_one rank hrank

end Gtz
