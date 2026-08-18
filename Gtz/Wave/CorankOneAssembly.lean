/-
# The corank-one assembly: the resolve identity, the full-moment floor, the
# outside cascade, and the wedge budget

Four bricks that couple the exchange system of `Gtz.Wave.CorankOneExchange` to
the size-six structure.  Everything here is unconditional over its stated
hypotheses; nothing is a reformulation of the hinge.

## The resolve identity

`Gtz.dominator_resolves_nullDir`: at a corank-one weak dominator the three
selected atoms RESOLVE the null direction exactly:

  `sum over e in C of (g_e . u) * g_e = u`.

One identity carries two facts at once: the kernel mass of the dominator is
exactly `|u|^2` (the scalar half is the landed
`Gtz.gapForm_eq_zero_iff_sum_sq`), and the kernel-weighted plane components
cancel (project on the plane).  A weak dominator sits at kernel mass exactly
its null length — the tight direction is where its mass budget closes with no
room.

## The full-moment floor

`Gtz.fullMoment_sub_one_posDef`: at every design with a corank-one weak
dominator, the UNWEIGHTED full moment `N = sum over all c of g_c g_c^T` is
strictly above the identity.  The gap of the dominator covers every direction
off the null line, and the complement covers the null line, because a null
direction always touches the complement
(`Gtz.exists_compl_dotProduct_ne_zero_of_nullDirection`).

## The outside cascade — the size-six refusal

At `(6,3)` the complement of the dominator is itself a triple, and the tie
refuses it.  `Gtz.outside_refusal_cascade` prices that refusal through three
rank-one downdates of `N - 1`: one of the three inside atoms reads at least
one in the cascade metric.  This is the constraint with no analogue at
`(5,3)`, where the complement of a triple is a pair and no refusal exists.

## The wedge budget

`Gtz.wedge_budget`: over every `(m,3)` design,

  `sum over c, d of t_c t_d |g_c x g_d|^2 = 6`,

by Cauchy-Binet on Parseval: the total weighted wedge mass is
`e_2(I_3) * 2 = 6` in the ordered double count.  The refusals of the exchange
system bound wedge components from below; this identity caps their weighted
total from above.  `Gtz.exists_cross_eq_zero_of_hasParallelPair` records the
bridge: a parallel pair is a vanishing wedge.
-/
import Gtz.Wave.CorankOneExchange
import Gtz.LinAlg.ProjectionForm
import Gtz.Wave.TieStratumClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The resolve identity -/

/-- **THE DOMINATOR RESOLVES ITS NULL DIRECTION.**  At a weakly dominating
subset whose gap kills a direction, the selected atoms reproduce that
direction exactly through their readings. -/
theorem dominator_resolves_nullDir (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    ∑ e ∈ C, (D.atom e ⬝ᵥ nullDir) • D.atom e = nullDir := by
  have hgapNull : (subsetSum D C - 1) *ᵥ nullDir = 0 :=
    mulVec_eq_zero_of_form_eq_zero hdominates
      (transpose_subsetSum_sub_one D C) hnull
  have hfixed : subsetSum D C *ᵥ nullDir = nullDir := by
    have hexpand : (subsetSum D C - 1) *ᵥ nullDir
        = subsetSum D C *ᵥ nullDir - nullDir := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hexpand] at hgapNull
    exact sub_eq_zero.mp hgapNull
  calc ∑ e ∈ C, (D.atom e ⬝ᵥ nullDir) • D.atom e
      = subsetSum D C *ᵥ nullDir := by
        rw [subsetSum, Matrix.sum_mulVec]
        exact Finset.sum_congr rfl fun e _ => by
          rw [atomMatrix, vecMulVec_mulVec_eq]
    _ = nullDir := hfixed

/-! ## 2. The full-moment floor -/

/-- The full moment splits across a subset and its complement. -/
theorem subsetSum_univ_split (D : WeightedDesign m 3) (C : Finset (Fin m)) :
    subsetSum D (Finset.univ : Finset (Fin m))
      = subsetSum D C + subsetSum D Cᶜ := by
  rw [subsetSum, subsetSum, subsetSum,
    ← Finset.sum_add_sum_compl C fun c => atomMatrix (D.atom c)]

/-- **THE FULL-MOMENT FLOOR.**  A corank-one weak dominator forces the
unweighted full moment strictly above the identity: the gap covers every
direction off the null line, and the complement covers the null line. -/
theorem fullMoment_sub_one_posDef (D : WeightedDesign m 3) (hsize : 2 ≤ m)
    {C : Finset (Fin m)} (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D C nullDir) :
    (subsetSum D (Finset.univ : Finset (Fin m)) - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _),
      fun probe hprobe => ?_⟩
  rw [star_trivial]
  have hsplit : subsetSum D (Finset.univ : Finset (Fin m)) - 1
      = (subsetSum D C - 1) + subsetSum D Cᶜ := by
    rw [subsetSum_univ_split D C]
    abel
  rw [hsplit, Matrix.add_mulVec, dotProduct_add]
  have hgap : 0 ≤ probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    rwa [star_trivial] at h
  have hout : 0 ≤ probe ⬝ᵥ (subsetSum D Cᶜ *ᵥ probe) := by
    rw [subsetSum_form_eq_sum_sq]
    exact Finset.sum_nonneg fun d _ => sq_nonneg _
  rcases lt_or_eq_of_le hgap with hgapPos | hgapZero
  · linarith
  rcases lt_or_eq_of_le hout with houtPos | houtZero
  · linarith
  exfalso
  obtain ⟨scale, hscale⟩ := hline.2.2 probe hgapZero.symm
  obtain ⟨witness, hwitnessMem, hwitnessRead⟩ :=
    exists_compl_dotProduct_ne_zero_of_nullDirection D hsize C hline.1
      hline.2.1
  have houtSum : ∑ d ∈ Cᶜ, (D.atom d ⬝ᵥ probe) ^ 2 = 0 := by
    rw [← subsetSum_form_eq_sum_sq, ← houtZero]
  have hterm : (D.atom witness ⬝ᵥ probe) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun d _ => sq_nonneg _).mp houtSum
      witness hwitnessMem
  have hreadZero : D.atom witness ⬝ᵥ probe = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp hterm
  rw [hscale, dotProduct_smul, smul_eq_mul] at hreadZero
  rcases mul_eq_zero.mp hreadZero with hscaleZero | hnullRead
  · exact hprobe (by rw [hscale, hscaleZero, zero_smul])
  · exact hwitnessRead hnullRead

/-! ## 3. The outside cascade at size six -/

/-- **THE OUTSIDE CASCADE.**  At a `(6,3)` tie the complement of a corank-one
weak dominator is a triple, and the tie refuses it.  The refusal cascades
through three rank-one downdates of the full-moment floor `N - 1`: for every
enumeration of the dominator, one of its three atoms reads at least one in
its cascade metric.

This is the size-six constraint.  At `(5,3)` the complement of a triple is a
pair, no third refusal exists, and the diamond survives — as it must. -/
theorem outside_refusal_cascade (D : WeightedDesign 6 3) (htie : IsTie D)
    {C : Finset (Fin 6)} (hcard : C.card = 3) (hdominates : Dominates D C)
    {nullDir : Fin 3 → ℝ} (hline : GapNullLine D C nullDir)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hC : C = {x, y, z}) :
    1 ≤ D.atom x ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom x)
    ∨ 1 ≤ D.atom y ⬝ᵥ ((subsetSum D Finset.univ - 1
        - Matrix.vecMulVec (D.atom x) (D.atom x))⁻¹ *ᵥ D.atom y)
    ∨ 1 ≤ D.atom z ⬝ᵥ ((subsetSum D Finset.univ - 1
        - Matrix.vecMulVec (D.atom x) (D.atom x)
        - Matrix.vecMulVec (D.atom y) (D.atom y))⁻¹ *ᵥ D.atom z) := by
  have hfull : (subsetSum D (Finset.univ : Finset (Fin 6)) - 1).PosDef :=
    fullMoment_sub_one_posDef D (by norm_num) hdominates hline
  by_cases hfirst :
      1 ≤ D.atom x ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom x)
  · exact Or.inl hfirst
  push Not at hfirst
  have hstepOne : (subsetSum D Finset.univ - 1
      - Matrix.vecMulVec (D.atom x) (D.atom x)).PosDef :=
    (posDef_sub_vecMulVec_iff _ hfull (D.atom x)).mpr hfirst
  by_cases hsecond :
      1 ≤ D.atom y ⬝ᵥ ((subsetSum D Finset.univ - 1
        - Matrix.vecMulVec (D.atom x) (D.atom x))⁻¹ *ᵥ D.atom y)
  · exact Or.inr (Or.inl hsecond)
  push Not at hsecond
  have hstepTwo : (subsetSum D Finset.univ - 1
      - Matrix.vecMulVec (D.atom x) (D.atom x)
      - Matrix.vecMulVec (D.atom y) (D.atom y)).PosDef :=
    (posDef_sub_vecMulVec_iff _ hstepOne (D.atom y)).mpr hsecond
  refine Or.inr (Or.inr ?_)
  have hrefusal := htie.2 Cᶜ (card_compl_eq_three_of_card_eq_three C hcard)
  have hsubsetC : subsetSum D C
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [hC, subsetSum]
    rw [Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  have hout : subsetSum D Cᶜ - 1
      = subsetSum D Finset.univ - 1
        - Matrix.vecMulVec (D.atom x) (D.atom x)
        - Matrix.vecMulVec (D.atom y) (D.atom y)
        - Matrix.vecMulVec (D.atom z) (D.atom z) := by
    have hsplit := subsetSum_univ_split D C
    have hxatom : Matrix.vecMulVec (D.atom x) (D.atom x)
        = atomMatrix (D.atom x) := rfl
    have hyatom : Matrix.vecMulVec (D.atom y) (D.atom y)
        = atomMatrix (D.atom y) := rfl
    have hzatom : Matrix.vecMulVec (D.atom z) (D.atom z)
        = atomMatrix (D.atom z) := rfl
    rw [hxatom, hyatom, hzatom]
    have : subsetSum D Cᶜ = subsetSum D Finset.univ - subsetSum D C := by
      rw [hsplit]; abel
    rw [this, hsubsetC]
    abel
  rw [hout] at hrefusal
  by_contra hthird
  push Not at hthird
  exact hrefusal ((posDef_sub_vecMulVec_iff _ hstepTwo (D.atom z)).mpr hthird)

/-! ## 4. The wedge budget -/

/-- **THE WEDGE BUDGET.**  Over every `(m,3)` design the weighted total of the
squared wedges is exactly six: Cauchy-Binet against Parseval, in the ordered
double count.  Every refusal of the exchange system bounds one wedge from
below; this identity is the cap on their weighted total. -/
theorem wedge_budget (D : WeightedDesign m 3) :
    ∑ c, ∑ d, D.weight c * D.weight d
      * (crossProduct (D.atom c) (D.atom d)
          ⬝ᵥ crossProduct (D.atom c) (D.atom d)) = 6 := by
  have hpoint : ∀ c d : Fin m,
      crossProduct (D.atom c) (D.atom d) ⬝ᵥ crossProduct (D.atom c) (D.atom d)
        = leverageOf (D.atom c) * leverageOf (D.atom d)
          - (D.atom c ⬝ᵥ D.atom d) ^ 2 := by
    intro c d
    rw [cross_dot_cross, ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct,
      dotProduct_comm (D.atom d) (D.atom c)]
    ring
  have hexpand : ∑ c, ∑ d, D.weight c * D.weight d
      * (crossProduct (D.atom c) (D.atom d)
          ⬝ᵥ crossProduct (D.atom c) (D.atom d))
      = (∑ c, ∑ d, (D.weight c * leverageOf (D.atom c))
            * (D.weight d * leverageOf (D.atom d)))
        - ∑ c, ∑ d, D.weight c * D.weight d * (D.atom c ⬝ᵥ D.atom d) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hpoint c d]
    ring
  have hproduct : ∑ c, ∑ d, (D.weight c * leverageOf (D.atom c))
      * (D.weight d * leverageOf (D.atom d))
      = (∑ c, D.weight c * leverageOf (D.atom c))
        * (∑ d, D.weight d * leverageOf (D.atom d)) := by
    rw [Finset.sum_mul_sum]
  have hlev := sum_weight_mul_leverage D
  have hpair := sum_weight_mul_pairing_sq D
  rw [hexpand, hproduct, hlev, hpair]
  norm_num

/-- **A parallel pair is a vanishing wedge.**  The bridge from the hinge
conclusion to the wedge vocabulary of the budget and the refusals. -/
theorem exists_cross_eq_zero_of_hasParallelPair (D : WeightedDesign m 3)
    (hpair : HasParallelPair D) :
    ∃ c d : Fin m, c ≠ d
      ∧ crossProduct (D.atom c) (D.atom d) = 0 := by
  obtain ⟨keptLabel, dropLabel, ratio, hne, heq⟩ := hpair
  refine ⟨keptLabel, dropLabel, hne, ?_⟩
  rw [heq, map_smul, cross_self, smul_zero]

end Gtz
