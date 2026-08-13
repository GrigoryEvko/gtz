/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.DegenerateHingeArm
import Gtz.Design.LeverageBound
import Gtz.Reduction.Reductions
import Gtz.Uniform.WindowInductionStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The polar cover: the predecessor rank makes the hyperplane cover STRICT

The general-rank hinge asks a tie for a card-`rank` subset that strictly
dominates the identity. The rank-down dispatch
`Gtz.exists_subspace_dominating_subset` answers only WEAKLY, and the named
obstruction of the degenerate arm was that the upgrade from a weak cover to a
strict one is `Gtz.GtzWeighted`-strictness one rank down.

This module kills that obstruction. The upgrade is free, and the mechanism is
the MASS OF THE POLE.

## The polar frame

Read the hyperplane against the LONG ATOM itself, not against the branch's
probe. Every design carries an atom of squared length at least `rank`
(`Gtz.exists_long_atom`, off the shipped leverage identity). Restrict the design
to that atom's orthogonal hyperplane: the long atom's own reading is ZERO there,
thus the remaining labels already resolve the identity of the hyperplane while
their weights add up to `1 - weight pole < 1`. Renormalizing scales every atom
DOWN, thus the rank-down dispatch answers with a subset that covers the
hyperplane with an explicit margin (`Gtz.exists_polarStrictCover`). No matrix
square root, no whitening, no Gram-Schmidt recursion: the deficit is a scalar.

## What is left, named and measured

The Schur producer needs the strict cover AND a bound on the COUPLING between
the pole direction and the hyperplane. `Gtz.posDef_insert_of_polarCover` proves
that a card-`rank` subset strictly dominates as soon as the covering set is
almost orthogonal to the pole, and `Gtz.PolarTiltSelection` is exactly that
residual. `Gtz.polarTilt_budget_lt_leverage` measures its budget: the tilt must
stay below the pole's own leverage, whatever the design.

## The consolidation

`Gtz.PolarTiltSelection` plus `Gtz.GtzWeightedAll (rank - 1)` closes
`Gtz.HingeHoldsAtSize` at every size and every rank of at least two, thus it
closes ALL THREE arms of `Gtz.design_stress_trichotomy`, the partial-support
sub-arm, `Gtz.DegenerateHyperplaneCover`, and both registry hinge obligations.
Its tie-free form also closes `Gtz.BalancedStratumSelectionAtRank` and
`Gtz.PartialSupportSelectionAtRank`. Six named residuals become one.
-/

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## Part 1: the Householder reflection is an orthogonal involution

`Gtz.reflect` is already known to be self-adjoint and isometric with no
hypothesis on the axis. Three more laws make it a linear involution, and those
three turn the Householder frame of `Gtz.hyperplaneFrameExists` from an
orthonormal FAMILY into an orthonormal BASIS of the hyperplane. -/

/-- The reflection fixes the origin. -/
theorem reflect_zero (axis : Fin rank → ℝ) : reflect axis (0 : Fin rank → ℝ) = 0 := by
  rw [reflect, dotProduct_zero, mul_zero, zero_div, zero_smul, sub_zero]

/-- The reflection is additive. -/
theorem reflect_add (axis leftProbe rightProbe : Fin rank → ℝ) :
    reflect axis (leftProbe + rightProbe) = reflect axis leftProbe + reflect axis rightProbe := by
  simp only [reflect, dotProduct_add]
  rw [mul_add, add_div, add_smul]
  abel

/-- The reflection is homogeneous. -/
theorem reflect_smul (axis : Fin rank → ℝ) (factor : ℝ) (probe : Fin rank → ℝ) :
    reflect axis (factor • probe) = factor • reflect axis probe := by
  simp only [reflect, dotProduct_smul, smul_eq_mul, smul_sub, smul_smul]
  congr 2
  ring

/-- The axis reverses under its own reflection, read as a pairing. -/
theorem dotProduct_axis_reflect (axis probe : Fin rank → ℝ)
    (haxis : axis ⬝ᵥ axis ≠ 0) : axis ⬝ᵥ reflect axis probe = -(axis ⬝ᵥ probe) := by
  rw [reflect, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  field_simp
  ring

/-- **THE REFLECTION IS AN INVOLUTION.**  No hypothesis on the axis: at a zero
axis it is the identity, and otherwise the axis pairing reverses sign, thus the
second reflection undoes the first. -/
theorem reflect_reflect (axis probe : Fin rank → ℝ) :
    reflect axis (reflect axis probe) = probe := by
  by_cases haxis : axis ⬝ᵥ axis = 0
  · rw [eq_zero_of_selfDotProduct_eq_zero haxis, reflect_zero_axis, reflect_zero_axis]
  · have hexpand : reflect axis (reflect axis probe)
        = reflect axis probe - (2 * (axis ⬝ᵥ reflect axis probe) / (axis ⬝ᵥ axis)) • axis := rfl
    have hsign : (2 * -(axis ⬝ᵥ probe) / (axis ⬝ᵥ axis))
        = -(2 * (axis ⬝ᵥ probe) / (axis ⬝ᵥ axis)) := by ring
    rw [hexpand, dotProduct_axis_reflect axis probe haxis, hsign, neg_smul, reflect]
    abel

/-- **A VECTOR IS ZERO IF IT MISSES THE WHOLE REFLECTED BASIS.**  The reflection
carries the standard basis to an orthonormal basis, thus its readings are the
coordinates of the reflected vector. -/
theorem eq_zero_of_dotProduct_reflect_basisVec (axis probe : Fin rank → ℝ)
    (hall : ∀ coord : Fin rank, probe ⬝ᵥ reflect axis (basisVec coord) = 0) : probe = 0 := by
  have hreflectZero : reflect axis probe = 0 := by
    funext coord
    have hcoord : reflect axis probe coord = basisVec coord ⬝ᵥ reflect axis probe :=
      (basisVec_dotProduct coord _).symm
    rw [Pi.zero_apply, hcoord, ← dotProduct_reflect_left, dotProduct_comm]
    exact hall coord
  have happly := congrArg (reflect axis) hreflectZero
  rwa [reflect_reflect, reflect_zero] at happly

/-! ### The named Householder frame

`Gtz.hyperplaneFrameExists` builds the frame anonymously. Naming it makes the
spanning law statable, and the spanning law is what a Schur producer needs: the
cover must hold at EVERY probe of the hyperplane, not only at the frame's
coordinate combinations. -/

/-- The orthonormal frame of the hyperplane orthogonal to a unit normal: the
Householder image of the standard basis vectors that miss the pivot. -/
noncomputable def householderFrame (hpos : 0 < rank) (unitNormal : Fin rank → ℝ) :
    Fin (rank - 1) → Fin rank → ℝ :=
  fun index => reflect (householderAxis (pivotIndex hpos) unitNormal) (basisVec (shiftIndex index))

/-- The frame is orthonormal, because the reflection is an isometry. -/
theorem householderFrame_orthonormal (hpos : 0 < rank) (unitNormal : Fin rank → ℝ)
    (leftIndex rightIndex : Fin (rank - 1)) :
    householderFrame hpos unitNormal leftIndex ⬝ᵥ householderFrame hpos unitNormal rightIndex
      = if leftIndex = rightIndex then 1 else 0 := by
  simp only [householderFrame]
  rw [dotProduct_reflect_reflect, basisVec_dotProduct_basisVec]
  by_cases hindex : leftIndex = rightIndex
  · rw [if_pos hindex, if_pos (by rw [hindex])]
  · rw [if_neg hindex,
      if_neg fun hshift => hindex (shiftIndex_injective leftIndex rightIndex hshift)]

/-- The frame misses the normal, because the reflection is self-adjoint and
carries the normal onto the pivot axis. -/
theorem householderFrame_dotProduct_normal (hpos : 0 < rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (index : Fin (rank - 1)) :
    householderFrame hpos unitNormal index ⬝ᵥ unitNormal = 0 := by
  rw [householderFrame, dotProduct_reflect_left,
    reflect_householderAxis_unitNormal (pivotIndex hpos) hunit, dotProduct_smul, smul_eq_mul,
    basisVec_dotProduct_basisVec, if_neg (shiftIndex_ne_pivotIndex hpos index), mul_zero]

/-- **THE PIVOT BASIS VECTOR REFLECTS ONTO THE NORMAL.**  The reflection is an
involution and it carries the normal onto the pivot axis, thus it carries the
pivot axis back onto the normal. This is the missing direction of the frame. -/
theorem reflect_basisVec_pivotIndex (hpos : 0 < rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    reflect (householderAxis (pivotIndex hpos) unitNormal) (basisVec (pivotIndex hpos))
      = (-stableSign (pivotIndex hpos) unitNormal) • unitNormal := by
  have hkey := reflect_householderAxis_unitNormal (pivotIndex hpos) hunit
  have happly := congrArg (reflect (householderAxis (pivotIndex hpos) unitNormal)) hkey
  rw [reflect_reflect, reflect_smul] at happly
  have hsquare : (-stableSign (pivotIndex hpos) unitNormal)
      * (-stableSign (pivotIndex hpos) unitNormal) = 1 := by
    have hsq := stableSign_sq (pivotIndex hpos) unitNormal
    nlinarith [hsq]
  have hscaled : (-stableSign (pivotIndex hpos) unitNormal) • unitNormal
      = (-stableSign (pivotIndex hpos) unitNormal)
        • ((-stableSign (pivotIndex hpos) unitNormal)
          • reflect (householderAxis (pivotIndex hpos) unitNormal)
            (basisVec (pivotIndex hpos))) := by
    rw [← happly]
  rw [smul_smul, hsquare, one_smul] at hscaled
  exact hscaled.symm

/-- Every coordinate other than the pivot is a shifted frame index. -/
theorem exists_shiftIndex_of_ne_pivotIndex (hpos : 0 < rank) {coord : Fin rank}
    (hne : coord ≠ pivotIndex hpos) : ∃ index : Fin (rank - 1), shiftIndex index = coord := by
  have hval : coord.val ≠ 0 := by
    intro hzero
    exact hne (Fin.ext (by rw [hzero]; rfl))
  have hlt := coord.isLt
  refine ⟨⟨coord.val - 1, by omega⟩, Fin.ext ?_⟩
  simp only [shiftIndex]
  omega

/-- **THE HOUSEHOLDER FRAME IS A BASIS OF THE HYPERPLANE.**  Every probe that
misses the normal is the frame expansion of its own frame readings. Thus a cover
stated at the frame's coordinate combinations is a cover at every probe of the
hyperplane, which is what the Schur producer consumes. -/
theorem householderFrame_spans (hpos : 0 < rank) {unitNormal : Fin rank → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) {probe : Fin rank → ℝ}
    (hperp : probe ⬝ᵥ unitNormal = 0) :
    probe = ∑ index, (probe ⬝ᵥ householderFrame hpos unitNormal index)
      • householderFrame hpos unitNormal index := by
  classical
  set frame := householderFrame hpos unitNormal with hframe
  set residual := probe - ∑ index, (probe ⬝ᵥ frame index) • frame index with hresidual
  have hframeRead : ∀ index : Fin (rank - 1), residual ⬝ᵥ frame index = 0 := by
    intro index
    rw [hresidual, sub_dotProduct, sum_dotProduct]
    have hpick : ∑ other, (probe ⬝ᵥ frame other) • frame other ⬝ᵥ frame index
        = probe ⬝ᵥ frame index := by
      have hterm : ∀ other : Fin (rank - 1),
          (probe ⬝ᵥ frame other) • frame other ⬝ᵥ frame index
            = if other = index then probe ⬝ᵥ frame index else 0 := by
        intro other
        rw [smul_dotProduct, smul_eq_mul, hframe, householderFrame_orthonormal]
        by_cases hother : other = index
        · rw [if_pos hother, if_pos hother, mul_one, hother]
        · rw [if_neg hother, if_neg hother, mul_zero]
      rw [Finset.sum_congr rfl fun other _ => hterm other,
        Finset.sum_ite_eq' Finset.univ index (fun _ => probe ⬝ᵥ frame index),
        if_pos (Finset.mem_univ index)]
    rw [hpick, sub_self]
  have hnormalRead : residual ⬝ᵥ unitNormal = 0 := by
    rw [hresidual, sub_dotProduct, sum_dotProduct, hperp]
    have hterm : ∀ other : Fin (rank - 1),
        (probe ⬝ᵥ frame other) • frame other ⬝ᵥ unitNormal = 0 := by
      intro other
      rw [smul_dotProduct, smul_eq_mul, hframe,
        householderFrame_dotProduct_normal hpos hunit, mul_zero]
    rw [Finset.sum_congr rfl fun other _ => hterm other, Finset.sum_const_zero, sub_zero]
  have hzero : residual = 0 := by
    refine eq_zero_of_dotProduct_reflect_basisVec
      (householderAxis (pivotIndex hpos) unitNormal) residual fun coord => ?_
    by_cases hpivot : coord = pivotIndex hpos
    · rw [hpivot, reflect_basisVec_pivotIndex hpos hunit, dotProduct_smul, smul_eq_mul,
        hnormalRead, mul_zero]
    · obtain ⟨index, hindex⟩ := exists_shiftIndex_of_ne_pivotIndex hpos hpivot
      rw [← hindex]
      exact hframeRead index
  have hmove : probe - ∑ index, (probe ⬝ᵥ frame index) • frame index = 0 := by
    rw [← hresidual]; exact hzero
  exact sub_eq_zero.mp hmove

/-! ## Part 2: the long atom, and how much mass it can carry

Two shipped facts drive the whole construction. Every design carries an atom of
squared length at least `rank` (`Gtz.exists_leverage_ge_rank`), and no atom
carries more than one unit of weighted leverage
(`Gtz.weighted_leverage_le_one`). Together they say: a long atom is LIGHT, and a
light atom leaves a mass deficit for the rest of the design. -/

/-- The per-atom leverage cap, in dot-product form. -/
theorem weight_mul_selfDotProduct_le_one (design : WeightedDesign size rank)
    (label : Fin size) :
    design.weight label * (design.atom label ⬝ᵥ design.atom label) ≤ 1 := by
  have hcap := weighted_leverage_le_one design label
  rwa [leverageOf_eq_dotProduct] at hcap

/-- **EVERY DESIGN CARRIES A LONG ATOM.**  The weighted leverage of a design is
its rank, and the weights add up to one, thus some atom has squared length at
least `rank`. At rank two and up that atom overshoots the unit sphere, which is
the only input the polar construction needs. -/
theorem exists_long_atom (design : WeightedDesign size rank) (hrank : 1 ≤ rank) :
    ∃ pole : Fin size, (rank : ℝ) ≤ design.atom pole ⬝ᵥ design.atom pole := by
  obtain ⟨pole, hpole⟩ := exists_leverage_ge_rank design hrank
  exact ⟨pole, by rwa [leverageOf_eq_dotProduct] at hpole⟩

/-- The long atom of a design of rank at least two overshoots. -/
theorem exists_overshooting_atom (design : WeightedDesign size rank) (hrank : 2 ≤ rank) :
    ∃ pole : Fin size, 1 < design.atom pole ⬝ᵥ design.atom pole := by
  obtain ⟨pole, hpole⟩ := exists_long_atom design (by omega)
  refine ⟨pole, lt_of_lt_of_le ?_ hpole⟩
  exact_mod_cast Nat.one_lt_cast.mpr (by omega : 1 < rank)

/-- **AN OVERSHOOTING ATOM IS LIGHT.**  Its weighted leverage is at most one and
its leverage is more than one, thus its weight is strictly below one. The
deficit `1 - weight pole` is the margin the polar cover will carry. -/
theorem weight_lt_one_of_one_lt_selfDotProduct (design : WeightedDesign size rank)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    design.weight pole < 1 := by
  have hcap := weight_mul_selfDotProduct_le_one design pole
  have hpos := design.weight_pos pole
  nlinarith [hcap, hpos, hlong]

/-- An overshooting atom is nonzero. -/
theorem atom_ne_zero_of_one_lt_selfDotProduct (design : WeightedDesign size rank)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    design.atom pole ≠ 0 := by
  intro hzero
  rw [hzero, dotProduct_zero] at hlong
  exact absurd hlong (by norm_num)

/-! ## Part 3: the polar deficit design

Read the design against an orthonormal frame of the hyperplane orthogonal to the
pole. The pole's own atom reads as ZERO there, thus the remaining labels alone
resolve the identity of the hyperplane while carrying only `1 - weight pole` of
the mass. Renormalizing the weights to add up to one forces every atom to shrink
by the same scalar, and that shrink is exactly the strictness of the cover. -/

/-- The squared shrink factor of the polar deficit design. The `share` is the
weight left with the pole, and it must stay strictly below the pole's own
weight, which is what makes the factor strictly less than one. -/
noncomputable def polarScaleSq (design : WeightedDesign size rank) (pole : Fin size)
    (share : ℝ) : ℝ :=
  (1 - design.weight pole) / (1 - share)

theorem polarScaleSq_pos (design : WeightedDesign size rank) {pole : Fin size} {share : ℝ}
    (hshareLt : share < design.weight pole) (hweightLt : design.weight pole < 1) :
    0 < polarScaleSq design pole share := by
  rw [polarScaleSq]
  exact div_pos (by linarith) (by linarith)

/-- **THE SHRINK IS STRICT.**  The polar restriction hands the predecessor rank
a design whose atoms are strictly SHORTER than the true hyperplane readings,
thus a weak dominator of that design is a STRICT dominator of the hyperplane
identity. This one inequality is the whole repair of the named obstruction. -/
theorem polarScaleSq_lt_one (design : WeightedDesign size rank) {pole : Fin size} {share : ℝ}
    (hshareLt : share < design.weight pole) (hweightLt : design.weight pole < 1) :
    polarScaleSq design pole share < 1 := by
  rw [polarScaleSq, div_lt_one (by linarith)]
  linarith

/-- **THE POLAR DEFICIT DESIGN.**  The design read against a frame of the pole's
orthogonal hyperplane, with the pole's weight cut to `share` and the rest
renormalized, and with every atom shrunk by `Gtz.polarScaleSq`. It is a genuine
weighted design of rank `rank - 1`, thus the conjecture one RANK down applies to
it verbatim. -/
noncomputable def polarDeficitDesign (design : WeightedDesign size rank) (pole : Fin size)
    (share : ℝ) (frame : Fin (rank - 1) → Fin rank → ℝ)
    (hshare : 0 < share) (hshareLt : share < design.weight pole)
    (hweightLt : design.weight pole < 1)
    (horthonormal : ∀ leftIndex rightIndex, frame leftIndex ⬝ᵥ frame rightIndex
      = if leftIndex = rightIndex then 1 else 0)
    (hpoleFlat : ∀ index, design.atom pole ⬝ᵥ frame index = 0) :
    WeightedDesign size (rank - 1) where
  atom := fun label index =>
    Real.sqrt (polarScaleSq design pole share) * (design.atom label ⬝ᵥ frame index)
  weight := fun label =>
    if label = pole then share
    else design.weight label * ((1 - share) / (1 - design.weight pole))
  weight_pos := by
    intro label
    by_cases hlabel : label = pole
    · rw [if_pos hlabel]; exact hshare
    · rw [if_neg hlabel]
      have hshareWeight := design.weight_pos label
      have hnum : (0 : ℝ) < 1 - share := by linarith [design.weight_pos pole]
      have hden : (0 : ℝ) < 1 - design.weight pole := by linarith
      positivity
  weight_sum_one := by
    classical
    have hden : (1 : ℝ) - design.weight pole ≠ 0 := by linarith
    have hsplit : ∑ label, (if label = pole then share
          else design.weight label * ((1 - share) / (1 - design.weight pole)))
        = share + ∑ label ∈ Finset.univ.erase pole,
            design.weight label * ((1 - share) / (1 - design.weight pole)) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun label => if label = pole then share
          else design.weight label * ((1 - share) / (1 - design.weight pole)))
        (Finset.mem_univ pole), if_pos rfl]
      exact congrArg (share + ·)
        (Finset.sum_congr rfl fun label hlabel => by
          rw [if_neg (Finset.ne_of_mem_erase hlabel)])
    have hmass : ∑ label ∈ Finset.univ.erase pole, design.weight label
        = 1 - design.weight pole := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ pole), design.weight_sum_one]
    rw [hsplit, ← Finset.sum_mul, hmass]
    field_simp
    ring
  isParseval := by
    classical
    have hscalePos := polarScaleSq_pos design hshareLt hweightLt
    have hscaleSq : Real.sqrt (polarScaleSq design pole share) ^ 2
        = polarScaleSq design pole share := Real.sq_sqrt hscalePos.le
    have hden : (1 : ℝ) - design.weight pole ≠ 0 := by linarith
    have hnum : (1 : ℝ) - share ≠ 0 := by linarith [design.weight_pos pole]
    ext rowIndex colIndex
    rw [Matrix.sum_apply, Matrix.one_apply, ← horthonormal rowIndex colIndex,
      dotProduct_eq_sum_weight_mul_pair design (frame rowIndex) (frame colIndex)]
    refine Finset.sum_congr rfl fun label _ => ?_
    simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
    by_cases hlabel : label = pole
    · subst hlabel
      rw [if_pos rfl, hpoleFlat rowIndex, hpoleFlat colIndex]
      ring
    · rw [if_neg hlabel]
      have hexpand : (Real.sqrt (polarScaleSq design pole share)
            * (design.atom label ⬝ᵥ frame rowIndex))
          * (Real.sqrt (polarScaleSq design pole share)
            * (design.atom label ⬝ᵥ frame colIndex))
          = Real.sqrt (polarScaleSq design pole share) ^ 2
            * ((design.atom label ⬝ᵥ frame rowIndex)
              * (design.atom label ⬝ᵥ frame colIndex)) := by ring
      rw [hexpand, hscaleSq, polarScaleSq]
      field_simp

/-- **THE POLAR STRICT COVER.**  With the conjecture one RANK down, every design
with an overshooting atom carries `rank - 1` OTHER atoms that cover the pole's
orthogonal hyperplane with the explicit margin `(1 - share) / (1 - weight pole)`,
which is strictly more than one at every admissible `share`.

This is the repair of the named obstruction of the degenerate arm. The weak
cover of `Gtz.exists_subspace_dominating_subset` is upgraded to a STRICT one for
free, because the pole's weight is missing from the restricted design. -/
theorem exists_polarStrictCover (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    {share : ℝ} (hshare : 0 < share) (hshareLt : share < design.weight pole) :
    ∃ covering : Finset (Fin size), covering.card = rank - 1 ∧ pole ∉ covering
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          ((1 - share) / (1 - design.weight pole)) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hpos : 0 < rank := by omega
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  have hden : (0 : ℝ) < 1 - design.weight pole := by linarith
  have hnum : (0 : ℝ) < 1 - share := by linarith [design.weight_pos pole]
  have hpoleNe := atom_ne_zero_of_one_lt_selfDotProduct design hlong
  set unitNormal : Fin rank → ℝ :=
    (Real.sqrt (design.atom pole ⬝ᵥ design.atom pole))⁻¹ • design.atom pole with hunitNormal
  have hunit : unitNormal ⬝ᵥ unitNormal = 1 := unit_of_ne_zero (design.atom pole) hpoleNe
  set frame := householderFrame hpos unitNormal with hframe
  have horthonormal := householderFrame_orthonormal hpos unitNormal
  have hframeNormal := householderFrame_dotProduct_normal hpos hunit
  have hrootPos : 0 < Real.sqrt (design.atom pole ⬝ᵥ design.atom pole) :=
    Real.sqrt_pos.mpr (by linarith)
  have hpoleFlat : ∀ index, design.atom pole ⬝ᵥ frame index = 0 := by
    intro index
    have hread := hframeNormal index
    rw [hunitNormal, dotProduct_smul, smul_eq_mul] at hread
    have hzero : frame index ⬝ᵥ design.atom pole = 0 := by
      rcases mul_eq_zero.mp hread with hinv | hdot
      · exact absurd hinv (by positivity)
      · exact hdot
    rw [dotProduct_comm]
    exact hzero
  -- the restricted design and the rank-down dispatch
  set restricted := polarDeficitDesign design pole share frame hshare hshareLt hweightLt
    horthonormal hpoleFlat with hrestricted
  obtain ⟨rawCovering, hrawCard, hrawDominates⟩ := hpredecessor size restricted
  -- drop the pole and pad back inside the complement of the pole
  have hsubset : rawCovering.erase pole ⊆ Finset.univ.erase pole :=
    Finset.erase_subset_erase pole (Finset.subset_univ rawCovering)
  have herasedCard : (rawCovering.erase pole).card ≤ rank - 1 :=
    le_trans (Finset.card_erase_le) (le_of_eq hrawCard)
  have hcomplementCard : rank - 1 ≤ (Finset.univ.erase pole).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ pole), Finset.card_univ, Fintype.card_fin]
    have hsize := rank_le_of_design design
    omega
  obtain ⟨covering, hcoverSup, hcoverSub, hcoverCard⟩ :=
    Finset.exists_subsuperset_card_eq hsubset herasedCard hcomplementCard
  have hpoleNotMem : pole ∉ covering := fun hmem =>
    (Finset.notMem_erase pole Finset.univ) (hcoverSub hmem)
  refine ⟨covering, hcoverCard, hpoleNotMem, fun probe hprobe => ?_⟩
  -- transport the probe into frame coordinates
  have hprobeNormal : probe ⬝ᵥ unitNormal = 0 := by
    rw [hunitNormal, dotProduct_smul, smul_eq_mul, hprobe, mul_zero]
  have hexpansion := householderFrame_spans hpos hunit hprobeNormal
  rw [← hframe] at hexpansion
  set coeff : Fin (rank - 1) → ℝ := fun index => probe ⬝ᵥ frame index with hcoeffDef
  have hcoeff : ∀ index : Fin (rank - 1), coeff index = probe ⬝ᵥ frame index := fun _ => rfl
  have hread : ∀ label : Fin size,
      design.atom label ⬝ᵥ probe = ∑ index, coeff index * (design.atom label ⬝ᵥ frame index) := by
    intro label
    conv_lhs => rw [hexpansion]
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun index _ => by
      rw [dotProduct_smul, smul_eq_mul, hcoeff index]
  have hprobeLength : coeff ⬝ᵥ coeff = probe ⬝ᵥ probe := by
    have hstep : probe ⬝ᵥ probe = ∑ index, coeff index * (frame index ⬝ᵥ probe) := by
      nth_rewrite 1 [hexpansion]
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl fun index _ => by
        rw [smul_dotProduct, smul_eq_mul, hcoeff index]
    rw [hstep, dotProduct]
    exact Finset.sum_congr rfl fun index _ => by
      rw [dotProduct_comm (frame index) probe, hcoeff index]
  -- the predecessor's weak domination, read at the frame coordinates
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hrawDominates).2 coeff
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, subsetSum_form, Matrix.one_mulVec] at hform
  have hatomRead : ∀ label : Fin size, restricted.atom label ⬝ᵥ coeff
      = Real.sqrt (polarScaleSq design pole share) * (design.atom label ⬝ᵥ probe) := by
    intro label
    rw [hread label, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [hrestricted]
    show Real.sqrt (polarScaleSq design pole share) * (design.atom label ⬝ᵥ frame index)
      * coeff index = _
    ring
  rw [Finset.sum_congr rfl fun label _ => congrArg (· ^ 2) (hatomRead label), hprobeLength]
    at hform
  -- remove the pole from the raw covering, then grow to the padded covering
  have hpoleTerm : (design.atom pole ⬝ᵥ probe) ^ 2 = 0 := by
    rw [dotProduct_comm, hprobe]; ring
  have hraw : ∑ label ∈ rawCovering,
        (Real.sqrt (polarScaleSq design pole share) * (design.atom label ⬝ᵥ probe)) ^ 2
      = polarScaleSq design pole share
        * ∑ label ∈ rawCovering.erase pole, (design.atom label ⬝ᵥ probe) ^ 2 := by
    have hscaleSq : Real.sqrt (polarScaleSq design pole share) ^ 2
        = polarScaleSq design pole share :=
      Real.sq_sqrt (polarScaleSq_pos design hshareLt hweightLt).le
    rw [Finset.mul_sum]
    by_cases hmem : pole ∈ rawCovering
    · rw [← Finset.add_sum_erase rawCovering
        (fun label => (Real.sqrt (polarScaleSq design pole share)
          * (design.atom label ⬝ᵥ probe)) ^ 2) hmem]
      have hkill : (Real.sqrt (polarScaleSq design pole share)
          * (design.atom pole ⬝ᵥ probe)) ^ 2 = 0 := by
        rw [mul_pow, hpoleTerm, mul_zero]
      rw [hkill, zero_add]
      exact Finset.sum_congr rfl fun label _ => by rw [mul_pow, hscaleSq]
    · rw [Finset.erase_eq_of_notMem hmem]
      exact Finset.sum_congr rfl fun label _ => by rw [mul_pow, hscaleSq]
  rw [hraw] at hform
  have hgrow : ∑ label ∈ rawCovering.erase pole, (design.atom label ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcoverSup fun label _ _ => sq_nonneg _
  have hscalePos := polarScaleSq_pos design hshareLt hweightLt
  have hchain : probe ⬝ᵥ probe
      ≤ polarScaleSq design pole share * ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_left hgrow hscalePos.le
    linarith [hform, hstep]
  have hinv : ((1 - share) / (1 - design.weight pole))
      * polarScaleSq design pole share = 1 := by
    rw [polarScaleSq, div_mul_div_comm, mul_comm (1 - share) (1 - design.weight pole)]
    exact div_self (by positivity)
  have hfactorPos : 0 < (1 - share) / (1 - design.weight pole) := div_pos hnum hden
  calc ((1 - share) / (1 - design.weight pole)) * (probe ⬝ᵥ probe)
      ≤ ((1 - share) / (1 - design.weight pole))
        * (polarScaleSq design pole share
          * ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) :=
        mul_le_mul_of_nonneg_left hchain hfactorPos.le
    _ = ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
        rw [← mul_assoc, hinv, one_mul]

/-- The polar strict cover with the margin made explicit and the `share` fixed
at half the pole's weight. The margin is then `weight pole / (2 - 2 * weight pole)`,
which is strictly positive at every overshooting atom. -/
theorem exists_polarCover_margin (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    ∃ (covering : Finset (Fin size)) (margin : ℝ), 0 < margin
      ∧ covering.card = rank - 1 ∧ pole ∉ covering
      ∧ ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hweightPos := design.weight_pos pole
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  obtain ⟨covering, hcard, hnotMem, hcover⟩ :=
    exists_polarStrictCover hrank hpredecessor design hlong
      (share := design.weight pole / 2) (by linarith) (by linarith)
  refine ⟨covering, design.weight pole / (2 * (1 - design.weight pole)), ?_, hcard, hnotMem,
    fun probe hprobe => ?_⟩
  · exact div_pos hweightPos (by linarith)
  · have hne : (1 : ℝ) - design.weight pole ≠ 0 := by linarith
    have hrewrite : (1 : ℝ) + design.weight pole / (2 * (1 - design.weight pole))
        = (1 - design.weight pole / 2) / (1 - design.weight pole) := by
      rw [eq_div_iff hne]
      field_simp
      ring
    rw [hrewrite]
    exact hcover probe hprobe

/-! ## Part 4: the Schur producer at the polar frame

The strict cover is one of the two halves the Schur producer
`Gtz.posDef_of_normalSurplus_hyperplaneCover` needs. The other half is the
COUPLING between the pole direction and the hyperplane, and the covering set
controls it through one scalar: the total squared pairing of the covering atoms
against the pole. -/

/-- Strict domination grows with the subset. The weak form is
`Gtz.Dominates.mono`. -/
theorem posDef_subsetSum_mono (design : WeightedDesign size rank)
    {small large : Finset (Fin size)} (hsub : small ⊆ large)
    (hsmall : (subsetSum design small - 1).PosDef) :
    (subsetSum design large - 1).PosDef := by
  have hsymm : (subsetSum design large - 1)ᵀ = subsetSum design large - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_subsetSum]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobeNe => ?_⟩
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hsmall).2 (x := probe) hprobeNe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, subsetSum_form,
    Matrix.one_mulVec] at hvalue ⊢
  have hgrow : ∑ label ∈ small, (design.atom label ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ large, (design.atom label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun label _ _ => sq_nonneg _
  linarith

/-- A strict dominator that is too small grows to a card-`rank` one, because
adding atoms only helps and a design has at least `rank` labels. -/
theorem exists_card_eq_posDef (design : WeightedDesign size rank)
    {small : Finset (Fin size)} (hcard : small.card ≤ rank)
    (hsmall : (subsetSum design small - 1).PosDef) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  obtain ⟨big, hsub, -, hbigCard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ small) hcard
      (by rw [Finset.card_univ, Fintype.card_fin]; exact rank_le_of_design design)
  exact ⟨big, hbigCard, posDef_subsetSum_mono design hsub hsmall⟩

/-- **THE POLAR SCHUR CORE.**  Putting the pole back onto a covering set gives a
strictly dominating subset exactly when one scalar inequality holds at every
probe of the pole's orthogonal hyperplane: the squared COUPLING between the
covering and the pole must stay below the product of the pole's own gap
`leverage * (leverage - 1)` plus the covering's tilt, and the covering's excess.

Everything about the normalization is discharged here: the pole supplies the
whole surplus along its own direction, the covering supplies the whole cover,
and the shipped completed square
`Gtz.posDef_of_normalSurplus_hyperplaneCover` does the rest. Both producers
below feed this core. -/
theorem posDef_insert_of_polarSchur (design : WeightedDesign size rank)
    {pole : Fin size} {covering : Finset (Fin size)}
    (hpoleNotMem : pole ∉ covering)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hschur : ∀ probe : Fin rank → ℝ, design.atom pole ⬝ᵥ probe = 0 → probe ≠ 0 →
      (∑ label ∈ covering,
          (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ design.atom pole)) ^ 2
        < ((design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)
            + ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2)
          * ((∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe)) :
    (subsetSum design (insert pole covering) - 1).PosDef := by
  classical
  set leverage : ℝ := design.atom pole ⬝ᵥ design.atom pole with hleverage
  have hleveragePos : 0 < leverage := by rw [hleverage]; linarith
  have hpoleNe := atom_ne_zero_of_one_lt_selfDotProduct design hlong
  set root : ℝ := Real.sqrt leverage with hroot
  have hrootPos : 0 < root := Real.sqrt_pos.mpr hleveragePos
  have hrootSq : root ^ 2 = leverage := Real.sq_sqrt hleveragePos.le
  set unitNormal : Fin rank → ℝ := root⁻¹ • design.atom pole with hunitNormal
  have hunit : unitNormal ⬝ᵥ unitNormal = 1 := unit_of_ne_zero (design.atom pole) hpoleNe
  have hnormalRead : ∀ label : Fin size, design.atom label ⬝ᵥ unitNormal
      = root⁻¹ * (design.atom label ⬝ᵥ design.atom pole) := by
    intro label
    rw [hunitNormal, dotProduct_smul, smul_eq_mul]
  have hpoleNormal : design.atom pole ⬝ᵥ unitNormal = root := by
    rw [hnormalRead pole, ← hleverage, ← hrootSq]
    field_simp
  set tilt : ℝ := ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 with htiltDef
  have htiltNonneg : 0 ≤ tilt :=
    Finset.sum_nonneg fun label _ => sq_nonneg _
  have hleverageNe : leverage ≠ 0 := ne_of_gt hleveragePos
  have hrootInvSq : root⁻¹ ^ 2 = leverage⁻¹ := by rw [inv_pow, hrootSq]
  have hnormalSum : ∑ label ∈ insert pole covering, (design.atom label ⬝ᵥ unitNormal) ^ 2
      = leverage⁻¹ * (leverage ^ 2 + tilt) := by
    have hterms : ∀ label : Fin size, (design.atom label ⬝ᵥ unitNormal) ^ 2
        = leverage⁻¹ * (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
      intro label
      rw [hnormalRead label, mul_pow, hrootInvSq]
    rw [Finset.sum_congr rfl fun label _ => hterms label, ← Finset.mul_sum,
      Finset.sum_insert hpoleNotMem, ← hleverage, ← htiltDef]
  have hsurplus : 1 < ∑ label ∈ insert pole covering, (design.atom label ⬝ᵥ unitNormal) ^ 2 := by
    rw [hnormalSum]
    have hexpand : leverage⁻¹ * (leverage ^ 2 + tilt)
        = leverage + leverage⁻¹ * tilt := by
      field_simp
    have hnonneg : 0 ≤ leverage⁻¹ * tilt := by positivity
    rw [hexpand]
    linarith [hlong, hnonneg]
  refine posDef_of_normalSurplus_hyperplaneCover design (insert pole covering) unitNormal hunit
    hsurplus fun probe hprobeNormal hprobeNe => ?_
  have hprobePole : probe ⬝ᵥ design.atom pole = 0 := by
    rw [hunitNormal, dotProduct_smul, smul_eq_mul] at hprobeNormal
    rcases mul_eq_zero.mp hprobeNormal with hinv | hdot
    · exact absurd hinv (by positivity)
    · exact hdot
  have hpoleProbe : design.atom pole ⬝ᵥ probe = 0 := by
    rw [dotProduct_comm]; exact hprobePole
  set spread : ℝ := ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 with hspread
  set cross : ℝ := ∑ label ∈ covering,
    (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ design.atom pole) with hcross
  have hcrossSum : ∑ label ∈ insert pole covering,
      (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ unitNormal) = root⁻¹ * cross := by
    rw [Finset.sum_insert hpoleNotMem, hpoleProbe, zero_mul, zero_add, hcross, Finset.mul_sum]
    exact Finset.sum_congr rfl fun label _ => by rw [hnormalRead label]; ring
  have hspreadSum : ∑ label ∈ insert pole covering, (design.atom label ⬝ᵥ probe) ^ 2
      = spread := by
    rw [Finset.sum_insert hpoleNotMem, hpoleProbe, hspread]
    ring
  rw [hcrossSum, hnormalSum, hspreadSum]
  have hmain : cross ^ 2 < (leverage * (leverage - 1) + tilt) * (spread - probe ⬝ᵥ probe) := by
    rw [hcross, hleverage, htiltDef, hspread]
    exact hschur probe hpoleProbe hprobeNe
  have hleft : (root⁻¹ * cross) ^ 2 = leverage⁻¹ * cross ^ 2 := by
    rw [mul_pow, hrootInvSq]
  have hright : leverage⁻¹ * (leverage ^ 2 + tilt) - 1
      = leverage⁻¹ * (leverage * (leverage - 1) + tilt) := by
    field_simp
    ring
  rw [hleft, hright, mul_assoc]
  exact mul_lt_mul_of_pos_left hmain (by positivity)

/-- **THE POLAR SCHUR PRODUCER, TILT FORM.**  A covering set that covers the
pole's orthogonal hyperplane with margin `margin` AND is almost orthogonal to
the pole gives a strictly dominating subset, once the pole is put back.

The tilt budget is `margin * leverage * (leverage - 1)`, and Cauchy-Schwarz is
what prices the coupling by the tilt. -/
theorem posDef_insert_of_polarCover (design : WeightedDesign size rank)
    {pole : Fin size} {covering : Finset (Fin size)} {margin : ℝ}
    (hpoleNotMem : pole ∉ covering)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hmargin : 0 < margin)
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2)
    (htilt : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2
      < margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    (subsetSum design (insert pole covering) - 1).PosDef := by
  classical
  refine posDef_insert_of_polarSchur design hpoleNotMem hlong fun probe hpoleProbe hprobeNe => ?_
  set leverage : ℝ := design.atom pole ⬝ᵥ design.atom pole with hleverage
  set tilt : ℝ := ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 with htiltDef
  set spread : ℝ := ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 with hspread
  set cross : ℝ := ∑ label ∈ covering,
    (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ design.atom pole) with hcross
  have hprobePole : probe ⬝ᵥ design.atom pole = 0 := by rw [dotProduct_comm]; exact hpoleProbe
  have hprobeLength : 0 < probe ⬝ᵥ probe := selfDotProduct_pos hprobeNe
  have hleveragePos : 0 < leverage := by rw [hleverage]; linarith
  have hcoverFires := hcover probe hprobePole
  rw [← hspread] at hcoverFires
  have hcauchy : cross ^ 2 ≤ tilt * spread := by
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq covering
      (fun label => design.atom label ⬝ᵥ design.atom pole)
      (fun label => design.atom label ⬝ᵥ probe)
    have hswap : ∑ label ∈ covering,
        (design.atom label ⬝ᵥ design.atom pole) * (design.atom label ⬝ᵥ probe) = cross := by
      rw [hcross]
      exact Finset.sum_congr rfl fun label _ => by ring
    rw [hswap] at hraw
    rw [htiltDef, hspread]
    exact hraw
  have hleverageGap : 0 < leverage * (leverage - 1) := by nlinarith [hlong, hleveragePos]
  have hgapPos : 0 < spread - probe ⬝ᵥ probe := by
    nlinarith [hcoverFires, mul_pos hmargin hprobeLength]
  have hstepOne : leverage * (leverage - 1) * ((1 + margin) * (probe ⬝ᵥ probe))
      ≤ leverage * (leverage - 1) * spread :=
    mul_le_mul_of_nonneg_left hcoverFires hleverageGap.le
  have hstepTwo : (leverage * (leverage - 1) + tilt) * (probe ⬝ᵥ probe)
      < leverage * (leverage - 1) * ((1 + margin) * (probe ⬝ᵥ probe)) := by
    have htiltBound : tilt < margin * (leverage * (leverage - 1)) := by
      rw [← mul_assoc, htiltDef, hleverage]
      exact htilt
    nlinarith [htiltBound, hprobeLength]
  nlinarith [hcauchy, hstepOne, hstepTwo, hgapPos]

/-- **THE POLAR SCHUR PRODUCER, COUPLING FORM.**  The sharper of the two: it
bounds the COUPLING functional directly rather than through Cauchy-Schwarz, thus
it fires at covering sets whose tilt is large but whose coupling cancels. No
Cauchy-Schwarz step is spent, and the budget is the same one. -/
theorem posDef_insert_of_polarCoupling (design : WeightedDesign size rank)
    {pole : Fin size} {covering : Finset (Fin size)} {margin couplingBound : ℝ}
    (hpoleNotMem : pole ∉ covering)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hmargin : 0 < margin)
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2)
    (hcoupling : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (∑ label ∈ covering,
          (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ design.atom pole)) ^ 2
        ≤ couplingBound * (probe ⬝ᵥ probe))
    (hbound : couplingBound < margin * (design.atom pole ⬝ᵥ design.atom pole)
      * (design.atom pole ⬝ᵥ design.atom pole - 1)) :
    (subsetSum design (insert pole covering) - 1).PosDef := by
  classical
  refine posDef_insert_of_polarSchur design hpoleNotMem hlong fun probe hpoleProbe hprobeNe => ?_
  set leverage : ℝ := design.atom pole ⬝ᵥ design.atom pole with hleverage
  set tilt : ℝ := ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 with htiltDef
  set spread : ℝ := ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 with hspread
  set cross : ℝ := ∑ label ∈ covering,
    (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ design.atom pole) with hcross
  have hprobePole : probe ⬝ᵥ design.atom pole = 0 := by rw [dotProduct_comm]; exact hpoleProbe
  have hprobeLength : 0 < probe ⬝ᵥ probe := selfDotProduct_pos hprobeNe
  have hleveragePos : 0 < leverage := by rw [hleverage]; linarith
  have htiltNonneg : 0 ≤ tilt := Finset.sum_nonneg fun label _ => sq_nonneg _
  have hcoverFires := hcover probe hprobePole
  rw [← hspread] at hcoverFires
  have hcouplingFires := hcoupling probe hprobePole
  rw [← hcross] at hcouplingFires
  have hboundFires : couplingBound < margin * (leverage * (leverage - 1)) := by
    rw [← mul_assoc, hleverage]
    exact hbound
  have hleverageGap : 0 < leverage * (leverage - 1) := by nlinarith [hlong, hleveragePos]
  have hgap : margin * (probe ⬝ᵥ probe) ≤ spread - probe ⬝ᵥ probe := by nlinarith [hcoverFires]
  have hgapPos : 0 < spread - probe ⬝ᵥ probe := by
    nlinarith [hgap, mul_pos hmargin hprobeLength]
  have hstep : couplingBound * (probe ⬝ᵥ probe)
      < (leverage * (leverage - 1) + tilt) * (spread - probe ⬝ᵥ probe) := by
    have hone : 0 ≤ tilt * (spread - probe ⬝ᵥ probe) := mul_nonneg htiltNonneg hgapPos.le
    have htwo : leverage * (leverage - 1) * (margin * (probe ⬝ᵥ probe))
        ≤ leverage * (leverage - 1) * (spread - probe ⬝ᵥ probe) :=
      mul_le_mul_of_nonneg_left hgap hleverageGap.le
    have hthree : couplingBound * (probe ⬝ᵥ probe)
        < leverage * (leverage - 1) * (margin * (probe ⬝ᵥ probe)) := by
      have hmul := mul_lt_mul_of_pos_right hboundFires hprobeLength
      linarith [hmul]
    nlinarith [hone, htwo, hthree]
  linarith [hcouplingFires, hstep]

/-! ### What a tie forces on every polar cover

The producer read backwards is an unconditional inequality about ties: a tie
cannot afford a covering set that is almost orthogonal to any of its long atoms.
This is the quantitative content the residual has to beat. -/

/-- **AT A TIE, EVERY MARGIN-COVER IS TILTED.**  A tie admits no strictly
dominating card-`rank` subset, thus every covering set of an overshooting atom's
hyperplane carries at least the whole tilt budget. No predecessor rank is spent
here: the inequality is a direct reading of the producer. -/
theorem budget_le_tilt_of_isTie (design : WeightedDesign size rank) (htie : IsTie design)
    {pole : Fin size} {covering : Finset (Fin size)} {margin : ℝ}
    (hrank : 1 ≤ rank) (hcard : covering.card ≤ rank - 1) (hpoleNotMem : pole ∉ covering)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) (hmargin : 0 < margin)
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) :
    margin * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  classical
  by_contra hsmall
  rw [not_le] at hsmall
  have hposDef := posDef_insert_of_polarCover design hpoleNotMem hlong hmargin hcover hsmall
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hpoleNotMem]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- **THE TIE INEQUALITY, WITH THE COVER SUPPLIED.**  Composed with the polar
strict cover: under the previous rank, every tie hands back, at every one of its
overshooting atoms, a covering set of `rank - 1` other atoms that covers the
hyperplane with a margin AND spends the whole tilt budget. That pair of
inequalities is a new quantitative constraint on ties at every rank. -/
theorem exists_tilted_polarCover_of_isTie (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    (htie : IsTie design) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    ∃ (covering : Finset (Fin size)) (margin : ℝ), 0 < margin ∧ covering.card = rank - 1
      ∧ pole ∉ covering
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ margin * (design.atom pole ⬝ᵥ design.atom pole)
            * (design.atom pole ⬝ᵥ design.atom pole - 1)
          ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 := by
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  exact ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover,
    budget_le_tilt_of_isTie design htie (by omega) (le_of_eq hcard) hnotMem hlong hmarginPos
      hcover⟩


/-! ## Part 5: the residual, and the collapse of the hinge onto it

The strict cover is a theorem. What is left is the tilt: the covering set must
be choosable almost orthogonal to the pole. That single selection statement
carries the whole general-rank hinge. -/

/-- **THE TILT RESIDUAL.**  At a primitive design with an overshooting atom, a
covering set of the pole's orthogonal hyperplane can be chosen with total
squared pairing against the pole below the budget
`margin * leverage * (leverage - 1)`.

The cover half of the hypothesis is supplied by
`Gtz.exists_polarCover_margin` under the previous rank, thus this Prop is the
whole remaining content of the hinge. -/
def PolarTiltSelection (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The same residual with the tie dropped. It is the stronger Prop, and it
closes the two SELECTION residuals of the balanced arm, whose statements
produce a dominating subset rather than contradict a tie. -/
def PolarTiltSelectionTieFree (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ selected : Finset (Fin size), selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ ∑ label ∈ selected, (design.atom label ⬝ᵥ design.atom pole) ^ 2
          < margin * (design.atom pole ⬝ᵥ design.atom pole)
              * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The tie-free residual is the stronger one. -/
theorem polarTiltSelection_of_tieFree (hfree : PolarTiltSelectionTieFree size rank) :
    PolarTiltSelection size rank :=
  fun design pole covering margin hprimitive _htie hlong hmargin hcard hnotMem hcover =>
    hfree design pole covering margin hprimitive hlong hmargin hcard hnotMem hcover

/-- **EVERY PRIMITIVE DESIGN CARRIES A STRICT DOMINATOR, UNDER THE PREVIOUS RANK
AND THE TILT RESIDUAL.**  The long atom is free, the strict cover is free, and
the tilt residual supplies the selection. Putting the pole back gives a
card-`rank` subset that beats the identity strictly. -/
theorem exists_dominating_of_polarTiltTieFree (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelectionTieFree size rank)
    (design : WeightedDesign size rank) (hprimitive : IsPrimitiveDesign design) :
    ∃ selected : Finset (Fin size), selected.card = rank
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive hlong hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover hselTilt
  refine exists_card_eq_posDef design ?_ hposDef
  rw [Finset.card_insert_of_notMem hselNotMem, hselCard]
  omega

/-- **THE HINGE, FROM THE PREVIOUS RANK AND ONE RESIDUAL.**  A tie with no
parallel pair is primitive, the residual then produces a strict dominator, and a
tie forbids one. -/
theorem hingeHoldsAtSize_of_polarTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, hselCard, hselNotMem, hselCover, hselTilt⟩ :=
    htilt design pole covering margin hprimitive htie hlong hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCover design hselNotMem hlong hmarginPos hselCover hselTilt
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- The tie-free residual closes the hinge too. -/
theorem hingeHoldsAtSize_of_polarTiltTieFree (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelectionTieFree size rank) :
    HingeHoldsAtSize size rank :=
  hingeHoldsAtSize_of_polarTilt hrank hpredecessor (polarTiltSelection_of_tieFree htilt)

/-! ### The three arms, the sub-arm and the cover, all at once

Every arm of `Gtz.design_stress_trichotomy` concludes `Gtz.HasParallelPair` from
`Gtz.IsTie`, thus every one of them is an instance of
`Gtz.HingeHoldsAtSize`. The residual list of the inherited map collapses. -/

/-- Arm (i) from the tilt residual. -/
theorem stressFreeArmAt_of_polarTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    StressFreeArmAt size rank :=
  fun design _hfree htie => hingeHoldsAtSize_of_polarTilt hrank hpredecessor htilt design htie

/-- Arm (ii) from the tilt residual. -/
theorem balancedArmAt_of_polarTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    BalancedArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTilt hrank hpredecessor htilt design htie

/-- Arm (iii) from the tilt residual. -/
theorem degenerateArmAt_of_polarTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    DegenerateArmAt size rank :=
  fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
    hingeHoldsAtSize_of_polarTilt hrank hpredecessor htilt design htie

/-- **THE PARTIAL-SUPPORT SUB-ARM, THE ONE WITH NO RANK-THREE ANALOGUE.**  It
falls out of the same collapse, thus the two residuals
`Gtz.PartialSupportSideIsRankSized` and `Gtz.PartialSupportSelectionAtRank` are
not needed on this route. -/
theorem balancedPartialSupportArmAt_of_polarTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    BalancedPartialSupportArmAt size rank :=
  fun design _stressCoeff _hstressNe _hstress _hunsupported _hposSpans _hnegSpans htie =>
    hingeHoldsAtSize_of_polarTilt hrank hpredecessor htilt design htie

/-- The full-support sub-arm, for the record. -/
theorem balancedFullSupportArmAt_of_polarTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    BalancedFullSupportArmAt size rank :=
  fun design _stressCoeff _hstress _hfull htie =>
    hingeHoldsAtSize_of_polarTilt hrank hpredecessor htilt design htie

/-- **THE ASSIGNED DEGENERATE RESIDUAL, DISCHARGED FROM THE TILT.**  On the
degenerate branch the hypotheses of `Gtz.DegenerateHyperplaneCover` include a
primitive tie, which the collapse refutes outright. -/
theorem degenerateHyperplaneCover_of_polarTilt (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    DegenerateHyperplaneCover size rank := by
  intro design _stressCoeff _unitNormal _pole hprimitive htie _hstressNe _hunit _hstress
    _hsupport _hpole
  exact absurd (hingeHoldsAtSize_of_polarTilt hrank hpredecessor htilt design htie)
    ((isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive)

/-- **THE BALANCED-STRATUM SELECTION, DISCHARGED FROM THE TIE-FREE TILT.**  Its
statement produces a dominating subset from a primitive design, thus it needs
the tie-free form of the residual. -/
theorem balancedStratumSelectionAtRank_of_polarTiltTieFree (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelectionTieFree size rank) :
    BalancedStratumSelectionAtRank size rank :=
  fun design _stressCoeff _hstress _hfull hprimitive _hgapPos _hgapNeg _hbudget =>
    exists_dominating_of_polarTiltTieFree hrank hpredecessor htilt design hprimitive

/-- The partial-support selection, from the same tie-free residual. -/
theorem partialSupportSelectionAtRank_of_polarTiltTieFree (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelectionTieFree size rank) :
    PartialSupportSelectionAtRank size rank :=
  fun design _stressCoeff _hstress _hstressNe _hunsupported _hposSpans _hnegSpans hprimitive
    _hgapPos _hgapNeg _hbudget =>
    exists_dominating_of_polarTiltTieFree hrank hpredecessor htilt design hprimitive

/-! ### The two registry hinge obligations -/

/-- **THE THRESHOLD CELL OBLIGATION, ON ONE RESIDUAL AND THE PREVIOUS RANK.**
The statement of `Skeleton.obligationThresholdCellHingeRankFourAndUp` with the
ladder's own induction hypothesis carried. Against
`Gtz.thresholdCellHingeRankFourAndUp_of_repairedResiduals` this trades FIVE
named residuals for ONE. -/
theorem thresholdCellHingeRankFourAndUp_of_polarTilt
    (htilt : ∀ rank : ℕ, 4 ≤ rank → PolarTiltSelection (thresholdSize rank) rank) :
    ∀ rank : ℕ, 4 ≤ rank → GtzWeightedAll (rank - 1) →
      GtzWeighted (rank * (rank + 1) / 2 - 1) rank →
        ∀ design : WeightedDesign (rank * (rank + 1) / 2) rank,
          IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor _hcell design htie
  exact hingeHoldsAtSize_of_polarTilt (by omega) hpredecessor (htilt rank hrank) design htie

/-- **THE SUB-THRESHOLD BAND OBLIGATION, BY THE SAME COLLAPSE.**  The statement
of `Skeleton.obligationSubThresholdBandHinge` with the previous rank carried. -/
theorem subThresholdBandHinge_of_polarTilt
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size < thresholdSize rank →
      PolarTiltSelection size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size < rank * (rank + 1) / 2 →
        GtzWeighted (size - 1) rank →
          ∀ design : WeightedDesign size rank,
            IsTie design → HasParallelPair design := by
  intro rank hrank hpredecessor size hlow hhigh _hcell design htie
  exact hingeHoldsAtSize_of_polarTilt (by omega) hpredecessor
    (htilt rank size hrank hlow hhigh) design htie

/-- **THE WHOLE SHARP WINDOW.**  Both registry hinge obligations are the two
ends of this window, and one residual closes it at every cell. -/
theorem sharpWindowHinge_of_polarTilt
    (htilt : ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ thresholdSize rank →
      PolarTiltSelection size rank) :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ∀ size : ℕ, 2 * rank ≤ size → size ≤ rank * (rank + 1) / 2 →
        HingeHoldsAtSize size rank := by
  intro rank hrank hpredecessor size hlow hhigh
  exact hingeHoldsAtSize_of_polarTilt (by omega) hpredecessor (htilt rank size hrank hlow hhigh)

/-- Arm (i) at the deciding cell of a rank. -/
theorem thresholdStressFreeArm_of_polarTilt (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelection (thresholdSize rank) rank) : ThresholdStressFreeArm rank :=
  stressFreeArmAt_of_polarTilt hrank hpredecessor htilt

/-- Arm (iii) at the deciding cell of a rank. -/
theorem thresholdDegenerateArm_of_polarTilt (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelection (thresholdSize rank) rank) : ThresholdDegenerateArm rank :=
  degenerateArmAt_of_polarTilt hrank hpredecessor htilt

/-- Arm (ii) at the deciding cell of a rank. -/
theorem thresholdBalancedArm_of_polarTilt (rank : ℕ) (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : PolarTiltSelection (thresholdSize rank) rank) : ThresholdBalancedArm rank :=
  balancedArmAt_of_polarTilt hrank hpredecessor htilt

/-! ## Part 6: the ledger of the residual

Three readings that make the residual auditable: its budget is capped by the
pole's own leverage, its zero-tilt instance is unconditional, and its rank-three
instance carries the open frontier. -/

/-- **THE TILT BUDGET IS BELOW THE POLE'S LEVERAGE.**  At the margin the polar
construction supplies, the budget `margin * leverage * (leverage - 1)` never
reaches `leverage`, because the pole's weighted leverage is capped by one. Thus
the residual asks the covering to hold less than ONE unit of squared pairing
against the pole's unit direction, whatever the design and whatever the rank. -/
theorem polarTilt_budget_lt_leverage (design : WeightedDesign size rank) {pole : Fin size}
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole) :
    design.weight pole / (2 * (1 - design.weight pole))
        * (design.atom pole ⬝ᵥ design.atom pole)
        * (design.atom pole ⬝ᵥ design.atom pole - 1)
      < design.atom pole ⬝ᵥ design.atom pole := by
  have hcap := weight_mul_selfDotProduct_le_one design pole
  have hweightPos := design.weight_pos pole
  have hweightLt := weight_lt_one_of_one_lt_selfDotProduct design hlong
  have hden : (0 : ℝ) < 2 * (1 - design.weight pole) := by linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hden]
  nlinarith [hcap, hweightPos, hlong, hweightLt]

/-- **THE ZERO-TILT INSTANCE IS UNCONDITIONAL.**  A covering set orthogonal to
the pole beats every budget, thus it produces a strict dominator with no
residual at all. This is the sharp special case of
`Gtz.posDef_insert_of_polarCover`. -/
theorem posDef_insert_of_orthogonalCover (design : WeightedDesign size rank)
    {pole : Fin size} {covering : Finset (Fin size)} {margin : ℝ}
    (hpoleNotMem : pole ∉ covering)
    (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (hmargin : 0 < margin)
    (hcover : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2)
    (horthogonal : ∀ label ∈ covering, design.atom label ⬝ᵥ design.atom pole = 0) :
    (subsetSum design (insert pole covering) - 1).PosDef := by
  refine posDef_insert_of_polarCover design hpoleNotMem hlong hmargin hcover ?_
  have hzero : ∑ label ∈ covering, (design.atom label ⬝ᵥ design.atom pole) ^ 2 = 0 :=
    Finset.sum_eq_zero fun label hlabel => by rw [horthogonal label hlabel]; ring
  rw [hzero]
  have hleveragePos : 0 < design.atom pole ⬝ᵥ design.atom pole := by linarith
  have hgapPos : 0 < design.atom pole ⬝ᵥ design.atom pole - 1 := by linarith
  exact mul_pos (mul_pos hmargin hleveragePos) hgapPos

/-- **A DESIGN WHOSE COVERING IS ORTHOGONAL TO ITS LONG ATOM IS NOT A TIE.**  No
residual is consumed: the previous rank supplies the cover and the orthogonality
supplies the tilt. -/
theorem not_isTie_of_orthogonalPolarCover (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (design : WeightedDesign size rank)
    {pole : Fin size} (hlong : 1 < design.atom pole ⬝ᵥ design.atom pole)
    (horthogonal : ∀ (covering : Finset (Fin size)), covering.card = rank - 1 →
      pole ∉ covering →
      (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
        probe ⬝ᵥ probe ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
      ∀ label ∈ covering, design.atom label ⬝ᵥ design.atom pole = 0) :
    ¬ IsTie design := by
  classical
  intro htie
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  have hweak : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      probe ⬝ᵥ probe ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2 := by
    intro probe hprobe
    have hfires := hcover probe hprobe
    have hlength : 0 ≤ probe ⬝ᵥ probe := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun coord _ => mul_self_nonneg _
    nlinarith [hfires, hlength, hmarginPos]
  have hposDef := posDef_insert_of_orthogonalCover design hnotMem hlong hmarginPos hcover
    (horthogonal covering hcard hnotMem hweak)
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hnotMem, hcard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-- **THE RANK-THREE LEDGER.**  At rank three the previous rank is the THEOREM
`Gtz.gtz_rank_two`, thus the residual alone carries the deciding cell. This
records what the reduction costs: `Gtz.PolarTiltSelection 6 3` is at least as
strong as the open `Gtz.HingeHoldsAtSize 6 3`, and it replaces five named
residuals by one selection of TWO atoms. -/
theorem hingeHoldsAtSize_six_three_of_polarTilt (htilt : PolarTiltSelection 6 3) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_polarTilt (by norm_num) gtz_rank_two htilt

/-- The whole `(6,3)` cell from the residual alone, through the shipped
window assembly of the rank-three arms. -/
theorem thresholdArms_rank_three_of_polarTilt (htilt : PolarTiltSelection 6 3) :
    ThresholdStressFreeArm 3 ∧ ThresholdBalancedArm 3 ∧ ThresholdDegenerateArm 3 :=
  ⟨thresholdStressFreeArm_of_polarTilt 3 (by norm_num) gtz_rank_two htilt,
    thresholdBalancedArm_of_polarTilt 3 (by norm_num) gtz_rank_two htilt,
    thresholdDegenerateArm_of_polarTilt 3 (by norm_num) gtz_rank_two htilt⟩

/-- **THE COLLAPSE, IN ONE STATEMENT.**  At every rank of at least two, the
previous rank plus the tilt residual give the hinge, all three arms, the
partial-support sub-arm and the repaired degenerate cover together. -/
theorem polarTilt_closes_every_arm (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (htilt : PolarTiltSelection size rank) :
    HingeHoldsAtSize size rank ∧ StressFreeArmAt size rank ∧ BalancedArmAt size rank
      ∧ DegenerateArmAt size rank ∧ BalancedPartialSupportArmAt size rank
      ∧ DegenerateHyperplaneCover size rank :=
  ⟨hingeHoldsAtSize_of_polarTilt hrank hpredecessor htilt,
    stressFreeArmAt_of_polarTilt hrank hpredecessor htilt,
    balancedArmAt_of_polarTilt hrank hpredecessor htilt,
    degenerateArmAt_of_polarTilt hrank hpredecessor htilt,
    balancedPartialSupportArmAt_of_polarTilt hrank hpredecessor htilt,
    degenerateHyperplaneCover_of_polarTilt hrank hpredecessor htilt⟩

/-! ## Part 7: the sharper residual, the refutation, and the deciding cell

The tilt residual prices the coupling by Cauchy-Schwarz. The COUPLING residual
prices it directly, thus it fires wherever the covering's pairings against the
pole cancel. Both are calibrated below by a kernel refutation: at `(5,3)`, where
the hinge is FALSE, the residual is FALSE too. -/

/-- **THE COUPLING RESIDUAL.**  The same selection statement with the coupling
functional bounded directly. It is not comparable with `Gtz.PolarTiltSelection`:
the tilt form reads the covering's total pairing, the coupling form reads the
functional those pairings define, and cancellation helps only the second. -/
def PolarCouplingSelection (size rank : ℕ) : Prop :=
  ∀ (design : WeightedDesign size rank) (pole : Fin size) (covering : Finset (Fin size))
      (margin : ℝ),
    IsPrimitiveDesign design →
    IsTie design →
    1 < design.atom pole ⬝ᵥ design.atom pole →
    0 < margin →
    covering.card = rank - 1 → pole ∉ covering →
    (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
      (1 + margin) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ covering, (design.atom label ⬝ᵥ probe) ^ 2) →
    ∃ (selected : Finset (Fin size)) (couplingBound : ℝ),
      selected.card = rank - 1 ∧ pole ∉ selected
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
      ∧ (∀ probe : Fin rank → ℝ, probe ⬝ᵥ design.atom pole = 0 →
          (∑ label ∈ selected,
              (design.atom label ⬝ᵥ probe) * (design.atom label ⬝ᵥ design.atom pole)) ^ 2
            ≤ couplingBound * (probe ⬝ᵥ probe))
      ∧ couplingBound < margin * (design.atom pole ⬝ᵥ design.atom pole)
          * (design.atom pole ⬝ᵥ design.atom pole - 1)

/-- The hinge from the coupling residual. -/
theorem hingeHoldsAtSize_of_polarCoupling (hrank : 2 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1)) (hcoupling : PolarCouplingSelection size rank) :
    HingeHoldsAtSize size rank := by
  classical
  intro design htie
  by_contra hnoPair
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair
  obtain ⟨pole, hlong⟩ := exists_overshooting_atom design hrank
  obtain ⟨covering, margin, hmarginPos, hcard, hnotMem, hcover⟩ :=
    exists_polarCover_margin hrank hpredecessor design hlong
  obtain ⟨selected, couplingBound, hselCard, hselNotMem, hselCover, hselCoupling, hselBound⟩ :=
    hcoupling design pole covering margin hprimitive htie hlong hmarginPos hcard hnotMem hcover
  have hposDef := posDef_insert_of_polarCoupling design hselNotMem hlong hmarginPos hselCover
    hselCoupling hselBound
  obtain ⟨dominating, hdomCard, hdomPosDef⟩ := exists_card_eq_posDef design
    (by rw [Finset.card_insert_of_notMem hselNotMem, hselCard]; omega) hposDef
  exact htie.2 dominating hdomCard hdomPosDef

/-! ### The calibration: the residual is FALSE below the window floor

`Gtz.not_hingeHoldsAtSize_five_three` refutes the hinge at `(5,3)` with the
diamond, a primitive tie. The predecessor rank at rank three is the THEOREM
`Gtz.gtz_rank_two`, thus the whole chain runs there and the residual takes the
refutation. This is what certifies the reduction is not vacuous: the residual
carries real content, and it carries exactly the content the window floor
supplies. -/

/-- **THE TILT RESIDUAL IS FALSE AT `(5,3)`.**  A cell below the window floor
`2 * rank ≤ size` carries the diamond, a primitive tie, thus no selection
statement that closes the hinge can hold there. -/
theorem not_polarTiltSelection_five_three : ¬ PolarTiltSelection 5 3 :=
  fun htilt => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarTilt (by norm_num) gtz_rank_two htilt)

/-- The tie-free form is refuted at the same cell. -/
theorem not_polarTiltSelectionTieFree_five_three : ¬ PolarTiltSelectionTieFree 5 3 :=
  fun htilt => not_polarTiltSelection_five_three (polarTiltSelection_of_tieFree htilt)

/-- The coupling form is refuted at the same cell. -/
theorem not_polarCouplingSelection_five_three : ¬ PolarCouplingSelection 5 3 :=
  fun hcoupling => not_hingeHoldsAtSize_five_three
    (hingeHoldsAtSize_of_polarCoupling (by norm_num) gtz_rank_two hcoupling)

/-- **THE DIAMOND SPENDS THE WHOLE TILT BUDGET.**  The refutation read
positively: at the diamond every polar cover of every overshooting atom is
tilted past its budget. This is the concrete shape of what the residual has to
exclude at the cells where it is true. -/
theorem diamondDesign_polarCover_is_tilted {pole : Fin 5}
    (hlong : 1 < diamondDesign.atom pole ⬝ᵥ diamondDesign.atom pole) :
    ∃ (covering : Finset (Fin 5)) (margin : ℝ), 0 < margin ∧ covering.card = 2
      ∧ pole ∉ covering
      ∧ (∀ probe : Fin 3 → ℝ, probe ⬝ᵥ diamondDesign.atom pole = 0 →
          (1 + margin) * (probe ⬝ᵥ probe)
            ≤ ∑ label ∈ covering, (diamondDesign.atom label ⬝ᵥ probe) ^ 2)
      ∧ margin * (diamondDesign.atom pole ⬝ᵥ diamondDesign.atom pole)
            * (diamondDesign.atom pole ⬝ᵥ diamondDesign.atom pole - 1)
          ≤ ∑ label ∈ covering, (diamondDesign.atom label ⬝ᵥ diamondDesign.atom pole) ^ 2 :=
  exists_tilted_polarCover_of_isTie (by norm_num) gtz_rank_two diamondDesign
    diamondDesign_isTie hlong

/-! ### The deciding cell of rank three, from the residual alone -/

/-- **THE `(6,3)` CELL FROM ONE RESIDUAL.**  The previous rank at rank three is
the theorem `Gtz.gtz_rank_two`, and the shipped window induction takes the hinge
to the cell. Thus the whole deciding cell of rank three rests on
`Gtz.PolarTiltSelection 6 3` and nothing else. -/
theorem gtzWeighted_six_three_of_polarTilt (htilt : PolarTiltSelection 6 3) :
    GtzWeighted 6 3 := by
  have harms := thresholdArms_rank_three_of_polarTilt htilt
  exact GeneralRankReach.gtzWeighted_six_three_of_arms harms.1 harms.2.1 harms.2.2

/-- All of rank three from the same single residual. -/
theorem gtzWeightedAll_three_of_polarTilt (htilt : PolarTiltSelection 6 3) :
    GtzWeightedAll 3 := by
  have harms := thresholdArms_rank_three_of_polarTilt htilt
  exact GeneralRankReach.gtzWeightedAll_three_of_arms harms.1 harms.2.1 harms.2.2

/-- The same cell from the coupling residual. -/
theorem gtzWeighted_six_three_of_polarCoupling (hcoupling : PolarCouplingSelection 6 3) :
    GtzWeighted 6 3 := by
  have hhinge := hingeHoldsAtSize_of_polarCoupling (rank := 3) (size := 6) (by norm_num)
    gtz_rank_two hcoupling
  exact GeneralRankReach.gtzWeighted_six_three_of_arms (fun design _hfree htie => hhinge design htie)
    (fun design _stressCoeff _hstressNe _hstress _hposSpans _hnegSpans htie => hhinge design htie)
    (fun design _stressCoeff _probe _hstressNe _hprobeNe _hstress _hsupport htie =>
      hhinge design htie)

/-- **THE WHOLE WINDOW OF EVERY RANK, FROM ONE RESIDUAL PER CELL.**  With the
previous rank in scope the ladder needs only the hinge at every cell above the
Naimark floor, and the residual supplies it. -/
theorem gtzWeighted_aboveFloor_of_polarTilt (hrank : 3 ≤ rank)
    (hpredecessor : GtzWeightedAll (rank - 1))
    (htilt : ∀ size : ℕ, 2 * rank ≤ size → PolarTiltSelection size rank)
    (size : ℕ) (hsize : 2 * rank - 1 ≤ size) : GtzWeighted size rank :=
  GeneralRankReach.gtzWeighted_aboveFloor_of_predecessorRank hrank hpredecessor
    (fun cellSize hcell =>
      hingeHoldsAtSize_of_polarTilt (by omega) hpredecessor (htilt cellSize hcell)) size hsize

end Gtz
