/-
# The moment dictionary, and two quadratic-form floors

Every domination statement in the campaign is a statement about ONE quadratic form.
Writing `momentCoord D c x := <g_c, x>^2` for the moment coordinate of an atom at a
probe direction, `quadForm_subsetSum` says a subset sum's quadratic form is the sum
of the moment coordinates it selects, and `dominates_iff_forall_moment_ge` turns
`Gtz.Dominates` into

  the moment image MISSES the open half-space `sum_{c in C} y_c < |x|^2`.

That dictionary is worth pinning down as a theorem rather than a picture, because it
also settles what such a reading can and cannot see: each condition is the minimum of
a LINEAR functional over the moment body, so it depends only on the CONVEX HULL of
the image -- never on the image's topology, its self-intersections, or the dimension
of the domain it came from.

Two floors are then one line each.

* THE UNIFORM LOEWNER FLOOR.  `posSemidef_bound_smul_subsetSum_sub_one`: if every
  weight is at most `bound`, the full unweighted atom sum dominates
  `(1 / bound) . 1`.  This sharpens the shipped `Gtz.posDef_fullExcess` from
  "positive definite" to an explicit constant, and its equality case is the shipped
  equal-weight identity
  `Gtz.subsetSum_univ_eq_size_smul_one_of_weight_eq_sizeInv`.

* THE PAIRING-MASS FLOOR.  `leverage_lt_sum_sq_atomPairing_compl`: wherever the
  co-singleton at an atom STRICTLY dominates, that atom's own leverage is outweighed
  by the squared pairings from it to all the others.  Feed the atom itself into its
  co-singleton's positive-definite gap and the bound falls out.  It is strictly
  stronger than what Parseval gives on its own -- the shipped bilinear identity
  `Gtz.sum_weight_mul_atomPairing_mul_atomPairing` yields only the same bound
  discounted by one minus the atom's share -- and the hypothesis is genuinely needed:
  an orthogonal design has all off-diagonal pairings zero and positive leverages, and
  there its co-singletons are singular.  A `(6,3)` crux carries
  `Gtz.HasStrictlyDominatingCoSingletons`, so the floor holds at all six of its atoms.

Both floors are degree two in the Gram entries, which is what makes them usable by an
algebraic search.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Reduction.NaimarkLeverage
import Gtz.Reduction.RealVolumeFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The moment dictionary -/

/-- The moment coordinate of an atom at a probe direction. -/
noncomputable def momentCoord (design : WeightedDesign size rank) (atomIndex : Fin size)
    (probe : Fin rank → ℝ) : ℝ :=
  (design.atom atomIndex ⬝ᵥ probe) ^ 2

theorem momentCoord_nonneg (design : WeightedDesign size rank) (atomIndex : Fin size)
    (probe : Fin rank → ℝ) : 0 ≤ momentCoord design atomIndex probe :=
  sq_nonneg _

/-- A subset sum's quadratic form is the sum of the moment coordinates it selects. -/
theorem quadForm_subsetSum (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ (subsetSum design selected *ᵥ probe)
      = ∑ atomIndex ∈ selected, momentCoord design atomIndex probe := by
  classical
  simp only [subsetSum, momentCoord]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun atomIndex _ =>
    dotProduct_atomMatrix_mulVec (design.atom atomIndex) probe

theorem quadForm_one (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ probe) = probe ⬝ᵥ probe := by
  rw [Matrix.one_mulVec]

/-- The subset sum's gap is symmetric, so its definiteness is a quadratic-form
condition. -/
theorem transpose_subsetSum_sub_one (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    (subsetSum design selected - 1)ᵀ = subsetSum design selected - 1 := by
  classical
  rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
  congr 1
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  simp only [atomMatrix, Matrix.vecMulVec]
  funext rowIndex colIndex
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  ring

/-- **THE MOMENT DICTIONARY.**  A subset dominates exactly when the moment image
misses the open half-space `sum_{c in C} y_c < |x|^2`.  Both sides are conditions on
the CONVEX HULL of the image, since each is the minimum of a linear functional. -/
theorem dominates_iff_forall_moment_ge (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    Dominates design selected ↔ ∀ probe : Fin rank → ℝ,
      probe ⬝ᵥ probe ≤ ∑ atomIndex ∈ selected, momentCoord design atomIndex probe := by
  classical
  rw [Dominates, posSemidef_iff_quadForm_nonneg _ (transpose_subsetSum_sub_one design selected)]
  constructor
  · intro hall probe
    have hprobe := hall probe
    rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, quadForm_one] at hprobe
    linarith
  · intro hall probe
    have hprobe := hall probe
    rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, quadForm_one]
    linarith

/-- **THE CRUX CONDITION, HALF-SPACE FORM.**  A subset fails to dominate exactly when
the moment image MEETS the corresponding open half-space, and the witness is a single
probe direction. -/
theorem not_dominates_iff_exists_moment_lt (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    ¬ Dominates design selected ↔ ∃ probe : Fin rank → ℝ,
      ∑ atomIndex ∈ selected, momentCoord design atomIndex probe < probe ⬝ᵥ probe := by
  rw [dominates_iff_forall_moment_ge]
  push Not
  rfl

/-! ## The uniform Loewner floor -/

/-- Parseval read as a quadratic form: the weighted moment coordinates sum to the
squared length of the probe, at every probe direction. -/
theorem sum_weight_mul_momentCoord (design : WeightedDesign size rank)
    (probe : Fin rank → ℝ) :
    ∑ atomIndex, design.weight atomIndex * momentCoord design atomIndex probe
      = probe ⬝ᵥ probe := by
  classical
  have hparseval :
      probe ⬝ᵥ ((∑ atomIndex, design.weight atomIndex • atomMatrix (design.atom atomIndex))
          *ᵥ probe)
        = probe ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ probe) := by
    rw [design.isParseval]
  rw [Matrix.sum_mulVec, dotProduct_sum, Matrix.one_mulVec] at hparseval
  rw [← hparseval]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
  rfl

/-- **THE UNIFORM FLOOR.**  If every weight is at most `bound` then the full unweighted
atom sum satisfies `|x|^2 <= bound * sum_c <g_c, x>^2` at every probe.  One line from
Parseval: the weights are being replaced by their common cap. -/
theorem dotProduct_le_bound_mul_quadForm_univ (design : WeightedDesign size rank)
    {bound : ℝ} (hbound : ∀ atomIndex, design.weight atomIndex ≤ bound)
    (probe : Fin rank → ℝ) :
    probe ⬝ᵥ probe ≤ bound * (probe ⬝ᵥ (subsetSum design Finset.univ *ᵥ probe)) := by
  classical
  rw [quadForm_subsetSum, ← sum_weight_mul_momentCoord design probe, Finset.mul_sum]
  refine Finset.sum_le_sum fun atomIndex _ => ?_
  exact mul_le_mul_of_nonneg_right (hbound atomIndex) (momentCoord_nonneg design atomIndex probe)

/-- **THE FLOOR IN LOEWNER FORM.**  `bound . subsetSum univ >= 1`.  Sharper than the
shipped `Gtz.posDef_fullExcess`, which gives positive definiteness with no constant;
its equality case is the shipped equal-weight identity
`Gtz.subsetSum_univ_eq_size_smul_one_of_weight_eq_sizeInv`. -/
theorem posSemidef_bound_smul_subsetSum_sub_one (design : WeightedDesign size rank)
    {bound : ℝ} (hbound : ∀ atomIndex, design.weight atomIndex ≤ bound) :
    (bound • subsetSum design Finset.univ - 1).PosSemidef := by
  classical
  have hsymmetric : (bound • subsetSum design Finset.univ - 1)ᵀ
      = bound • subsetSum design Finset.univ - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, subsetSum,
      Matrix.transpose_sum]
    congr 2
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    simp only [atomMatrix, Matrix.vecMulVec]
    funext rowIndex colIndex
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    ring
  rw [posSemidef_iff_quadForm_nonneg _ hsymmetric]
  intro probe
  have hfloor := dotProduct_le_bound_mul_quadForm_univ design hbound probe
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    quadForm_one]
  linarith

/-! ## The pairing-mass floor -/

/-- **THE PAIRING-MASS FLOOR.**  Wherever the co-singleton at an atom STRICTLY
dominates, the squared pairings from that atom to all the others outweigh its own
leverage.  The proof feeds the atom itself into its co-singleton's positive-definite
gap; the strictness of the co-singleton is what makes the bound strict, and it cannot
be dropped -- an orthogonal design has vanishing off-diagonal pairings and positive
leverages, and there the co-singleton is singular. -/
theorem leverage_lt_sum_sq_atomPairing_compl (design : WeightedDesign size rank)
    (atomIndex : Fin size)
    (hcoSingleton : (subsetSum design ({atomIndex}ᶜ : Finset (Fin size)) - 1).PosDef)
    (hnonzero : design.atom atomIndex ≠ 0) :
    leverageOf (design.atom atomIndex)
      < ∑ otherIndex ∈ ({atomIndex}ᶜ : Finset (Fin size)),
          (design.atom atomIndex ⬝ᵥ design.atom otherIndex) ^ 2 := by
  classical
  have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hcoSingleton).2 hnonzero
  simp only [star_trivial] at hpositive
  rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_subsetSum, Matrix.one_mulVec] at hpositive
  have hself : design.atom atomIndex ⬝ᵥ design.atom atomIndex
      = leverageOf (design.atom atomIndex) := by
    simp only [leverageOf, dotProduct, pow_two]
  have hswap : ∀ otherIndex, momentCoord design otherIndex (design.atom atomIndex)
      = (design.atom atomIndex ⬝ᵥ design.atom otherIndex) ^ 2 :=
    fun otherIndex => by rw [momentCoord, dotProduct_comm]
  simp only [hswap] at hpositive
  rw [hself] at hpositive
  linarith

/-- The design-level reading: at a design with strictly dominating co-singletons the
floor holds at EVERY atom.  A `(6,3)` crux carries exactly that field. -/
theorem forall_leverage_lt_sum_sq_atomPairing_compl (design : WeightedDesign size rank)
    (hcoSingletons : HasStrictlyDominatingCoSingletons design)
    (hnonzero : ∀ atomIndex, design.atom atomIndex ≠ 0) (atomIndex : Fin size) :
    leverageOf (design.atom atomIndex)
      < ∑ otherIndex ∈ ({atomIndex}ᶜ : Finset (Fin size)),
          (design.atom atomIndex ⬝ᵥ design.atom otherIndex) ^ 2 :=
  leverage_lt_sum_sq_atomPairing_compl design atomIndex (hcoSingletons atomIndex)
    (hnonzero atomIndex)

end Gtz
