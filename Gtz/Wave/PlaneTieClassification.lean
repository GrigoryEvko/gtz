import Gtz.Wave.PlanePairCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The three-atom plane tie classification

A TIE of the plane at mass one is a frame with positive weights of total one
and no strictly dominating pair.  This module classifies the three-atom ties
completely.  The classification is an equivalence with one closed form.

The engine is one determinant identity.  For a plane frame of three atoms the
complement of two outer products is the third outer product, and the third
outer product is singular.  Thus the squared dot of every pair equals the
product of the two mass deficits: `(b_x ⬝ᵥ b_y)^2 = (1 - |b_x|^2)(1 - |b_y|^2)`.

The identity makes the tie weights visible.  The weight `t_y = 2 l_y - 1`
turns the pair determinant reading `(l_x - t_x)(l_y - t_y)` into exactly
`(1 - l_x)(1 - l_y)`, so EVERY pair sits at the certificate boundary at once.
The mass law makes these weights total one with no computation.  The family
generalizes the trine of `Gtz.planeTrineAtom`, which is its equilateral point.

The converse is the classification: a three-atom mass-one design with no
strictly dominating pair carries exactly these weights.  The proof is a
sandwich.  Write `w_y = l_y - t_y` and `v_y = 1 - l_y`.  Both vectors total
one, the failed strictness reads `w_x w_y ≤ v_x v_y` at every pair, and the
scalar ladder forces `w = v` slot by slot.

## The declarations

* `Gtz.plane_dot_self_pos` — a nonzero plane vector has positive energy.
* `Gtz.planePairStrict_of_certificate` — the classification-facing alias of
  the canonical strict pair certificate from `PlanePairCriterion`.
* `Gtz.scalar_of_not_planePairStrict` — the scalar disjunction of a failed
  strict test, by contraposition from the canonical exact pair criterion.
* `Gtz.plane_three_pair_det` — **THE PAIR DETERMINANT IDENTITY.**  At three
  atoms the squared dot of a pair is the product of the two mass deficits.
* `Gtz.plane_three_wedge_sq` — **THE WEDGE LAW.**  The squared wedge of a
  pair is the pair mass total minus one.
* `Gtz.planeTieWeight`, `Gtz.planeTieWeight_sum`, `Gtz.planeTieWeight_pos`,
  `Gtz.plane_three_mass_lt_one`, `Gtz.planeTieWeight_lt_one` — the closed
  form `t_y = 2 l_y - 1` and its range.
* `Gtz.planeTie_pair_det_eq` — every pair of the family sits at the
  certificate boundary exactly.
* `Gtz.planeTie_pair_dominates` — every pair of the family dominates weakly.
* `Gtz.planeTie_pair_independent` — the family is parallel free.
* `Gtz.planeTieProbe` with `Gtz.planeTieProbe_read_left`,
  `Gtz.planeTieProbe_read_right`, `Gtz.planeTieProbe_energy`,
  `Gtz.planeTieProbe_certificate`, `Gtz.planeTieProbe_ne_zero` — **THE KERNEL
  PROBE.**  The explicit direction that every pair of the family fails to
  dominate strictly.
* `Gtz.planeTie_pair_not_strict` — no pair of the family is strict.
* `Gtz.tie_scalar_leverage_lt_one`, `Gtz.tie_scalar_weight_pos`,
  `Gtz.tie_scalar_slot_le`, `Gtz.tie_scalar_classification` — the scalar
  ladder of the converse.
* `Gtz.plane_three_classification` — **THE CLASSIFICATION.**  No strict pair
  at mass one forces the closed-form weights.
* `Gtz.plane_three_tie_iff` — **THE EQUIVALENCE.**  At a three-atom plane
  frame with positive mass-one weights, the absence of a strict pair IS the
  closed form `t_y = 2 l_y - 1`.
* `Gtz.exists_plane_three_tie_iff` — **THE EXISTENCE CLASSIFICATION.**  The
  open tie simplex is inhabited exactly when all three masses exceed one half.
* `Gtz.plane_three_tie_unique` — the open tie simplex contains at most one
  weight vector.
* `Gtz.plane_three_pair_dominates_of_tie` — every pair of a three-atom tie
  weakly dominates: the entire family lies on the certificate boundary.
* `Gtz.planeTie_w_identity` — the W reading of the family: the sum of
  `2 l_y t_y - t_y^2` equals the mass total minus one.
* `Gtz.planeTrine_tieWeight` — the trine carries the closed-form weights, so
  the landed sharpness calibration is the equilateral point of this family.
* `Gtz.quarter_trace_core` — **THE QUARTER-TRACE CORE.**  A two-by-two
  operator between zero and the identity has its squared Frobenius reading
  below its trace, division free.
* `Gtz.plane_w_engine` — **THE W ENGINE, at every slot count.**  At mass one
  an active set with positive budgets, an inert complement and no strict pair
  obeys `Σ (2 l t - t^2) ≤ Σ l - 1` over the active slots.
* `Gtz.plane_plucker_first`, `Gtz.plane_plucker_second`,
  `Gtz.plane_plucker_third` — **THE PLANE PLÜCKER IDENTITIES.**  The three
  perfect matchings of four plane vectors differ by products of wedges.
* `Gtz.plane_four_allTied_parallel`,
  `Gtz.plane_four_allTied_exists_parallel` — **THE FOUR-ATOM KILL.**  Four
  atoms of positive budget are never all tied without a parallel pair, so an
  all-tied family never carries four distinct lines.
* `Gtz.planeTie_allTied_reading` — the three-atom family IS all tied, so the
  four-atom kill is sharp at exactly three lines.

The tie set of a three-atom plane frame in the open weight simplex is
therefore EMPTY when some mass sits at one half or less, and it is EXACTLY
ONE POINT when every mass exceeds one half.  The probes of 2026-08-15
confirmed both statements at machine precision, with the uniqueness scan at
three hundred configurations per side.
-/

namespace Gtz

open scoped BigOperators Matrix

/-! ## Layer 1 — the strict certificate and its refusal -/

/-- A nonzero plane vector has positive energy.  This coordinate-free name is
kept as part of the tie-classification API; the exact pair criterion exposes
the equivalent coordinate statement as `planeProbe_energy_pos`. -/
theorem plane_dot_self_pos {vec : Fin 2 → ℝ} (hne : vec ≠ 0) : 0 < vec ⬝ᵥ vec := by
  rw [dot_fin_two]
  simpa only [pow_two] using planeProbe_energy_pos hne

/-- **THE CLASSIFICATION-FACING STRICT CERTIFICATE.**  This preserves the
original tie-classification interface while delegating the mathematics to the
stronger exact criterion in `PlanePairCriterion`. -/
theorem planePairStrict_of_certificate {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo : ℝ}
    (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hshiftOne : scaleOne < atomOne ⬝ᵥ atomOne)
    (hshiftTwo : scaleTwo < atomTwo ⬝ᵥ atomTwo)
    (hdet : (atomOne ⬝ᵥ atomTwo) ^ 2
      < (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)) :
    PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo :=
  planePairDominatesStrict_of_certificate hposOne hposTwo hshiftOne hshiftTwo hdet

/-- **THE SCALAR DISJUNCTION OF A FAILED STRICT TEST.**  At positive scales a
pair that does not dominate strictly satisfies one of the three scalar
refusals: a blocked budget on either slot, or the determinant reading at or
below the squared dot. -/
theorem scalar_of_not_planePairStrict {atomOne atomTwo : Fin 2 → ℝ}
    {scaleOne scaleTwo : ℝ} (hposOne : 0 < scaleOne) (hposTwo : 0 < scaleTwo)
    (hns : ¬ PlanePairDominatesStrict atomOne atomTwo scaleOne scaleTwo) :
    atomOne ⬝ᵥ atomOne ≤ scaleOne ∨ atomTwo ⬝ᵥ atomTwo ≤ scaleTwo
      ∨ (atomOne ⬝ᵥ atomOne - scaleOne) * (atomTwo ⬝ᵥ atomTwo - scaleTwo)
        ≤ (atomOne ⬝ᵥ atomTwo) ^ 2 := by
  by_contra hall
  simp only [not_or, not_le] at hall
  obtain ⟨hOne, hTwo, hDet⟩ := hall
  exact hns (planePairStrict_of_certificate hposOne hposTwo hOne hTwo hDet)

/-! ## Layer 2 — the pair determinant identity at three atoms -/

/-- The scalar core of the pair determinant identity.  Three plane vectors
whose coordinates satisfy the three entry laws of a frame satisfy the
deficit-product law at the first pair. -/
theorem pair_det_core {a0 a1 b0 b1 c0 c1 : ℝ}
    (hfirst : a0 * a0 + b0 * b0 + c0 * c0 = 1)
    (hsecond : a1 * a1 + b1 * b1 + c1 * c1 = 1)
    (hcross : a0 * a1 + b0 * b1 + c0 * c1 = 0) :
    (a0 * b0 + a1 * b1) ^ 2 = (1 - (a0 * a0 + a1 * a1)) * (1 - (b0 * b0 + b1 * b1)) := by
  have hzero : c0 * c0 = 1 - a0 * a0 - b0 * b0 := by linarith
  have hone : c1 * c1 = 1 - a1 * a1 - b1 * b1 := by linarith
  have hc : c0 * c1 = -(a0 * a1 + b0 * b1) := by linarith
  have hbridge : (a0 * a1 + b0 * b1) ^ 2 = (1 - a0 * a0 - b0 * b0) * (1 - a1 * a1 - b1 * b1) := by
    calc (a0 * a1 + b0 * b1) ^ 2 = (c0 * c1) ^ 2 := by rw [hc]; ring
    _ = (c0 * c0) * (c1 * c1) := by ring
    _ = (1 - a0 * a0 - b0 * b0) * (1 - a1 * a1 - b1 * b1) := by rw [hzero, hone]
  linear_combination hbridge

/-- The scalar core of the wedge law.  The squared wedge of the first pair is
the pair coordinate total minus one. -/
theorem wedge_core {a0 a1 b0 b1 c0 c1 : ℝ}
    (hfirst : a0 * a0 + b0 * b0 + c0 * c0 = 1)
    (hsecond : a1 * a1 + b1 * b1 + c1 * c1 = 1)
    (hcross : a0 * a1 + b0 * b1 + c0 * c1 = 0) :
    (a0 * b1 - a1 * b0) ^ 2 = (a0 * a0 + a1 * a1) + (b0 * b0 + b1 * b1) - 1 := by
  have hzero : c0 * c0 = 1 - a0 * a0 - b0 * b0 := by linarith
  have hone : c1 * c1 = 1 - a1 * a1 - b1 * b1 := by linarith
  have hc : c0 * c1 = -(a0 * a1 + b0 * b1) := by linarith
  have hbridge : (a0 * a1 + b0 * b1) ^ 2 = (1 - a0 * a0 - b0 * b0) * (1 - a1 * a1 - b1 * b1) := by
    calc (a0 * a1 + b0 * b1) ^ 2 = (c0 * c1) ^ 2 := by rw [hc]; ring
    _ = (c0 * c0) * (c1 * c1) := by ring
    _ = (1 - a0 * a0 - b0 * b0) * (1 - a1 * a1 - b1 * b1) := by rw [hzero, hone]
  linear_combination (-1 : ℝ) * hbridge

/-- The pair determinant identity at the first pair. -/
theorem plane_three_pair_det_first {atom : Fin 3 → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) :
    (atom 0 ⬝ᵥ atom 1) ^ 2
      = (1 - atom 0 ⬝ᵥ atom 0) * (1 - atom 1 ⬝ᵥ atom 1) := by
  have hfirst := hframe.sum_first_sq
  have hsecond := hframe.sum_second_sq
  have hcross := hframe.sum_cross
  rw [Fin.sum_univ_three] at hfirst hsecond hcross
  simp only [dot_fin_two]
  exact pair_det_core (c0 := atom 2 0) (c1 := atom 2 1) hfirst hsecond hcross

/-- The pair determinant identity at the second pair. -/
theorem plane_three_pair_det_second {atom : Fin 3 → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) :
    (atom 0 ⬝ᵥ atom 2) ^ 2
      = (1 - atom 0 ⬝ᵥ atom 0) * (1 - atom 2 ⬝ᵥ atom 2) := by
  have hfirst := hframe.sum_first_sq
  have hsecond := hframe.sum_second_sq
  have hcross := hframe.sum_cross
  rw [Fin.sum_univ_three] at hfirst hsecond hcross
  simp only [dot_fin_two]
  exact pair_det_core (c0 := atom 1 0) (c1 := atom 1 1)
    (by linarith) (by linarith) (by linarith)

/-- The pair determinant identity at the third pair. -/
theorem plane_three_pair_det_third {atom : Fin 3 → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) :
    (atom 1 ⬝ᵥ atom 2) ^ 2
      = (1 - atom 1 ⬝ᵥ atom 1) * (1 - atom 2 ⬝ᵥ atom 2) := by
  have hfirst := hframe.sum_first_sq
  have hsecond := hframe.sum_second_sq
  have hcross := hframe.sum_cross
  rw [Fin.sum_univ_three] at hfirst hsecond hcross
  simp only [dot_fin_two]
  exact pair_det_core (c0 := atom 0 0) (c1 := atom 0 1)
    (by linarith) (by linarith) (by linarith)

/-- **THE PAIR DETERMINANT IDENTITY.**  At a plane frame of three atoms the
squared dot of every pair equals the product of the two mass deficits.  The
complement of two outer products is the third outer product, and a single
outer product is singular. -/
theorem plane_three_pair_det {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {x y : Fin 3} (hxy : x ≠ y) :
    (atom x ⬝ᵥ atom y) ^ 2
      = (1 - atom x ⬝ᵥ atom x) * (1 - atom y ⬝ᵥ atom y) := by
  fin_cases x <;> fin_cases y
  · exact absurd rfl hxy
  · exact plane_three_pair_det_first hframe
  · exact plane_three_pair_det_second hframe
  · show (atom 1 ⬝ᵥ atom 0) ^ 2 = (1 - atom 1 ⬝ᵥ atom 1) * (1 - atom 0 ⬝ᵥ atom 0)
    have hkey := plane_three_pair_det_first hframe
    simp only [dot_fin_two] at hkey ⊢
    linear_combination hkey
  · exact absurd rfl hxy
  · exact plane_three_pair_det_third hframe
  · show (atom 2 ⬝ᵥ atom 0) ^ 2 = (1 - atom 2 ⬝ᵥ atom 2) * (1 - atom 0 ⬝ᵥ atom 0)
    have hkey := plane_three_pair_det_second hframe
    simp only [dot_fin_two] at hkey ⊢
    linear_combination hkey
  · show (atom 2 ⬝ᵥ atom 1) ^ 2 = (1 - atom 2 ⬝ᵥ atom 2) * (1 - atom 1 ⬝ᵥ atom 1)
    have hkey := plane_three_pair_det_third hframe
    simp only [dot_fin_two] at hkey ⊢
    linear_combination hkey
  · exact absurd rfl hxy

/-- **THE WEDGE LAW.**  At a plane frame of three atoms the squared wedge of
every pair is the pair mass total minus one. -/
theorem plane_three_wedge_sq {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {x y : Fin 3} (hxy : x ≠ y) :
    (atom x 0 * atom y 1 - atom x 1 * atom y 0) ^ 2
      = (atom x ⬝ᵥ atom x) + (atom y ⬝ᵥ atom y) - 1 := by
  have hfirst := hframe.sum_first_sq
  have hsecond := hframe.sum_second_sq
  have hcross := hframe.sum_cross
  rw [Fin.sum_univ_three] at hfirst hsecond hcross
  fin_cases x <;> fin_cases y
  · exact absurd rfl hxy
  · show (atom 0 0 * atom 1 1 - atom 0 1 * atom 1 0) ^ 2
      = (atom 0 ⬝ᵥ atom 0) + (atom 1 ⬝ᵥ atom 1) - 1
    simp only [dot_fin_two]
    exact wedge_core (c0 := atom 2 0) (c1 := atom 2 1) hfirst hsecond hcross
  · show (atom 0 0 * atom 2 1 - atom 0 1 * atom 2 0) ^ 2
      = (atom 0 ⬝ᵥ atom 0) + (atom 2 ⬝ᵥ atom 2) - 1
    simp only [dot_fin_two]
    exact wedge_core (c0 := atom 1 0) (c1 := atom 1 1)
      (by linarith) (by linarith) (by linarith)
  · show (atom 1 0 * atom 0 1 - atom 1 1 * atom 0 0) ^ 2
      = (atom 1 ⬝ᵥ atom 1) + (atom 0 ⬝ᵥ atom 0) - 1
    simp only [dot_fin_two]
    exact wedge_core (c0 := atom 2 0) (c1 := atom 2 1)
      (by linarith) (by linarith) (by linarith)
  · exact absurd rfl hxy
  · show (atom 1 0 * atom 2 1 - atom 1 1 * atom 2 0) ^ 2
      = (atom 1 ⬝ᵥ atom 1) + (atom 2 ⬝ᵥ atom 2) - 1
    simp only [dot_fin_two]
    exact wedge_core (c0 := atom 0 0) (c1 := atom 0 1)
      (by linarith) (by linarith) (by linarith)
  · show (atom 2 0 * atom 0 1 - atom 2 1 * atom 0 0) ^ 2
      = (atom 2 ⬝ᵥ atom 2) + (atom 0 ⬝ᵥ atom 0) - 1
    simp only [dot_fin_two]
    exact wedge_core (c0 := atom 1 0) (c1 := atom 1 1)
      (by linarith) (by linarith) (by linarith)
  · show (atom 2 0 * atom 1 1 - atom 2 1 * atom 1 0) ^ 2
      = (atom 2 ⬝ᵥ atom 2) + (atom 1 ⬝ᵥ atom 1) - 1
    simp only [dot_fin_two]
    exact wedge_core (c0 := atom 0 0) (c1 := atom 0 1)
      (by linarith) (by linarith) (by linarith)
  · exact absurd rfl hxy

/-! ## Layer 3 — the all-tied family -/

/-- **THE TIE WEIGHT.**  The closed-form weight of the all-tied family: twice
the mass minus one. -/
def planeTieWeight (atom : Fin 3 → (Fin 2 → ℝ)) (slot : Fin 3) : ℝ :=
  2 * (atom slot ⬝ᵥ atom slot) - 1

/-- The tie weights total one.  The mass law makes the cotangent identity of
the angle picture a triviality. -/
theorem planeTieWeight_sum {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom) :
    (∑ slot, planeTieWeight atom slot) = 1 := by
  have hmass := hframe.sum_mass
  rw [Fin.sum_univ_three] at hmass
  simp only [planeTieWeight]
  rw [Fin.sum_univ_three]
  linarith

/-- A mass above one half makes the tie weight positive. -/
theorem planeTieWeight_pos {atom : Fin 3 → (Fin 2 → ℝ)}
    (hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot) (slot : Fin 3) :
    0 < planeTieWeight atom slot := by
  simp only [planeTieWeight]
  linarith [hhalf slot]

/-- When every mass exceeds one half, every mass sits strictly below one. -/
theorem plane_three_mass_lt_one {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot) (slot : Fin 3) :
    atom slot ⬝ᵥ atom slot < 1 := by
  have hmass := hframe.sum_mass
  rw [Fin.sum_univ_three] at hmass
  fin_cases slot
  · show atom 0 ⬝ᵥ atom 0 < 1
    linarith [hhalf 1, hhalf 2]
  · show atom 1 ⬝ᵥ atom 1 < 1
    linarith [hhalf 0, hhalf 2]
  · show atom 2 ⬝ᵥ atom 2 < 1
    linarith [hhalf 0, hhalf 1]

/-- The tie weight sits strictly below one. -/
theorem planeTieWeight_lt_one {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot) (slot : Fin 3) :
    planeTieWeight atom slot < 1 := by
  simp only [planeTieWeight]
  linarith [plane_three_mass_lt_one hframe hhalf slot]

/-- **THE CERTIFICATE BOUNDARY.**  At the tie weights the determinant reading
of every pair is an exact equality: the shifted masses reproduce the two
deficits of the pair determinant identity. -/
theorem planeTie_pair_det_eq {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {x y : Fin 3} (hxy : x ≠ y) :
    (atom x ⬝ᵥ atom y) ^ 2
      = (atom x ⬝ᵥ atom x - planeTieWeight atom x)
        * (atom y ⬝ᵥ atom y - planeTieWeight atom y) := by
  have hdet := plane_three_pair_det hframe hxy
  simp only [planeTieWeight]
  linear_combination hdet

/-- Every pair of the family dominates weakly. -/
theorem planeTie_pair_dominates {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot) {x y : Fin 3} (hxy : x ≠ y) :
    PlanePairDominates (atom x) (atom y) (planeTieWeight atom x) (planeTieWeight atom y) := by
  apply planePairDominates_of_certificate
  · exact planeTieWeight_pos hhalf x
  · exact planeTieWeight_pos hhalf y
  · simp only [planeTieWeight]
    nlinarith [hhalf x, hhalf y, plane_three_mass_lt_one hframe hhalf x,
      plane_three_mass_lt_one hframe hhalf y]
  · exact le_of_eq (planeTie_pair_det_eq hframe hxy)

/-- The family is parallel free: every pair reads a strict Cauchy-Schwarz. -/
theorem planeTie_pair_independent {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot) {x y : Fin 3} (hxy : x ≠ y) :
    (atom x ⬝ᵥ atom y) ^ 2 < (atom x ⬝ᵥ atom x) * (atom y ⬝ᵥ atom y) := by
  have hdet := plane_three_pair_det hframe hxy
  rw [hdet]
  nlinarith [hhalf x, hhalf y]

/-! ## Layer 4 — the kernel probe -/

/-- **THE KERNEL PROBE.**  The direction on which the pair matrix of the
family reads exactly the identity. -/
def planeTieProbe (atom : Fin 3 → (Fin 2 → ℝ)) (x y : Fin 3) : Fin 2 → ℝ :=
  fun index =>
    (atom x ⬝ᵥ atom y) * atom x index - (1 - atom x ⬝ᵥ atom x) * atom y index

/-- The first read of the kernel probe, division free. -/
theorem planeTieProbe_read_left (atom : Fin 3 → (Fin 2 → ℝ)) (x y : Fin 3) :
    atom x ⬝ᵥ planeTieProbe atom x y
      = (atom x ⬝ᵥ atom y) * (2 * (atom x ⬝ᵥ atom x) - 1) := by
  simp only [planeTieProbe, dot_fin_two]
  ring

/-- The second read of the kernel probe, division free. -/
theorem planeTieProbe_read_right (atom : Fin 3 → (Fin 2 → ℝ)) (x y : Fin 3) :
    atom y ⬝ᵥ planeTieProbe atom x y
      = (atom x ⬝ᵥ atom y) ^ 2 - (1 - atom x ⬝ᵥ atom x) * (atom y ⬝ᵥ atom y) := by
  simp only [planeTieProbe, dot_fin_two]
  ring

/-- The energy of the kernel probe, division free. -/
theorem planeTieProbe_energy (atom : Fin 3 → (Fin 2 → ℝ)) (x y : Fin 3) :
    planeTieProbe atom x y ⬝ᵥ planeTieProbe atom x y
      = (atom x ⬝ᵥ atom y) ^ 2 * (atom x ⬝ᵥ atom x)
        - 2 * (atom x ⬝ᵥ atom y) ^ 2 * (1 - atom x ⬝ᵥ atom x)
        + (1 - atom x ⬝ᵥ atom x) ^ 2 * (atom y ⬝ᵥ atom y) := by
  simp only [planeTieProbe, dot_fin_two]
  ring

/-- **THE EQUALITY AT THE PROBE.**  On the kernel probe the pair energy of the
family equals the scaled probe energy exactly. -/
theorem planeTieProbe_certificate {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {x y : Fin 3} (hxy : x ≠ y) :
    planeTieWeight atom y * (atom x ⬝ᵥ planeTieProbe atom x y) ^ 2
        + planeTieWeight atom x * (atom y ⬝ᵥ planeTieProbe atom x y) ^ 2
      = planeTieWeight atom x * planeTieWeight atom y
        * (planeTieProbe atom x y ⬝ᵥ planeTieProbe atom x y) := by
  have hdet := plane_three_pair_det hframe hxy
  rw [planeTieProbe_read_left, planeTieProbe_read_right, planeTieProbe_energy]
  simp only [planeTieWeight]
  linear_combination ((2 * (atom x ⬝ᵥ atom x) - 1)
    * ((atom x ⬝ᵥ atom y) ^ 2 - (1 - atom x ⬝ᵥ atom x) * (atom y ⬝ᵥ atom y))) * hdet

/-- The kernel probe is nonzero on the admissible family. -/
theorem planeTieProbe_ne_zero {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot) {x y : Fin 3} (hxy : x ≠ y) :
    planeTieProbe atom x y ≠ 0 := by
  intro hzero
  have henergy : planeTieProbe atom x y ⬝ᵥ planeTieProbe atom x y = 0 := by
    rw [hzero]
    simp
  rw [planeTieProbe_energy] at henergy
  have hdet := plane_three_pair_det hframe hxy
  have hltx := plane_three_mass_lt_one hframe hhalf x
  have hlty := plane_three_mass_lt_one hframe hhalf y
  have hfact : (1 - atom x ⬝ᵥ atom x)
      * ((2 * (atom x ⬝ᵥ atom x) - 1) * (1 - atom y ⬝ᵥ atom y)
        + (2 * (atom y ⬝ᵥ atom y) - 1) * (1 - atom x ⬝ᵥ atom x)) = 0 := by
    linear_combination henergy - (3 * (atom x ⬝ᵥ atom x) - 2) * hdet
  have hbracket : 0 < (2 * (atom x ⬝ᵥ atom x) - 1) * (1 - atom y ⬝ᵥ atom y)
      + (2 * (atom y ⬝ᵥ atom y) - 1) * (1 - atom x ⬝ᵥ atom x) := by
    have honePos : 0 < (2 * (atom x ⬝ᵥ atom x) - 1) * (1 - atom y ⬝ᵥ atom y) :=
      mul_pos (by linarith [hhalf x]) (by linarith)
    have htwoPos : 0 < (2 * (atom y ⬝ᵥ atom y) - 1) * (1 - atom x ⬝ᵥ atom x) :=
      mul_pos (by linarith [hhalf y]) (by linarith)
    linarith
  have hprod : 0 < (1 - atom x ⬝ᵥ atom x)
      * ((2 * (atom x ⬝ᵥ atom x) - 1) * (1 - atom y ⬝ᵥ atom y)
        + (2 * (atom y ⬝ᵥ atom y) - 1) * (1 - atom x ⬝ᵥ atom x)) :=
    mul_pos (by linarith) hbracket
  linarith [hfact, hprod]

/-- **NO PAIR OF THE FAMILY IS STRICT.**  The kernel probe defeats the strict
test at every pair. -/
theorem planeTie_pair_not_strict {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    (hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot) {x y : Fin 3} (hxy : x ≠ y) :
    ¬ PlanePairDominatesStrict (atom x) (atom y)
        (planeTieWeight atom x) (planeTieWeight atom y) := by
  intro hstrict
  have hviol := hstrict (planeTieProbe atom x y) (planeTieProbe_ne_zero hframe hhalf hxy)
  have hcert := planeTieProbe_certificate hframe hxy
  linarith [hviol, hcert]

/-! ## Layer 5 — the scalar ladder of the converse -/

/-- The first rung: no leverage sits at the cap.  A slot of mass one is
orthogonal to the two others, the two refusals over-weight them, and the mass
budget breaks. -/
theorem tie_scalar_leverage_lt_one {l0 l1 l2 t0 t1 t2 d01 d02 : ℝ}
    (hsuml : l0 + l1 + l2 = 2) (hsumt : t0 + t1 + t2 = 1)
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hle : l0 ≤ 1)
    (hd01 : d01 ^ 2 = (1 - l0) * (1 - l1))
    (hd02 : d02 ^ 2 = (1 - l0) * (1 - l2))
    (hp01 : l0 ≤ t0 ∨ l1 ≤ t1 ∨ (l0 - t0) * (l1 - t1) ≤ d01 ^ 2)
    (hp02 : l0 ≤ t0 ∨ l2 ≤ t2 ∨ (l0 - t0) * (l2 - t2) ≤ d02 ^ 2) :
    l0 < 1 := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    have hz01 : d01 ^ 2 = 0 := by rw [hd01, ← heq]; ring
    have hz02 : d02 ^ 2 = 0 := by rw [hd02, ← heq]; ring
    have hw0 : 0 < l0 - t0 := by linarith
    have hb1 : l1 ≤ t1 := by
      rcases hp01 with h | h | h
      · linarith
      · exact h
      · rw [hz01] at h
        nlinarith [hw0, h]
    have hb2 : l2 ≤ t2 := by
      rcases hp02 with h | h | h
      · linarith
      · exact h
      · rw [hz02] at h
        nlinarith [hw0, h]
    linarith [heq]
  · exact hlt

/-- The second rung: every weight sits strictly below its leverage.  An
over-weighted slot starves the other two, and their pair turns strict. -/
theorem tie_scalar_weight_pos {l0 l1 l2 t0 t1 t2 d12 : ℝ}
    (hsuml : l0 + l1 + l2 = 2) (hsumt : t0 + t1 + t2 = 1)
    (_ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hl1 : l1 < 1) (hl2 : l2 < 1)
    (hd12 : d12 ^ 2 = (1 - l1) * (1 - l2))
    (hp12 : l1 ≤ t1 ∨ l2 ≤ t2 ∨ (l1 - t1) * (l2 - t2) ≤ d12 ^ 2) :
    t0 < l0 := by
  by_contra hng
  rw [not_lt] at hng
  rcases hp12 with h | h | h
  · linarith
  · linarith
  · rw [hd12] at h
    have hgapOne : 0 < (l1 - t1) - (1 - l2) := by linarith
    have hgapTwo : 0 < (l2 - t2) - (1 - l1) := by linarith
    nlinarith [h, mul_pos hgapOne hgapTwo,
      mul_pos (show (0 : ℝ) < 1 - l1 by linarith) hgapOne,
      mul_pos (show (0 : ℝ) < 1 - l2 by linarith) hgapTwo]

/-- The third rung: the completed square.  Both pair refusals at one slot cap
its weight deficit by its mass deficit. -/
theorem tie_scalar_slot_le {l0 l1 l2 t0 t1 t2 : ℝ}
    (hsuml : l0 + l1 + l2 = 2) (hsumt : t0 + t1 + t2 = 1)
    (ht0 : 0 < t0)
    (hq01 : (l0 - t0) * (l1 - t1) ≤ (1 - l0) * (1 - l1))
    (hq02 : (l0 - t0) * (l2 - t2) ≤ (1 - l0) * (1 - l2)) :
    l0 - t0 ≤ 1 - l0 := by
  by_contra hng
  rw [not_le] at hng
  nlinarith [hq01, hq02, mul_pos (sub_pos.mpr hng) ht0, hsuml, hsumt]

/-- **THE SCALAR CLASSIFICATION.**  Six masses and weights with the frame
sums, the three deficit-product identities and the three strict-test refusals
force the closed form on every slot. -/
theorem tie_scalar_classification {l0 l1 l2 t0 t1 t2 d01 d02 d12 : ℝ}
    (hsuml : l0 + l1 + l2 = 2) (hsumt : t0 + t1 + t2 = 1)
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hle0 : l0 ≤ 1) (hle1 : l1 ≤ 1) (hle2 : l2 ≤ 1)
    (hd01 : d01 ^ 2 = (1 - l0) * (1 - l1))
    (hd02 : d02 ^ 2 = (1 - l0) * (1 - l2))
    (hd12 : d12 ^ 2 = (1 - l1) * (1 - l2))
    (hp01 : l0 ≤ t0 ∨ l1 ≤ t1 ∨ (l0 - t0) * (l1 - t1) ≤ d01 ^ 2)
    (hp02 : l0 ≤ t0 ∨ l2 ≤ t2 ∨ (l0 - t0) * (l2 - t2) ≤ d02 ^ 2)
    (hp12 : l1 ≤ t1 ∨ l2 ≤ t2 ∨ (l1 - t1) * (l2 - t2) ≤ d12 ^ 2) :
    t0 = 2 * l0 - 1 ∧ t1 = 2 * l1 - 1 ∧ t2 = 2 * l2 - 1 := by
  have hd01s : d01 ^ 2 = (1 - l1) * (1 - l0) := by rw [hd01]; ring
  have hd02s : d02 ^ 2 = (1 - l2) * (1 - l0) := by rw [hd02]; ring
  have hd12s : d12 ^ 2 = (1 - l2) * (1 - l1) := by rw [hd12]; ring
  have hp01s : l1 ≤ t1 ∨ l0 ≤ t0 ∨ (l1 - t1) * (l0 - t0) ≤ d01 ^ 2 := by
    rcases hp01 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [mul_comm]; exact h))
  have hp02s : l2 ≤ t2 ∨ l0 ≤ t0 ∨ (l2 - t2) * (l0 - t0) ≤ d02 ^ 2 := by
    rcases hp02 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [mul_comm]; exact h))
  have hp12s : l2 ≤ t2 ∨ l1 ≤ t1 ∨ (l2 - t2) * (l1 - t1) ≤ d12 ^ 2 := by
    rcases hp12 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [mul_comm]; exact h))
  -- Step 1: every leverage sits strictly below one.
  have hl0 : l0 < 1 := tie_scalar_leverage_lt_one hsuml hsumt ht0 ht1 ht2 hle0
    hd01 hd02 hp01 hp02
  have hl1 : l1 < 1 := tie_scalar_leverage_lt_one (l0 := l1) (l1 := l0) (l2 := l2)
    (t0 := t1) (t1 := t0) (t2 := t2) (by linarith) (by linarith) ht1 ht0 ht2 hle1
    hd01s hd12 hp01s hp12
  have hl2 : l2 < 1 := tie_scalar_leverage_lt_one (l0 := l2) (l1 := l0) (l2 := l1)
    (t0 := t2) (t1 := t0) (t2 := t1) (by linarith) (by linarith) ht2 ht0 ht1 hle2
    hd02s hd12s hp02s hp12s
  -- Step 2: every weight sits strictly below its leverage.
  have hw0 : t0 < l0 := tie_scalar_weight_pos hsuml hsumt ht0 ht1 ht2 hl1 hl2 hd12 hp12
  have hw1 : t1 < l1 := tie_scalar_weight_pos (l0 := l1) (l1 := l0) (l2 := l2)
    (t0 := t1) (t1 := t0) (t2 := t2) (by linarith) (by linarith) ht1 ht0 ht2 hl0 hl2
    hd02 hp02
  have hw2 : t2 < l2 := tie_scalar_weight_pos (l0 := l2) (l1 := l0) (l2 := l1)
    (t0 := t2) (t1 := t0) (t2 := t1) (by linarith) (by linarith) ht2 ht0 ht1 hl0 hl1
    hd01 hp01
  -- Step 3: the refusals collapse to the product readings.
  have hq01 : (l0 - t0) * (l1 - t1) ≤ (1 - l0) * (1 - l1) := by
    rcases hp01 with h | h | h
    · linarith
    · linarith
    · rw [hd01] at h; exact h
  have hq02 : (l0 - t0) * (l2 - t2) ≤ (1 - l0) * (1 - l2) := by
    rcases hp02 with h | h | h
    · linarith
    · linarith
    · rw [hd02] at h; exact h
  have hq12 : (l1 - t1) * (l2 - t2) ≤ (1 - l1) * (1 - l2) := by
    rcases hp12 with h | h | h
    · linarith
    · linarith
    · rw [hd12] at h; exact h
  have hq01s : (l1 - t1) * (l0 - t0) ≤ (1 - l1) * (1 - l0) := by
    rw [mul_comm, mul_comm (1 - l1)]; exact hq01
  have hq02s : (l2 - t2) * (l0 - t0) ≤ (1 - l2) * (1 - l0) := by
    rw [mul_comm, mul_comm (1 - l2)]; exact hq02
  have hq12s : (l2 - t2) * (l1 - t1) ≤ (1 - l2) * (1 - l1) := by
    rw [mul_comm, mul_comm (1 - l2)]; exact hq12
  -- Step 4: the completed square caps every slot.
  have hs0 : l0 - t0 ≤ 1 - l0 := tie_scalar_slot_le hsuml hsumt ht0 hq01 hq02
  have hs1 : l1 - t1 ≤ 1 - l1 := tie_scalar_slot_le (l0 := l1) (l1 := l0) (l2 := l2)
    (t0 := t1) (t1 := t0) (t2 := t2) (by linarith) (by linarith) ht1 hq01s hq12
  have hs2 : l2 - t2 ≤ 1 - l2 := tie_scalar_slot_le (l0 := l2) (l1 := l0) (l2 := l1)
    (t0 := t2) (t1 := t0) (t2 := t1) (by linarith) (by linarith) ht2 hq02s hq12s
  -- Step 5: the two sums close the sandwich.
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## Layer 6 — the classification and the equivalence -/

/-- **THE CLASSIFICATION.**  A three-atom plane frame with positive weights of
mass one and no strictly dominating pair carries exactly the closed-form tie
weights. -/
theorem plane_three_classification {atom : Fin 3 → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) {weight : Fin 3 → ℝ}
    (hpos : ∀ slot, 0 < weight slot) (hmass : (∑ slot, weight slot) = 1)
    (hnostrict : ∀ x y : Fin 3, x ≠ y →
      ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y)) :
    ∀ slot, weight slot = planeTieWeight atom slot := by
  have hsuml := hframe.sum_mass
  rw [Fin.sum_univ_three] at hsuml
  have hsumt := hmass
  rw [Fin.sum_univ_three] at hsumt
  have hd01 := plane_three_pair_det hframe (show (0 : Fin 3) ≠ 1 by decide)
  have hd02 := plane_three_pair_det hframe (show (0 : Fin 3) ≠ 2 by decide)
  have hd12 := plane_three_pair_det hframe (show (1 : Fin 3) ≠ 2 by decide)
  have hp01 := scalar_of_not_planePairStrict (hpos 0) (hpos 1)
    (hnostrict 0 1 (by decide))
  have hp02 := scalar_of_not_planePairStrict (hpos 0) (hpos 2)
    (hnostrict 0 2 (by decide))
  have hp12 := scalar_of_not_planePairStrict (hpos 1) (hpos 2)
    (hnostrict 1 2 (by decide))
  obtain ⟨hzero, hone, htwo⟩ := tie_scalar_classification hsuml hsumt
    (hpos 0) (hpos 1) (hpos 2)
    (hframe.mass_le_one 0) (hframe.mass_le_one 1) (hframe.mass_le_one 2)
    hd01 hd02 hd12 hp01 hp02 hp12
  intro slot
  fin_cases slot
  · show weight 0 = planeTieWeight atom 0
    simp only [planeTieWeight]
    exact hzero
  · show weight 1 = planeTieWeight atom 1
    simp only [planeTieWeight]
    exact hone
  · show weight 2 = planeTieWeight atom 2
    simp only [planeTieWeight]
    exact htwo

/-- **THE EQUIVALENCE.**  At a three-atom plane frame with positive weights of
mass one, the absence of a strictly dominating pair IS the closed form
`t_y = 2 l_y - 1`.  The tie set of the open weight simplex is one point when
every mass exceeds one half, and it is empty when some mass does not. -/
theorem plane_three_tie_iff {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {weight : Fin 3 → ℝ} (hpos : ∀ slot, 0 < weight slot)
    (hmass : (∑ slot, weight slot) = 1) :
    (∀ x y : Fin 3, x ≠ y →
        ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y))
      ↔ ∀ slot, weight slot = planeTieWeight atom slot := by
  constructor
  · exact plane_three_classification hframe hpos hmass
  · intro hweights x y hxy
    have hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot := by
      intro slot
      have hw := hpos slot
      rw [hweights slot] at hw
      simp only [planeTieWeight] at hw
      linarith
    rw [hweights x, hweights y]
    exact planeTie_pair_not_strict hframe hhalf hxy

/-- **THE EXISTENCE CLASSIFICATION.**  A three-atom plane Parseval frame
admits a positive mass-one weight vector with no strict pair exactly when all
three atom masses exceed one half.  In that case the witness is the explicit
`planeTieWeight`. -/
theorem exists_plane_three_tie_iff {atom : Fin 3 → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) :
    (∃ weight : Fin 3 → ℝ,
        (∀ slot, 0 < weight slot) ∧ (∑ slot, weight slot) = 1 ∧
          ∀ x y : Fin 3, x ≠ y →
            ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y))
      ↔ ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot := by
  constructor
  · rintro ⟨weight, hpos, hmass, hnostrict⟩ slot
    have hweight := plane_three_classification hframe hpos hmass hnostrict slot
    have hslot := hpos slot
    rw [hweight] at hslot
    simp only [planeTieWeight] at hslot
    linarith
  · intro hhalf
    refine ⟨planeTieWeight atom, planeTieWeight_pos hhalf, planeTieWeight_sum hframe, ?_⟩
    intro x y hxy
    exact planeTie_pair_not_strict hframe hhalf hxy

/-- The positive mass-one tie weight of a three-atom plane frame is unique. -/
theorem plane_three_tie_unique {atom : Fin 3 → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) {firstWeight secondWeight : Fin 3 → ℝ}
    (hfirstPos : ∀ slot, 0 < firstWeight slot)
    (hfirstMass : (∑ slot, firstWeight slot) = 1)
    (hfirstTie : ∀ x y : Fin 3, x ≠ y →
      ¬ PlanePairDominatesStrict (atom x) (atom y) (firstWeight x) (firstWeight y))
    (hsecondPos : ∀ slot, 0 < secondWeight slot)
    (hsecondMass : (∑ slot, secondWeight slot) = 1)
    (hsecondTie : ∀ x y : Fin 3, x ≠ y →
      ¬ PlanePairDominatesStrict (atom x) (atom y) (secondWeight x) (secondWeight y)) :
    firstWeight = secondWeight := by
  funext slot
  rw [plane_three_classification hframe hfirstPos hfirstMass hfirstTie slot,
    plane_three_classification hframe hsecondPos hsecondMass hsecondTie slot]

/-- Every pair of a positive mass-one three-atom tie dominates weakly.  Thus
the classification is genuinely an all-tied family, not merely a family with
no strict winner. -/
theorem plane_three_pair_dominates_of_tie {atom : Fin 3 → (Fin 2 → ℝ)}
    (hframe : PlaneParseval atom) {weight : Fin 3 → ℝ}
    (hpos : ∀ slot, 0 < weight slot) (hmass : (∑ slot, weight slot) = 1)
    (hnostrict : ∀ x y : Fin 3, x ≠ y →
      ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y))
    {x y : Fin 3} (hxy : x ≠ y) :
    PlanePairDominates (atom x) (atom y) (weight x) (weight y) := by
  have hweights := plane_three_classification hframe hpos hmass hnostrict
  have hhalf : ∀ slot, 1 / 2 < atom slot ⬝ᵥ atom slot := by
    intro slot
    have hslot := hpos slot
    rw [hweights slot] at hslot
    simp only [planeTieWeight] at hslot
    linarith
  rw [hweights x, hweights y]
  exact planeTie_pair_dominates hframe hhalf hxy

/-- **THE W READING OF THE FAMILY.**  At the tie weights each term
`2 l_y t_y - t_y^2` collapses to `t_y`, so the sum is the mass total minus
one.  This is the equality case of the W identity of the tie locus. -/
theorem planeTie_w_identity {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom) :
    (∑ slot, (2 * (atom slot ⬝ᵥ atom slot) * planeTieWeight atom slot
        - planeTieWeight atom slot ^ 2))
      = (∑ slot, atom slot ⬝ᵥ atom slot) - 1 := by
  have hmass := hframe.sum_mass
  rw [Fin.sum_univ_three] at hmass
  simp only [planeTieWeight]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  ring_nf
  linarith

/-- The trine carries the closed-form tie weights: the landed sharpness
calibration of the selection theorem is the equilateral point of this
family. -/
theorem planeTrine_tieWeight (slot : Fin 3) :
    planeTieWeight planeTrineAtom slot = 1 / 3 := by
  simp only [planeTieWeight, planeTrineAtom_mass]
  norm_num

/-! ## Layer 7 — the W engine at every slot count

The quantitative engine of the tie locus.  The active block of a design is a
partial plane operator between zero and the identity, so its squared
Frobenius reading sits below its trace.  The no-strict refusals price every
active pair reading from below, and the inert slots can only enlarge the
active budget total.  The three facts close the W bound. -/

/-- **THE QUARTER-TRACE CORE.**  A two-by-two operator caught between zero and
the identity has its squared Frobenius reading below its trace.  The proof
multiplies the two determinant readings and completes one square. -/
theorem quarter_trace_core {p q r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hpOne : p ≤ 1) (hrOne : r ≤ 1)
    (hdetOne : q ^ 2 ≤ p * r) (hdetTwo : q ^ 2 ≤ (1 - p) * (1 - r)) :
    p ^ 2 + 2 * q ^ 2 + r ^ 2 ≤ p + r := by
  have hA : 0 ≤ p * r - q ^ 2 := by linarith
  have hB : 0 ≤ (1 - p) * (1 - r) - q ^ 2 := by linarith
  have hprod : 0 ≤ (p * (1 - p) + r * (1 - r)) ^ 2 - 4 * q ^ 4 := by
    nlinarith [mul_nonneg hA hB, sq_nonneg (p * (1 - p) - r * (1 - r))]
  have hXnn : 0 ≤ p * (1 - p) := mul_nonneg hp (by linarith)
  have hYnn : 0 ≤ r * (1 - r) := mul_nonneg hr (by linarith)
  by_cases hzero : p * (1 - p) + r * (1 - r) + 2 * q ^ 2 = 0
  · have hq : q ^ 2 = 0 := by nlinarith [sq_nonneg q]
    nlinarith [hq, hzero]
  · have hpos : 0 < p * (1 - p) + r * (1 - r) + 2 * q ^ 2 := by
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ p * (1 - p) + r * (1 - r) + 2 * q ^ 2 by
        nlinarith [sq_nonneg q]) with h | h
      · exact h
      · exact absurd h.symm hzero
    by_contra hng
    rw [not_le] at hng
    have hgap : 0 < p ^ 2 + 2 * q ^ 2 + r ^ 2 - (p + r) := by linarith
    nlinarith [hprod, mul_pos hpos hgap]

/-- **THE W ENGINE.**  At mass one, an active set whose slots all carry a
positive budget, whose complement is inert, and whose pairs never dominate
strictly obeys the W bound: the active sum of `2 l t - t ^ 2` stays below the
active mass total minus one.  This is the strictness engine of the tie
charts, at every slot count. -/
theorem plane_w_engine {slotCount : ℕ} {atom : Fin slotCount → (Fin 2 → ℝ)}
    {weight : Fin slotCount → ℝ} (hframe : PlaneParseval atom)
    (hpos : ∀ slot, 0 < weight slot) (hmass : (∑ slot, weight slot) = 1)
    (active : Finset (Fin slotCount))
    (hactive : ∀ slot ∈ active, weight slot < atom slot ⬝ᵥ atom slot)
    (hinert : ∀ slot ∉ active, atom slot ⬝ᵥ atom slot ≤ weight slot)
    (hnostrict : ∀ x ∈ active, ∀ y ∈ active, x ≠ y →
      ¬ PlanePairDominatesStrict (atom x) (atom y) (weight x) (weight y)) :
    (∑ slot ∈ active, (2 * (atom slot ⬝ᵥ atom slot) * weight slot - weight slot ^ 2))
      ≤ (∑ slot ∈ active, atom slot ⬝ᵥ atom slot) - 1 := by
  classical
  -- The partial entry sums of the active block, and their operator bounds.
  have hpNonneg : (0 : ℝ) ≤ ∑ slot ∈ active, atom slot 0 * atom slot 0 :=
    Finset.sum_nonneg fun slot _ => mul_self_nonneg _
  have hrNonneg : (0 : ℝ) ≤ ∑ slot ∈ active, atom slot 1 * atom slot 1 :=
    Finset.sum_nonneg fun slot _ => mul_self_nonneg _
  have hpSplit := Finset.sum_add_sum_compl active (fun slot => atom slot 0 * atom slot 0)
  have hrSplit := Finset.sum_add_sum_compl active (fun slot => atom slot 1 * atom slot 1)
  have hqSplit := Finset.sum_add_sum_compl active (fun slot => atom slot 0 * atom slot 1)
  rw [hframe.sum_first_sq] at hpSplit
  rw [hframe.sum_second_sq] at hrSplit
  rw [hframe.sum_cross] at hqSplit
  have hpOne : (∑ slot ∈ active, atom slot 0 * atom slot 0) ≤ 1 := by
    have hcompl : (0 : ℝ) ≤ ∑ slot ∈ activeᶜ, atom slot 0 * atom slot 0 :=
      Finset.sum_nonneg fun slot _ => mul_self_nonneg _
    linarith
  have hrOne : (∑ slot ∈ active, atom slot 1 * atom slot 1) ≤ 1 := by
    have hcompl : (0 : ℝ) ≤ ∑ slot ∈ activeᶜ, atom slot 1 * atom slot 1 :=
      Finset.sum_nonneg fun slot _ => mul_self_nonneg _
    linarith
  have hdetOne : (∑ slot ∈ active, atom slot 0 * atom slot 1) ^ 2
      ≤ (∑ slot ∈ active, atom slot 0 * atom slot 0)
        * (∑ slot ∈ active, atom slot 1 * atom slot 1) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq active
      (fun slot => atom slot 0) (fun slot => atom slot 1)
    simp only [pow_two] at hcs ⊢
    exact hcs
  have hdetTwo : (∑ slot ∈ active, atom slot 0 * atom slot 1) ^ 2
      ≤ (1 - ∑ slot ∈ active, atom slot 0 * atom slot 0)
        * (1 - ∑ slot ∈ active, atom slot 1 * atom slot 1) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq activeᶜ
      (fun slot => atom slot 0) (fun slot => atom slot 1)
    simp only [pow_two] at hcs
    have hqc : (∑ slot ∈ activeᶜ, atom slot 0 * atom slot 1)
        = -(∑ slot ∈ active, atom slot 0 * atom slot 1) := by linarith
    have hpc : (∑ slot ∈ activeᶜ, atom slot 0 * atom slot 0)
        = 1 - (∑ slot ∈ active, atom slot 0 * atom slot 0) := by linarith
    have hrc : (∑ slot ∈ activeᶜ, atom slot 1 * atom slot 1)
        = 1 - (∑ slot ∈ active, atom slot 1 * atom slot 1) := by linarith
    rw [hqc, hpc, hrc] at hcs
    nlinarith [hcs]
  have hcore := quarter_trace_core hpNonneg hrNonneg hpOne hrOne hdetOne hdetTwo
  -- The double-sum reading of the squared Frobenius norm.
  have hdouble : (∑ x ∈ active, ∑ y ∈ active, (atom x ⬝ᵥ atom y) ^ 2)
      = (∑ slot ∈ active, atom slot 0 * atom slot 0) ^ 2
        + 2 * (∑ slot ∈ active, atom slot 0 * atom slot 1) ^ 2
        + (∑ slot ∈ active, atom slot 1 * atom slot 1) ^ 2 := by
    simp only [pow_two]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [dot_fin_two]
    ring
  -- The refusal prices every off-diagonal reading from below.
  have hcompare : (∑ x ∈ active, ∑ y ∈ active,
        (if x = y then (atom x ⬝ᵥ atom x) ^ 2
          else (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y)))
      ≤ ∑ x ∈ active, ∑ y ∈ active, (atom x ⬝ᵥ atom y) ^ 2 := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
    · rw [if_neg hxy]
      rcases scalar_of_not_planePairStrict (hpos x) (hpos y)
        (hnostrict x hx y hy hxy) with h | h | h
      · exact absurd h (not_le.mpr (hactive x hx))
      · exact absurd h (not_le.mpr (hactive y hy))
      · exact h
  -- The comparison sum in closed form.
  have hsplitFun : ∀ x ∈ active, (∑ y ∈ active,
        (if x = y then (atom x ⬝ᵥ atom x) ^ 2
          else (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y)))
      = (∑ y ∈ active, (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y))
        + ((atom x ⬝ᵥ atom x) ^ 2
          - (atom x ⬝ᵥ atom x - weight x) * (atom x ⬝ᵥ atom x - weight x)) := by
    intro x hx
    have hpoint : ∀ y : Fin slotCount, (if x = y then (atom x ⬝ᵥ atom x) ^ 2
          else (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y))
        = (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y)
          + (if x = y then (atom x ⬝ᵥ atom x) ^ 2
              - (atom x ⬝ᵥ atom x - weight x) * (atom x ⬝ᵥ atom x - weight x) else 0) := by
      intro y
      by_cases h : x = y
      · subst h
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg h, if_neg h]
        ring
    simp only [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq active x, if_pos hx]
  have hiteSum : (∑ x ∈ active, ∑ y ∈ active,
        (if x = y then (atom x ⬝ᵥ atom x) ^ 2
          else (atom x ⬝ᵥ atom x - weight x) * (atom y ⬝ᵥ atom y - weight y)))
      = (∑ slot ∈ active, (atom slot ⬝ᵥ atom slot - weight slot))
          * (∑ slot ∈ active, (atom slot ⬝ᵥ atom slot - weight slot))
        + ((∑ slot ∈ active, (atom slot ⬝ᵥ atom slot) ^ 2)
          - (∑ slot ∈ active,
              (atom slot ⬝ᵥ atom slot - weight slot)
                * (atom slot ⬝ᵥ atom slot - weight slot))) := by
    rw [Finset.sum_congr rfl hsplitFun, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul_sum]
  -- The active budget total reaches one.
  have hwOne : 1 ≤ ∑ slot ∈ active, (atom slot ⬝ᵥ atom slot - weight slot) := by
    have htotal : (∑ slot, (atom slot ⬝ᵥ atom slot - weight slot)) = 1 := by
      rw [Finset.sum_sub_distrib, hframe.sum_mass, hmass]
      norm_num
    have hsplit := Finset.sum_add_sum_compl active
      (fun slot => atom slot ⬝ᵥ atom slot - weight slot)
    have hcompl : (∑ slot ∈ activeᶜ, (atom slot ⬝ᵥ atom slot - weight slot)) ≤ 0 :=
      Finset.sum_nonpos fun slot hslot => by
        have hread := hinert slot (Finset.mem_compl.mp hslot)
        linarith
    rw [htotal] at hsplit
    linarith
  have hwSq : 1 ≤ (∑ slot ∈ active, (atom slot ⬝ᵥ atom slot - weight slot))
      * (∑ slot ∈ active, (atom slot ⬝ᵥ atom slot - weight slot)) := by
    nlinarith [hwOne]
  -- The trace of the active block is its mass total.
  have htrace : (∑ slot ∈ active, atom slot 0 * atom slot 0)
        + (∑ slot ∈ active, atom slot 1 * atom slot 1)
      = ∑ slot ∈ active, atom slot ⬝ᵥ atom slot := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    rw [dot_fin_two]
  -- The per-slot reading of the W terms.
  have hterms : (∑ slot ∈ active,
        (2 * (atom slot ⬝ᵥ atom slot) * weight slot - weight slot ^ 2))
      = (∑ slot ∈ active, (atom slot ⬝ᵥ atom slot) ^ 2)
        - (∑ slot ∈ active,
            (atom slot ⬝ᵥ atom slot - weight slot)
              * (atom slot ⬝ᵥ atom slot - weight slot)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    ring
  linarith [hcore, hdouble, hcompare, hiteSum, hwSq, htrace, hterms]

/-! ## Layer 8 — the four-atom kill, and the exact line count of an all-tied
family

A design is ALL TIED when every pair sits at the certificate boundary,
`(b_x ⬝ᵥ b_y)^2 = w_x w_y` with `w_y = l_y - t_y` the budget mass.  The
three-atom family of Layer 3 is all tied.  This layer proves that FOUR atoms
of positive budget can never be all tied unless two of them are PARALLEL.

The engine is the Plücker identity of the plane.  For any four plane vectors
the three pair products of dots differ by products of wedges, and the three
differences use the three perfect matchings of the four slots.  An all-tied
quadruple gives all three products the same square, namely `w_1 w_2 w_3 w_4`.
If no pair is parallel, every wedge product is nonzero, so each of the three
SUMS of products vanishes, which forces every product to vanish — against the
positive budget.

The consequence is the line count.  Parallel atoms carry the same line, so an
all-tied family of positive budgets occupies at most THREE distinct lines, and
Layer 3 realizes exactly three.  The Mercedes trine is the equilateral point of
that family. -/

/-- **THE PLANE PLÜCKER IDENTITY, FIRST MATCHING.**  A universal polynomial
identity of four plane vectors: no frame law, no normalization. -/
theorem plane_plucker_first (b0 b1 b2 b3 : Fin 2 → ℝ) :
    (b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) - (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3)
      = planeWedge b0 b3 * planeWedge b1 b2 := by
  simp only [dot_fin_two, planeWedge]
  ring

/-- **THE PLANE PLÜCKER IDENTITY, SECOND MATCHING.** -/
theorem plane_plucker_second (b0 b1 b2 b3 : Fin 2 → ℝ) :
    (b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) - (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2)
      = planeWedge b0 b2 * planeWedge b1 b3 := by
  simp only [dot_fin_two, planeWedge]
  ring

/-- **THE PLANE PLÜCKER IDENTITY, THIRD MATCHING.** -/
theorem plane_plucker_third (b0 b1 b2 b3 : Fin 2 → ℝ) :
    (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) - (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2)
      = planeWedge b0 b1 * planeWedge b2 b3 := by
  simp only [dot_fin_two, planeWedge]
  ring

/-- **THE FOUR-ATOM KILL.**  Four plane atoms of positive budget mass cannot
have every pair at the certificate boundary unless two of them are parallel.

The hypothesis is the boundary reading `(b_x ⬝ᵥ b_y)^2 = w_x w_y` at all six
pairs.  No frame law is used, and no isotropy: the statement is pure plane
algebra. -/
theorem plane_four_allTied_parallel {b0 b1 b2 b3 : Fin 2 → ℝ} {w0 w1 w2 w3 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hw3 : 0 < w3)
    (h01 : (b0 ⬝ᵥ b1) ^ 2 = w0 * w1) (h02 : (b0 ⬝ᵥ b2) ^ 2 = w0 * w2)
    (h03 : (b0 ⬝ᵥ b3) ^ 2 = w0 * w3) (h12 : (b1 ⬝ᵥ b2) ^ 2 = w1 * w2)
    (h13 : (b1 ⬝ᵥ b3) ^ 2 = w1 * w3) (h23 : (b2 ⬝ᵥ b3) ^ 2 = w2 * w3) :
    planeWedge b0 b1 = 0 ∨ planeWedge b0 b2 = 0 ∨ planeWedge b0 b3 = 0
      ∨ planeWedge b1 b2 = 0 ∨ planeWedge b1 b3 = 0 ∨ planeWedge b2 b3 = 0 := by
  by_contra hall
  simp only [not_or] at hall
  obtain ⟨n01, n02, n03, n12, n13, n23⟩ := hall
  -- The three matching products carry one common square.
  have hcommon : 0 < w0 * w1 * (w2 * w3) := by positivity
  have hsqOne : ((b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3)) ^ 2 = w0 * w1 * (w2 * w3) := by
    rw [mul_pow, h01, h23]
  have hsqTwo : ((b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3)) ^ 2 = w0 * w1 * (w2 * w3) := by
    rw [mul_pow, h02, h13]; ring
  have hsqThree : ((b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2)) ^ 2 = w0 * w1 * (w2 * w3) := by
    rw [mul_pow, h03, h12]; ring
  -- Each difference of products is a nonzero product of wedges.
  have hdiffOne : (b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) - (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) ≠ 0 := by
    rw [plane_plucker_first]
    exact mul_ne_zero n03 n12
  have hdiffTwo : (b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) - (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2) ≠ 0 := by
    rw [plane_plucker_second]
    exact mul_ne_zero n02 n13
  have hdiffThree : (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) - (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2) ≠ 0 := by
    rw [plane_plucker_third]
    exact mul_ne_zero n01 n23
  -- Equal squares with a nonzero difference force the SUM to vanish.
  have hsumOne : (b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) + (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) = 0 := by
    rcases mul_eq_zero.mp (show ((b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) - (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3))
        * ((b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) + (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3)) = 0 by
      have := hsqOne.trans hsqTwo.symm
      nlinarith [this]) with h | h
    · exact absurd h hdiffOne
    · exact h
  have hsumTwo : (b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) + (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2) = 0 := by
    rcases mul_eq_zero.mp (show ((b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) - (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2))
        * ((b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) + (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2)) = 0 by
      have := hsqOne.trans hsqThree.symm
      nlinarith [this]) with h | h
    · exact absurd h hdiffTwo
    · exact h
  have hsumThree : (b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) + (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2) = 0 := by
    rcases mul_eq_zero.mp (show ((b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) - (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2))
        * ((b0 ⬝ᵥ b2) * (b1 ⬝ᵥ b3) + (b0 ⬝ᵥ b3) * (b1 ⬝ᵥ b2)) = 0 by
      have := hsqTwo.trans hsqThree.symm
      nlinarith [this]) with h | h
    · exact absurd h hdiffThree
    · exact h
  -- The three sums vanish, so every product vanishes, against the budget.
  have hzero : (b0 ⬝ᵥ b1) * (b2 ⬝ᵥ b3) = 0 := by linarith
  rw [hzero] at hsqOne
  nlinarith [hsqOne, hcommon]

/-- **THE ALL-TIED FAMILY OCCUPIES THREE LINES.**  Stated at a family indexed
by `Fin 4`: some pair is parallel, hence an all-tied family of positive
budgets never carries four distinct lines. -/
theorem plane_four_allTied_exists_parallel {b : Fin 4 → (Fin 2 → ℝ)} {w : Fin 4 → ℝ}
    (hw : ∀ slot, 0 < w slot)
    (htied : ∀ x y : Fin 4, x ≠ y → (b x ⬝ᵥ b y) ^ 2 = w x * w y) :
    ∃ x y : Fin 4, x ≠ y ∧ planeWedge (b x) (b y) = 0 := by
  rcases plane_four_allTied_parallel (hw 0) (hw 1) (hw 2) (hw 3)
    (htied 0 1 (by decide)) (htied 0 2 (by decide)) (htied 0 3 (by decide))
    (htied 1 2 (by decide)) (htied 1 3 (by decide)) (htied 2 3 (by decide)) with
    h | h | h | h | h | h
  · exact ⟨0, 1, by decide, h⟩
  · exact ⟨0, 2, by decide, h⟩
  · exact ⟨0, 3, by decide, h⟩
  · exact ⟨1, 2, by decide, h⟩
  · exact ⟨1, 3, by decide, h⟩
  · exact ⟨2, 3, by decide, h⟩

/-- The three-atom family of Layer 3 IS all tied in the budget reading, so the
four-atom kill is sharp: three atoms of positive budget are all tied, four are
never all tied without a parallel pair. -/
theorem planeTie_allTied_reading {atom : Fin 3 → (Fin 2 → ℝ)} (hframe : PlaneParseval atom)
    {x y : Fin 3} (hxy : x ≠ y) :
    (atom x ⬝ᵥ atom y) ^ 2
      = ((atom x ⬝ᵥ atom x) - planeTieWeight atom x)
        * ((atom y ⬝ᵥ atom y) - planeTieWeight atom y) :=
  planeTie_pair_det_eq hframe hxy

end Gtz
