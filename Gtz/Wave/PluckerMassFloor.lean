import Gtz.LinAlg.ProjectionForm
import Gtz.Wave.SelectionMarginLaws
import Gtz.Wave.ProjectionBlockObjective

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The Plücker mass floor, and why the determinantal measure cannot select

At rank three on six labels the twenty three-by-three principal minors of the
projection form a probability measure — `Gtz.sum_det_projectionMinors_rank` — and
the block determinant that decides domination is that measure minus a sign-free
threshold.  This module makes the reduction exact, pushes the floor on the
measure as far as it goes, and then proves that the whole lane is blind.

## The reduction

Write `p S` for the principal minor of the projection at a triple and `Z` for the
shifted matrix `P - diagonal w`.  Expanding `det Z_S` by the elementary symmetric
functions of the triple's Gram gives `det Z_S = w_x w_y w_z * (bracket ^ 2 - Δ)`
with `Δ` sign-free, so at a uniform weight the objective is implied by

  `1/216 * (some triple's bracket squared) > 1/216 * Δ`,

and summing the two sides over the twenty triples turns the average of the left
into `1` and the average of the right into `1 - e₃(Z) = 34/27`.  The gap `7/27`
is the whole content: the objective holds if the MAXIMUM of the measure beats its
mean by that factor, that is if `max p ≥ 17/270`.

## The floor, and the refutation

`Gtz.exists_pluckerWeight_ge_one_twentieth` is the free pigeonhole, and it is
already a factor `9/5` better than the landed
`Gtz.exists_dppTripleWeight_ge`, which divides the determinantal mass six by the
two hundred and sixteen ORDERED triples instead of by the twenty unordered ones.

`Gtz.massFloor_of_two_small` together with the landed Plücker spread law pushes
past the pigeonhole: two disjoint pivot stars each contain a triple of weight at
most `max / √2`, so `(1 - 18 * max) ^ 2 ≤ 2 * max ^ 2` and the maximum clears
`51/1000`.  That improvement is REAL ONLY.  Over the Hermitian field the six
weights of a star obey the triangle inequalities alone, twenty equal weights are
admissible, and the floor is exactly `1/20`.

The floor does not reach `17/270`, and the obstruction is landed and named.  At
`Gtz.kfourEdgeProjection`, the graphic point of `K4`, the twenty weights are
`1/16` on the sixteen spanning trees and `0` on the four triangles, so

  `max p = 1/16 < 17/270`,  deficit exactly `1/2160`.

`Gtz.not_massFloorReaches_seventeen_twoSeventieths` records that.

## The blindness, which is the real result

The refutation is a hair, but the reason behind it is absolute.  At the graphic
point SIXTEEN triples carry the identical weight `1/16` while only FOUR of them
dominate — the four stars of `K4`, at `det Z = 5/864`, against the twelve paths
at `-1/216`.  `Gtz.margin_not_determined_by_pluckerWeight` exhibits the pair.

So no function of the determinantal measure alone can decide, bound, or certify
domination.  This is the Plücker-coordinate companion of the landed
`Gtz.margin_not_determined_by_leverage_diagonal`, and together they close the two
coordinate systems in which the campaign has looked for a selection rule.

## What is reusable

`Gtz.det_submatrix_val_eq_principalMinorThree` is the `Finset.powersetCard`
bridge: the determinant of the subtype-indexed block equals the Sarrus form at
the three sorted elements.  Two forks named that step as a gap and routed around
it.  `Gtz.sum_pow_succ_le_max_mul_sum_pow` is the moment ladder, `max ≥ Σ f^{n+1}
/ Σ f^n` for every `n`, which the corpus lacks at any level.
-/

namespace Gtz

open scoped BigOperators

open Matrix

/-! ## 1. The principal three-minor, and the `powersetCard` bridge -/

/-- The principal three-by-three minor of a square matrix at three labels,
written by the Sarrus expansion so that every downstream statement is scalar
algebra.  The term order matches `Matrix.det_fin_three`. -/
def principalMinorThree {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ) (labelA labelB labelC : Fin n) :
    ℝ :=
  form labelA labelA * form labelB labelB * form labelC labelC
    - form labelA labelA * form labelB labelC * form labelC labelB
    - form labelA labelB * form labelB labelA * form labelC labelC
    + form labelA labelB * form labelB labelC * form labelC labelA
    + form labelA labelC * form labelB labelA * form labelC labelB
    - form labelA labelC * form labelB labelB * form labelC labelA

/-- A repeated label kills the minor: two equal rows. -/
theorem principalMinorThree_self_left {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ)
    (labelA labelC : Fin n) : principalMinorThree form labelA labelA labelC = 0 := by
  rw [principalMinorThree]; ring

/-- A repeated outer label kills the minor. -/
theorem principalMinorThree_self_outer {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ)
    (labelA labelB : Fin n) : principalMinorThree form labelA labelB labelA = 0 := by
  rw [principalMinorThree]; ring

/-- A repeated trailing label kills the minor. -/
theorem principalMinorThree_self_right {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ)
    (labelA labelB : Fin n) : principalMinorThree form labelA labelB labelB = 0 := by
  rw [principalMinorThree]; ring

/-- The minor is invariant under swapping the first two labels. -/
theorem principalMinorThree_swap_left {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ)
    (labelA labelB labelC : Fin n) :
    principalMinorThree form labelA labelB labelC = principalMinorThree form labelB labelA labelC := by
  rw [principalMinorThree, principalMinorThree]; ring

/-- The minor is invariant under swapping the last two labels. -/
theorem principalMinorThree_swap_right {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ)
    (labelA labelB labelC : Fin n) :
    principalMinorThree form labelA labelB labelC = principalMinorThree form labelA labelC labelB := by
  rw [principalMinorThree, principalMinorThree]; ring

/-- Scaling the matrix scales the minor by the cube. -/
theorem principalMinorThree_smul {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ) (scale : ℝ)
    (labelA labelB labelC : Fin n) :
    principalMinorThree (scale • form) labelA labelB labelC
      = scale ^ 3 * principalMinorThree form labelA labelB labelC := by
  simp only [principalMinorThree, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **THE `powersetCard` BRIDGE.**  The determinant of the subtype-indexed
principal block at a three-element label set is the Sarrus form at the three
labels in increasing order.  The landed determinantal identities are stated on
the subtype-indexed block, every cell in the campaign is stated on explicit
labels, and this is the step that joins them. -/
theorem det_submatrix_val_eq_principalMinorThree {n : ℕ} (form : Matrix (Fin n) (Fin n) ℝ)
    (labels : Finset (Fin n)) (hcard : labels.card = 3) :
    (form.submatrix (Subtype.val : { c // c ∈ labels } → Fin n)
        (Subtype.val : { c // c ∈ labels } → Fin n)).det
      = principalMinorThree form (labels.orderIsoOfFin hcard 0)
          (labels.orderIsoOfFin hcard 1) (labels.orderIsoOfFin hcard 2) := by
  classical
  have hre := Matrix.det_submatrix_equiv_self (labels.orderIsoOfFin hcard).toEquiv
    (form.submatrix (Subtype.val : { c // c ∈ labels } → Fin n)
      (Subtype.val : { c // c ∈ labels } → Fin n))
  rw [← hre, Matrix.submatrix_submatrix, Matrix.det_fin_three]
  rfl

/-! ## 2. The moment ladder

For a nonnegative function on a finite set the ratio of consecutive power sums is
a lower bound for the maximum, and the ladder is monotone in the exponent.  The
`n = 0` rung is the plain pigeonhole.  Nothing of this shape is in the corpus. -/

/-- **THE MOMENT LADDER.**  For a nonnegative function capped by `cap`, the
`(n+1)`-st power sum is at most `cap` times the `n`-th. -/
theorem sum_pow_succ_le_max_mul_sum_pow {ι : Type*} (labels : Finset ι) (value : ι → ℝ)
    (cap : ℝ) (hnonneg : ∀ x ∈ labels, 0 ≤ value x) (hcap : ∀ x ∈ labels, value x ≤ cap)
    (power : ℕ) :
    (∑ x ∈ labels, value x ^ (power + 1)) ≤ cap * ∑ x ∈ labels, value x ^ power := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  have hpow : (0:ℝ) ≤ value x ^ power := pow_nonneg (hnonneg x hx) power
  calc value x ^ (power + 1) = value x * value x ^ power := by ring
    _ ≤ cap * value x ^ power := by
        exact mul_le_mul_of_nonneg_right (hcap x hx) hpow

/-- **THE PIGEONHOLE RUNG.**  If every value is capped then the total is at most
the cardinality times the cap.  This is the `n = 0` rung of the ladder. -/
theorem sum_le_card_mul_of_le {ι : Type*} (labels : Finset ι) (value : ι → ℝ) (cap : ℝ)
    (hcap : ∀ x ∈ labels, value x ≤ cap) :
    (∑ x ∈ labels, value x) ≤ (labels.card : ℝ) * cap := by
  calc (∑ x ∈ labels, value x) ≤ ∑ _x ∈ labels, cap := Finset.sum_le_sum hcap
    _ = (labels.card : ℝ) * cap := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **THE LADDER AS A FLOOR ON THE MAXIMUM.**  If the `n`-th power sum is
positive then the ratio of consecutive power sums is a witness-free lower bound
for any cap.  Larger exponents give sharper bounds, and the limit is exact. -/
theorem le_cap_of_sum_pow_ratio {ι : Type*} (labels : Finset ι) (value : ι → ℝ) (cap : ℝ)
    (hnonneg : ∀ x ∈ labels, 0 ≤ value x) (hcap : ∀ x ∈ labels, value x ≤ cap)
    (power : ℕ) (hpos : 0 < ∑ x ∈ labels, value x ^ power) :
    (∑ x ∈ labels, value x ^ (power + 1)) / (∑ x ∈ labels, value x ^ power) ≤ cap := by
  rw [div_le_iff₀ hpos]
  have h := sum_pow_succ_le_max_mul_sum_pow labels value cap hnonneg hcap power
  linarith [h]

/-! ## 3. The determinantal measure on triples

The `k`-subset minors of a design's projection form a probability measure.  At
`(6,3)` there are exactly twenty of them, so the free pigeonhole gives a maximum
of at least one twentieth. -/

/-- The **PLÜCKER WEIGHT** of a label set: the principal minor of the projection
form.  At a rank-sized set it is the squared volume of the selected scaled atoms,
and the landed volume-sampling identity makes these a probability measure. -/
noncomputable def pluckerWeight {m k : ℕ} (D : WeightedDesign m k) (labels : Finset (Fin m)) : ℝ :=
  ((projectionOfDesign D).submatrix (Subtype.val : { c // c ∈ labels } → Fin m)
    (Subtype.val : { c // c ∈ labels } → Fin m)).det

/-- The Plücker weights of the rank-sized sets add to one. -/
theorem sum_pluckerWeight_eq_one {m k : ℕ} (D : WeightedDesign m k) :
    (∑ labels ∈ (Finset.univ : Finset (Fin m)).powersetCard k, pluckerWeight D labels) = 1 :=
  sum_det_projectionMinors_rank D

/-- Every Plücker weight is nonnegative: a principal block of a positive
semidefinite form is positive semidefinite.  The frame-square positivity is the
landed `Gtz.posSemidef_projectionOfDesign`. -/
theorem pluckerWeight_nonneg {m k : ℕ} (D : WeightedDesign m k) (labels : Finset (Fin m)) :
    0 ≤ pluckerWeight D labels :=
  ((posSemidef_projectionOfDesign D).submatrix _).det_nonneg

/-- There are exactly twenty three-element label sets at six labels. -/
theorem card_powersetCard_three_six :
    ((Finset.univ : Finset (Fin 6)).powersetCard 3).card = 20 := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

/-- The three-element label sets at six labels are nonempty. -/
theorem powersetCard_three_six_nonempty :
    ((Finset.univ : Finset (Fin 6)).powersetCard 3).Nonempty := by
  rw [← Finset.card_pos, card_powersetCard_three_six]
  norm_num

/-- **THE FREE MASS FLOOR.**  Some triple of a `(6,3)` design carries a Plücker
weight of at least one twentieth.  The landed `Gtz.exists_dppTripleWeight_ge`
gives one thirty-sixth, because it divides the determinantal mass by the two
hundred and sixteen ORDERED triples rather than by the twenty unordered ones, so
this is a factor `9/5` sharper. -/
theorem exists_pluckerWeight_ge_one_twentieth (D : WeightedDesign 6 3) :
    ∃ labels ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (1:ℝ) / 20 ≤ pluckerWeight D labels := by
  classical
  by_contra hnone
  push Not at hnone
  have hstrict : (∑ labels ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3, pluckerWeight D labels)
      < ∑ _labels ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3, (1:ℝ) / 20 :=
    Finset.sum_lt_sum_of_nonempty powersetCard_three_six_nonempty fun labels hlabels =>
      hnone labels hlabels
  rw [sum_pluckerWeight_eq_one, Finset.sum_const, card_powersetCard_three_six] at hstrict
  norm_num at hstrict

/-- **THE MASS FLOOR STATEMENT.**  A level is reached when every symmetric
idempotent of trace three on six labels carries a three-minor at that level.  The
objective at a uniform weight follows from the level `17/270`, because the
determinantal-weighted total of the threshold is `34/27` and there are twenty
triples. -/
def MassFloorReaches (level : ℝ) : Prop :=
  ∀ form : Matrix (Fin 6) (Fin 6) ℝ, formᵀ = form → form * form = form →
    Matrix.trace form = 3 →
      ∃ labelA labelB labelC : Fin 6, labelA ≠ labelB ∧ labelA ≠ labelC ∧ labelB ≠ labelC
        ∧ level ≤ principalMinorThree form labelA labelB labelC

/-! ## 4. The graphic point of `K4`, exactly

The landed `Gtz.kfourEdgeProjection` is `Gtz.kfourGramInt / 4`.  Its three-minors
are therefore the integer minors of the core divided by sixty-four, and those
integers take exactly two values. -/

/-- The integer core of the three-minor at the graphic point of `K4`. -/
def kfourMinorInt (labelA labelB labelC : Fin 6) : ℤ :=
  kfourGramInt labelA labelA * kfourGramInt labelB labelB * kfourGramInt labelC labelC
    - kfourGramInt labelA labelA * kfourGramInt labelB labelC * kfourGramInt labelC labelB
    - kfourGramInt labelA labelB * kfourGramInt labelB labelA * kfourGramInt labelC labelC
    + kfourGramInt labelA labelB * kfourGramInt labelB labelC * kfourGramInt labelC labelA
    + kfourGramInt labelA labelC * kfourGramInt labelB labelA * kfourGramInt labelC labelB
    - kfourGramInt labelA labelC * kfourGramInt labelB labelB * kfourGramInt labelC labelA

/-- **THE GRAPHIC POINT CARRIES TWO MINOR VALUES AND NO OTHER.**  Two hundred and
sixteen decidable integer identities.  The value four occurs at the sixteen
spanning trees of `K4` and the value zero at the four triangles and at every
repeated label. -/
theorem kfourMinorInt_eq_zero_or_four (labelA labelB labelC : Fin 6) :
    kfourMinorInt labelA labelB labelC = 0 ∨ kfourMinorInt labelA labelB labelC = 4 := by
  fin_cases labelA <;> fin_cases labelB <;> fin_cases labelC <;> decide

/-- The integer core is capped by four. -/
theorem kfourMinorInt_le_four (labelA labelB labelC : Fin 6) :
    kfourMinorInt labelA labelB labelC ≤ 4 := by
  rcases kfourMinorInt_eq_zero_or_four labelA labelB labelC with h | h <;> omega

/-- The three-minor of the graphic point is the integer core over sixty-four. -/
theorem principalMinorThree_kfourEdgeProjection (labelA labelB labelC : Fin 6) :
    principalMinorThree kfourEdgeProjection labelA labelB labelC
      = (kfourMinorInt labelA labelB labelC : ℝ) / 64 := by
  simp only [principalMinorThree, kfourEdgeProjection_apply, kfourMinorInt]
  push_cast
  ring

/-- **THE GRAPHIC POINT'S PLÜCKER PROFILE IS CAPPED AT ONE SIXTEENTH.**  Every
three-minor of `Gtz.kfourEdgeProjection` is at most `1/16`, and sixteen of the
twenty attain it. -/
theorem principalMinorThree_kfourEdgeProjection_le (labelA labelB labelC : Fin 6) :
    principalMinorThree kfourEdgeProjection labelA labelB labelC ≤ 1 / 16 := by
  rw [principalMinorThree_kfourEdgeProjection]
  have hle : (kfourMinorInt labelA labelB labelC : ℝ) ≤ 4 := by
    exact_mod_cast kfourMinorInt_le_four labelA labelB labelC
  linarith

/-- The integer core at the star `{0,1,2}`. -/
theorem kfourMinorInt_zeroOneTwo : kfourMinorInt 0 1 2 = 4 := by decide

/-- The integer core at the path `{0,1,4}`. -/
theorem kfourMinorInt_zeroOneFour : kfourMinorInt 0 1 4 = 4 := by decide

/-- The integer core at the triangle `{0,1,3}`. -/
theorem kfourMinorInt_zeroOneThree : kfourMinorInt 0 1 3 = 0 := by decide

/-- The spanning-tree value: the triple `{0,1,2}` attains one sixteenth. -/
theorem principalMinorThree_kfourEdgeProjection_zeroOneTwo :
    principalMinorThree kfourEdgeProjection 0 1 2 = 1 / 16 := by
  rw [principalMinorThree_kfourEdgeProjection, kfourMinorInt_zeroOneTwo]
  norm_num

/-- A second spanning tree with the SAME weight: the triple `{0,1,4}`. -/
theorem principalMinorThree_kfourEdgeProjection_zeroOneFour :
    principalMinorThree kfourEdgeProjection 0 1 4 = 1 / 16 := by
  rw [principalMinorThree_kfourEdgeProjection, kfourMinorInt_zeroOneFour]
  norm_num

/-- A triangle of `K4` carries weight zero: the triple `{0,1,3}` is dependent. -/
theorem principalMinorThree_kfourEdgeProjection_zeroOneThree :
    principalMinorThree kfourEdgeProjection 0 1 3 = 0 := by
  rw [principalMinorThree_kfourEdgeProjection, kfourMinorInt_zeroOneThree]
  norm_num

/-! ## 5. The refutation of the mass floor -/

/-- **THE MASS FLOOR DOES NOT REACH `17/270`.**  The graphic point of `K4` is a
symmetric idempotent of trace three whose every three-minor is at most `1/16`,
and `1/16 < 17/270`.  So the reduction of the objective to a floor on the
determinantal measure FAILS, and it fails by the exact deficit `1/2160`. -/
theorem not_massFloorReaches_seventeen_twoSeventieths : ¬ MassFloorReaches (17 / 270) := by
  intro hfloor
  obtain ⟨labelA, labelB, labelC, -, -, -, hge⟩ :=
    hfloor kfourEdgeProjection kfourEdgeProjection_symm kfourEdgeProjection_idempotent
      kfourEdgeProjection_trace
  have hle := principalMinorThree_kfourEdgeProjection_le labelA labelB labelC
  norm_num at hge hle
  linarith

/-- The deficit, exactly.  The level the reduction needs and the level the
graphic point supplies differ by one part in two thousand one hundred and
sixty. -/
theorem massFloor_deficit : (17:ℝ) / 270 - 1 / 16 = 1 / 2160 := by norm_num

/-- **AND THE FLOOR FAILS AT EVERY LEVEL ABOVE ONE SIXTEENTH.**  The graphic
point caps the whole lane, so no strengthening of the pigeonhole can reach past
`1/16` and the reduction is dead for every level in `(1/16, 1]`. -/
theorem not_massFloorReaches_of_one_sixteenth_lt {level : ℝ} (hlevel : 1 / 16 < level) :
    ¬ MassFloorReaches level := by
  intro hfloor
  obtain ⟨labelA, labelB, labelC, -, -, -, hge⟩ :=
    hfloor kfourEdgeProjection kfourEdgeProjection_symm kfourEdgeProjection_idempotent
      kfourEdgeProjection_trace
  have hle := principalMinorThree_kfourEdgeProjection_le labelA labelB labelC
  linarith

/-! ## 6. The blindness of the determinantal measure

The refutation above is quantitative and narrow.  The reason behind it is not.
At the graphic point sixteen triples share the weight `1/16` while only four of
them dominate, so the measure cannot see the difference at all. -/

/-- The shifted graphic point at the uniform weight: `P - (1/6) * I`. -/
noncomputable def kfourShift : Matrix (Fin 6) (Fin 6) ℝ :=
  kfourEdgeProjection - (1 / 6 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)

/-- The integer core of the shifted graphic point, cleared by twelve. -/
def kfourShiftInt (labelA labelB : Fin 6) : ℤ :=
  3 * kfourGramInt labelA labelB - (if labelA = labelB then 2 else 0)

/-- The shifted matrix is the integer core over twelve. -/
theorem kfourShift_apply (labelA labelB : Fin 6) :
    kfourShift labelA labelB = (kfourShiftInt labelA labelB : ℝ) / 12 := by
  rw [kfourShift, kfourShiftInt]
  by_cases hEq : labelA = labelB
  · subst hEq
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      kfourEdgeProjection_apply]
    rw [kfourGramInt_diag]
    norm_num
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hEq, smul_eq_mul,
      kfourEdgeProjection_apply, if_neg hEq]
    push_cast
    ring

/-- The integer core of the shifted three-minor, cleared by one thousand seven
hundred and twenty-eight. -/
def kfourShiftMinorInt (labelA labelB labelC : Fin 6) : ℤ :=
  kfourShiftInt labelA labelA * kfourShiftInt labelB labelB * kfourShiftInt labelC labelC
    - kfourShiftInt labelA labelA * kfourShiftInt labelB labelC * kfourShiftInt labelC labelB
    - kfourShiftInt labelA labelB * kfourShiftInt labelB labelA * kfourShiftInt labelC labelC
    + kfourShiftInt labelA labelB * kfourShiftInt labelB labelC * kfourShiftInt labelC labelA
    + kfourShiftInt labelA labelC * kfourShiftInt labelB labelA * kfourShiftInt labelC labelB
    - kfourShiftInt labelA labelC * kfourShiftInt labelB labelB * kfourShiftInt labelC labelA

/-- The shifted three-minor is its integer core over `12 ^ 3`. -/
theorem principalMinorThree_kfourShift (labelA labelB labelC : Fin 6) :
    principalMinorThree kfourShift labelA labelB labelC
      = (kfourShiftMinorInt labelA labelB labelC : ℝ) / 1728 := by
  simp only [principalMinorThree, kfourShift_apply, kfourShiftMinorInt]
  push_cast
  ring

/-- **THE SHIFTED PROFILE TAKES EXACTLY THREE VALUES.**  Ten at the four stars,
minus eight at the twelve paths, minus ninety-eight at the four triangles, and
zero at every repeated label.  Two hundred and sixteen decidable identities. -/
theorem kfourShiftMinorInt_mem (labelA labelB labelC : Fin 6) :
    kfourShiftMinorInt labelA labelB labelC = 0 ∨ kfourShiftMinorInt labelA labelB labelC = 10
      ∨ kfourShiftMinorInt labelA labelB labelC = -8
      ∨ kfourShiftMinorInt labelA labelB labelC = -98 := by
  fin_cases labelA <;> fin_cases labelB <;> fin_cases labelC <;> decide

/-- The shifted integer core at the star `{0,1,2}`. -/
theorem kfourShiftMinorInt_zeroOneTwo : kfourShiftMinorInt 0 1 2 = 10 := by decide

/-- The shifted integer core at the path `{0,1,4}`. -/
theorem kfourShiftMinorInt_zeroOneFour : kfourShiftMinorInt 0 1 4 = -8 := by decide

/-- A star of `K4` dominates: the triple `{0,1,2}` has a strictly positive
shifted minor. -/
theorem principalMinorThree_kfourShift_zeroOneTwo :
    principalMinorThree kfourShift 0 1 2 = 5 / 864 := by
  rw [principalMinorThree_kfourShift, kfourShiftMinorInt_zeroOneTwo]
  norm_num

/-- A path of `K4` does not: the triple `{0,1,4}` has a strictly negative shifted
minor, at the SAME Plücker weight as the star above. -/
theorem principalMinorThree_kfourShift_zeroOneFour :
    principalMinorThree kfourShift 0 1 4 = -(1 / 216) := by
  rw [principalMinorThree_kfourShift, kfourShiftMinorInt_zeroOneFour]
  norm_num

/-- **THE DETERMINANTAL MEASURE CANNOT SELECT.**  One symmetric idempotent of
trace three on six labels carries two triples of EQUAL Plücker weight `1/16`
whose shifted minors have OPPOSITE signs.  No function of the determinantal
measure alone can compute, bound below, or certify the selection margin.

This is the Plücker companion of `Gtz.margin_not_determined_by_leverage_diagonal`.
Together the two close both coordinate systems the campaign has searched for a
selection rule in: the diagonal of the projection and its three-minors. -/
theorem margin_not_determined_by_pluckerWeight :
    ∃ form : Matrix (Fin 6) (Fin 6) ℝ, formᵀ = form ∧ form * form = form
      ∧ Matrix.trace form = 3
      ∧ ∃ firstA firstB firstC secondA secondB secondC : Fin 6,
          principalMinorThree form firstA firstB firstC
              = principalMinorThree form secondA secondB secondC
            ∧ 0 < principalMinorThree (form - (1 / 6 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ))
                firstA firstB firstC
            ∧ principalMinorThree (form - (1 / 6 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ))
                secondA secondB secondC < 0 := by
  refine ⟨kfourEdgeProjection, kfourEdgeProjection_symm, kfourEdgeProjection_idempotent,
    kfourEdgeProjection_trace, 0, 1, 2, 0, 1, 4, ?_, ?_, ?_⟩
  · rw [principalMinorThree_kfourEdgeProjection_zeroOneTwo,
      principalMinorThree_kfourEdgeProjection_zeroOneFour]
  · have h := principalMinorThree_kfourShift_zeroOneTwo
    rw [kfourShift] at h
    rw [h]; norm_num
  · have h := principalMinorThree_kfourShift_zeroOneFour
    rw [kfourShift] at h
    rw [h]; norm_num

/-- **THE MEASURE IS BLIND AT A DOMINATING TRIPLE TOO.**  The two triples above
carry the same weight and the star's block is the one that dominates, so the
blindness is not an artefact of comparing a basis with a dependent set. -/
theorem pluckerWeight_blind_at_dominating :
    principalMinorThree kfourEdgeProjection 0 1 2
        = principalMinorThree kfourEdgeProjection 0 1 4
      ∧ principalMinorThree kfourShift 0 1 2 ≠ principalMinorThree kfourShift 0 1 4 := by
  refine ⟨?_, ?_⟩
  · rw [principalMinorThree_kfourEdgeProjection_zeroOneTwo,
      principalMinorThree_kfourEdgeProjection_zeroOneFour]
  · rw [principalMinorThree_kfourShift_zeroOneTwo, principalMinorThree_kfourShift_zeroOneFour]
    norm_num

/-! ## 7. Past the pigeonhole, and it is real only

Two disjoint pivot stars each carry a triple of small weight.  Adding the cap on
the remaining eighteen triples to those two gives a quadratic inequality on the
maximum, and it clears the free pigeonhole strictly.  The input is the landed
Plücker spread law, which is a REAL statement — the Hermitian field admits twenty
equal weights and the floor there is exactly one twentieth. -/

/-- **THE TWO-SMALL-TRIPLE BUDGET.**  If two distinct triples carry weight at
most `small` and every triple carries weight at most `cap`, the determinantal
mass one forces `1 ≤ 18 * cap + 2 * small`. -/
theorem massFloor_of_two_small (D : WeightedDesign 6 3) {cap small : ℝ}
    {firstSet secondSet : Finset (Fin 6)}
    (hfirst : firstSet ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3)
    (hsecond : secondSet ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3)
    (hne : firstSet ≠ secondSet)
    (hcap : ∀ labels ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3, pluckerWeight D labels ≤ cap)
    (hfirstSmall : pluckerWeight D firstSet ≤ small)
    (hsecondSmall : pluckerWeight D secondSet ≤ small) :
    1 ≤ 18 * cap + 2 * small := by
  classical
  set whole := (Finset.univ : Finset (Fin 6)).powersetCard 3 with hwhole
  set pair : Finset (Finset (Fin 6)) := {firstSet, secondSet} with hpair
  have hsub : pair ⊆ whole := by
    intro x hx
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hfirst
    · exact hsecond
  have hpaircard : pair.card = 2 := by
    rw [hpair, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hsplit : (∑ labels ∈ whole \ pair, pluckerWeight D labels)
      + ∑ labels ∈ pair, pluckerWeight D labels
      = ∑ labels ∈ whole, pluckerWeight D labels := Finset.sum_sdiff hsub
  have hpairsum : (∑ labels ∈ pair, pluckerWeight D labels)
      = pluckerWeight D firstSet + pluckerWeight D secondSet := by
    rw [hpair, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  have hinter : pair ∩ whole = pair := Finset.inter_eq_left.mpr hsub
  have hrestcard : (whole \ pair).card = 18 := by
    rw [Finset.card_sdiff, hinter, hpaircard, hwhole, card_powersetCard_three_six]
  have hrest : (∑ labels ∈ whole \ pair, pluckerWeight D labels) ≤ 18 * cap := by
    have := sum_le_card_mul_of_le (whole \ pair) (pluckerWeight D) cap
      fun x hx => hcap x (Finset.mem_sdiff.mp hx).1
    rwa [hrestcard] at this

  have htotal : (∑ labels ∈ whole, pluckerWeight D labels) = 1 := sum_pluckerWeight_eq_one D
  rw [hpairsum, htotal] at hsplit
  linarith

/-- **THE SPREAD FLOOR, ROOT FREE.**  If the two small triples come from the
Plücker spread law, so that `2 * small ^ 2 ≤ cap ^ 2`, the budget becomes a
quadratic inequality on the cap alone. -/
theorem sq_massFloor_of_spread {cap small : ℝ} (hsmall : 0 ≤ small)
    (hbudget : 1 ≤ 18 * cap + 2 * small) (hspread : 2 * small ^ 2 ≤ cap ^ 2)
    (hcapSmall : cap ≤ 1 / 18) :
    (1 - 18 * cap) ^ 2 ≤ 2 * cap ^ 2 := by
  have hpos : 0 ≤ 1 - 18 * cap := by linarith
  have hle : 1 - 18 * cap ≤ 2 * small := by linarith
  nlinarith [hle, hpos, hsmall, hspread, sq_nonneg (2 * small - (1 - 18 * cap))]

/-- **AND THE SPREAD FLOOR STRICTLY BEATS THE PIGEONHOLE.**  A cap admitting two
spread-small triples exceeds `51/1000`, which is strictly more than the free
`1/20`.  The sharp value is `1 / (18 + √2)`. -/
theorem massFloor_gt_of_spread {cap small : ℝ} (hsmall : 0 ≤ small)
    (hbudget : 1 ≤ 18 * cap + 2 * small) (hspread : 2 * small ^ 2 ≤ cap ^ 2) :
    51 / 1000 < cap := by
  by_contra hle
  push Not at hle
  have hcapSmall : cap ≤ 1 / 18 := by linarith
  have hquad := sq_massFloor_of_spread hsmall hbudget hspread hcapSmall
  nlinarith [hquad, hle]

/-- The free pigeonhole is never tight: at `(6,3)` no design spreads its
determinantal mass evenly over the twenty triples. -/
theorem massFloor_ne_one_twentieth {cap small : ℝ} (hsmall : 0 ≤ small)
    (hbudget : 1 ≤ 18 * cap + 2 * small) (hspread : 2 * small ^ 2 ≤ cap ^ 2) :
    (1:ℝ) / 20 < cap := by
  have h := massFloor_gt_of_spread hsmall hbudget hspread
  linarith

/-! ## 8. The reduction the floor was built for

The threshold that the Plücker weight must beat is sign free, and its
determinantal-weighted total at a uniform weight is a universal constant.  This
records the arithmetic that made `17/270` the level to aim at, so that the
refutation above is anchored to a stated target. -/

/-- The **THRESHOLD** of a triple: the value the squared bracket must beat for the
block to dominate.  It reads leverages and SQUARED pairings only, so it carries
no sign. -/
noncomputable def tripleThreshold {m : ℕ} (form : Matrix (Fin m) (Fin m) ℝ)
    (weight : Fin m → ℝ) (labelA labelB labelC : Fin m) : ℝ :=
  principalMinorThree form labelA labelB labelC
    - principalMinorThree (form - Matrix.diagonal weight) labelA labelB labelC

/-- **THE OBJECTIVE AT A TRIPLE IS THE WEIGHT BEATING THE THRESHOLD.**  By
construction, and it is the reduction the mass floor was aiming at. -/
theorem principalMinorThree_shift_pos_iff {m : ℕ} (form : Matrix (Fin m) (Fin m) ℝ)
    (weight : Fin m → ℝ) (labelA labelB labelC : Fin m) :
    0 < principalMinorThree (form - Matrix.diagonal weight) labelA labelB labelC
      ↔ tripleThreshold form weight labelA labelB labelC
          < principalMinorThree form labelA labelB labelC := by
  rw [tripleThreshold]
  constructor <;> intro h <;> linarith

/-- At the graphic point of `K4` the threshold of a star is `49/864` and its
Plücker weight `1/16 = 54/864` clears it.  The four stars are exactly the four
dominating triples, and the landed margin there is `1/12`. -/
theorem tripleThreshold_kfourEdgeProjection_zeroOneTwo :
    tripleThreshold kfourEdgeProjection (fun _ => (1:ℝ) / 6) 0 1 2 = 49 / 864 := by
  have hdiag : kfourEdgeProjection - Matrix.diagonal (fun _ : Fin 6 => (1:ℝ) / 6) = kfourShift := by
    rw [kfourShift]
    ext labelA labelB
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hEq : labelA = labelB <;> simp [hEq]
  rw [tripleThreshold, hdiag, principalMinorThree_kfourEdgeProjection_zeroOneTwo,
    principalMinorThree_kfourShift_zeroOneTwo]
  norm_num

/-- And at a path the threshold is `57/864`, which the same weight `54/864` does
NOT clear.  The threshold — not the measure — is what separates the two, which is
the content of `Gtz.margin_not_determined_by_pluckerWeight`. -/
theorem tripleThreshold_kfourEdgeProjection_zeroOneFour :
    tripleThreshold kfourEdgeProjection (fun _ => (1:ℝ) / 6) 0 1 4 = 58 / 864 := by
  have hdiag : kfourEdgeProjection - Matrix.diagonal (fun _ : Fin 6 => (1:ℝ) / 6) = kfourShift := by
    rw [kfourShift]
    ext labelA labelB
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hEq : labelA = labelB <;> simp [hEq]
  rw [tripleThreshold, hdiag, principalMinorThree_kfourEdgeProjection_zeroOneFour,
    principalMinorThree_kfourShift_zeroOneFour]
  norm_num

/-! ## 9. The floor in explicit labels

Every cell in the campaign is stated on three explicit labels, and the landed
determinantal identities are stated on subtype-indexed blocks.  The bridge of
section 1 carries the floor across, so the mass floor becomes usable by a cell
without any further index work. -/

/-- The three sorted elements of a three-element label set are strictly
increasing, hence pairwise distinct. -/
theorem orderIsoOfFin_coe_lt {n : ℕ} (labels : Finset (Fin n)) (hcard : labels.card = 3)
    {i j : Fin 3} (hij : i < j) :
    ((labels.orderIsoOfFin hcard i : Fin n)) < ((labels.orderIsoOfFin hcard j : Fin n)) :=
  (labels.orderIsoOfFin hcard).strictMono hij

/-- **THE MASS FLOOR, IN EXPLICIT LABELS.**  Some three distinct labels of a
`(6,3)` design carry a principal minor of at least one twentieth.  This is the
consumable form: it names the labels a cell can read. -/
theorem exists_principalMinorThree_ge_one_twentieth (D : WeightedDesign 6 3) :
    ∃ labelA labelB labelC : Fin 6, labelA ≠ labelB ∧ labelA ≠ labelC ∧ labelB ≠ labelC
      ∧ (1:ℝ) / 20 ≤ principalMinorThree (projectionOfDesign D) labelA labelB labelC := by
  classical
  obtain ⟨labels, hmem, hge⟩ := exists_pluckerWeight_ge_one_twentieth D
  have hcard : labels.card = 3 := (Finset.mem_powersetCard.mp hmem).2
  have hlt01 := orderIsoOfFin_coe_lt labels hcard (i := 0) (j := 1) (by decide)
  have hlt02 := orderIsoOfFin_coe_lt labels hcard (i := 0) (j := 2) (by decide)
  have hlt12 := orderIsoOfFin_coe_lt labels hcard (i := 1) (j := 2) (by decide)
  refine ⟨labels.orderIsoOfFin hcard 0, labels.orderIsoOfFin hcard 1,
    labels.orderIsoOfFin hcard 2, ne_of_lt hlt01, ne_of_lt hlt02, ne_of_lt hlt12, ?_⟩
  rwa [pluckerWeight, det_submatrix_val_eq_principalMinorThree] at hge

/-- **THE MASS FLOOR IS A TRUE FLOOR AT ONE TWENTIETH.**  The level `1/20` IS
reached, so the refutation of section 5 is a refutation of the LEVEL and not of
the shape of the statement. -/
theorem massFloorReaches_one_twentieth_of_design (D : WeightedDesign 6 3) :
    ∃ labelA labelB labelC : Fin 6, labelA ≠ labelB ∧ labelA ≠ labelC ∧ labelB ≠ labelC
      ∧ (1:ℝ) / 20 ≤ principalMinorThree (projectionOfDesign D) labelA labelB labelC :=
  exists_principalMinorThree_ge_one_twentieth D

/-! ## 10. The graphic point, calibrated in kernel

The twenty sorted triples, with the two integer cores summed over them.  The
Plücker mass reproduces the landed volume-sampling total and the shifted mass
reproduces the landed universal constant `−7/27`, both from the same explicit
enumeration.  Neither is assumed: both are recomputed. -/

/-- The twenty sorted triples of six labels. -/
def sortedTripleList : List (Fin 6 × Fin 6 × Fin 6) :=
  [(0,1,2), (0,1,3), (0,1,4), (0,1,5), (0,2,3), (0,2,4), (0,2,5), (0,3,4), (0,3,5), (0,4,5),
   (1,2,3), (1,2,4), (1,2,5), (1,3,4), (1,3,5), (1,4,5), (2,3,4), (2,3,5), (2,4,5), (3,4,5)]

/-- The list has twenty entries, one for each three-element label set. -/
theorem sortedTripleList_length : sortedTripleList.length = 20 := by decide

/-- **THE PLÜCKER MASS AT THE GRAPHIC POINT IS ONE.**  Sixteen cores of four and
four of zero.  This recomputes the landed volume-sampling total
`Gtz.sum_det_projectionMinors_rank` at an explicit point, from the integer core
alone. -/
theorem sum_kfourMinorInt :
    (sortedTripleList.map fun t => kfourMinorInt t.1 t.2.1 t.2.2).sum = 64 := by decide

/-- **THE SHIFTED MASS AT THE GRAPHIC POINT IS `−7/27`.**  Four cores of ten,
twelve of minus eight, four of minus ninety-eight.  Their total is `−448`, and
`−448 / 1728 = −7/27`, which is the landed universal value of
`Gtz.sum_det_shiftedChartMinors_sixThree`.  The two computations are independent:
that one is a polynomial identity, this one an integer enumeration. -/
theorem sum_kfourShiftMinorInt :
    (sortedTripleList.map fun t => kfourShiftMinorInt t.1 t.2.1 t.2.2).sum = -448 := by decide

/-- The calibration, as a rational statement: the shifted mass at the graphic
point is exactly the landed universal constant. -/
theorem kfourShift_mass_eq_neg_seven_twentySevenths :
    ((sortedTripleList.map fun t => kfourShiftMinorInt t.1 t.2.1 t.2.2).sum : ℝ) / 1728
      = -(7 / 27) := by
  rw [sum_kfourShiftMinorInt]
  norm_num

/-- The second power sum of the Plücker cores. -/
theorem sum_sq_kfourMinorInt :
    (sortedTripleList.map fun t => kfourMinorInt t.1 t.2.1 t.2.2 ^ 2).sum = 256 := by decide

/-- The third power sum of the Plücker cores. -/
theorem sum_cube_kfourMinorInt :
    (sortedTripleList.map fun t => kfourMinorInt t.1 t.2.1 t.2.2 ^ 3).sum = 1024 := by decide

/-- **THE MOMENT LADDER IS SHARP.**  At the graphic point the ratio of the third
to the second power sum of the Plücker weights is `1/16`, which is exactly the
maximum.  So `Gtz.le_cap_of_sum_pow_ratio` is attained, and no rung of the ladder
above the second can be improved by a constant. -/
theorem momentRatio_kfour_eq_max :
    ((((sortedTripleList.map fun t => kfourMinorInt t.1 t.2.1 t.2.2 ^ 3).sum : ℤ) : ℝ) / 64 ^ 3)
        / ((((sortedTripleList.map fun t => kfourMinorInt t.1 t.2.1 t.2.2 ^ 2).sum : ℤ) : ℝ)
            / 64 ^ 2)
      = 1 / 16 := by
  rw [sum_cube_kfourMinorInt, sum_sq_kfourMinorInt]
  norm_num

/-! ## 11. The objective survives the refutation

The mass floor dies at the graphic point, but the objective does not: four
triples dominate there.  So section 5 refutes a REDUCTION and not the statement
the reduction was aiming at. -/

/-- The first star of `K4`. -/
theorem kfourShiftMinorInt_star_one : kfourShiftMinorInt 0 1 2 = 10 := kfourShiftMinorInt_zeroOneTwo

/-- The second star of `K4`. -/
theorem kfourShiftMinorInt_star_two : kfourShiftMinorInt 0 3 4 = 10 := by decide

/-- The third star of `K4`. -/
theorem kfourShiftMinorInt_star_three : kfourShiftMinorInt 1 3 5 = 10 := by decide

/-- The fourth star of `K4`. -/
theorem kfourShiftMinorInt_star_four : kfourShiftMinorInt 2 4 5 = 10 := by decide

/-- **THE OBJECTIVE HOLDS AT THE GRAPHIC POINT.**  Some triple of
`Gtz.kfourEdgeProjection` strictly dominates the uniform weight diagonal, so the
configuration that kills the mass floor is not a counterexample to anything the
campaign wants.  The landed margin there is `1/12`. -/
theorem exists_dominating_triple_kfourShift :
    ∃ labelA labelB labelC : Fin 6, labelA ≠ labelB ∧ labelA ≠ labelC ∧ labelB ≠ labelC
      ∧ 0 < principalMinorThree kfourShift labelA labelB labelC := by
  refine ⟨0, 1, 2, by decide, by decide, by decide, ?_⟩
  rw [principalMinorThree_kfourShift_zeroOneTwo]
  norm_num

/-- **AND FOUR TRIPLES DOMINATE, NOT ONE.**  The four stars of `K4`, each at
`5/864`. -/
theorem four_dominating_triples_kfourShift :
    0 < principalMinorThree kfourShift 0 1 2 ∧ 0 < principalMinorThree kfourShift 0 3 4
      ∧ 0 < principalMinorThree kfourShift 1 3 5 ∧ 0 < principalMinorThree kfourShift 2 4 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [principalMinorThree_kfourShift] <;>
    [rw [kfourShiftMinorInt_star_one]; rw [kfourShiftMinorInt_star_two];
     rw [kfourShiftMinorInt_star_three]; rw [kfourShiftMinorInt_star_four]] <;>
    norm_num

/-! ## 12. The sharp level

The graphic point caps the mass floor at `1/16`, and a directed descent over the
Grassmannian of three-planes in six-space finds no configuration below it.  The
attainment is a theorem, the optimality is not. -/

/-- **THE SHARP LEVEL IS ATTAINED.**  The graphic point of `K4` reaches exactly
`1/16` and no more, so `1/16` is the largest level that the mass floor could
possibly reach. -/
theorem massFloor_sharp_at_kfour :
    (∀ labelA labelB labelC : Fin 6,
        principalMinorThree kfourEdgeProjection labelA labelB labelC ≤ 1 / 16)
      ∧ principalMinorThree kfourEdgeProjection 0 1 2 = 1 / 16 :=
  ⟨principalMinorThree_kfourEdgeProjection_le, principalMinorThree_kfourEdgeProjection_zeroOneTwo⟩

/-! ## 13. What the measure DOES decide

The measure cannot select among its support, but it does cut the search down to
that support: a dominating selection has strictly positive Plücker weight.  So
the four triangles of the graphic point are excluded outright, and every search
may be restricted to the bases of the underlying matroid. -/

/-- **A DOMINATING SELECTION HAS POSITIVE PLÜCKER WEIGHT.**  If the block gap is
positive definite then the block itself is the sum of two positive definite
matrices, so its determinant is strictly positive.  A selection of Plücker weight
zero — a circuit of the underlying matroid — can never dominate. -/
theorem det_projectionBlock_pos_of_posDef {m k : ℕ} (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m)
    (hpd : ((projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).PosDef) :
    0 < ((projectionOfDesign D).submatrix pick pick).det := by
  have hdiag : (Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).PosDef :=
    Matrix.PosDef.diagonal fun selectedIndex => D.weight_pos (pick selectedIndex)
  have hsum : ((projectionOfDesign D).submatrix pick pick).PosDef := by
    have := hpd.add hdiag
    simpa using this
  exact hsum.det_pos

/-- **THE SUPPORT CUT, IN EXPLICIT LABELS.**  A three-element selection whose
principal minor vanishes cannot dominate.  The mass floor therefore lives
entirely on the bases, and at the graphic point that is sixteen of twenty. -/
theorem not_posDef_of_det_projectionBlock_eq_zero {m k : ℕ} (D : WeightedDesign m k) {size : ℕ}
    (pick : Fin size → Fin m)
    (hzero : ((projectionOfDesign D).submatrix pick pick).det = 0) :
    ¬ ((projectionOfDesign D).submatrix pick pick
        - Matrix.diagonal (fun selectedIndex => D.weight (pick selectedIndex))).PosDef := by
  intro hpd
  have := det_projectionBlock_pos_of_posDef D pick hpd
  rw [hzero] at this
  exact lt_irrefl 0 this

/-! ## 14. The joint blindness

The landed `Gtz.margin_not_determined_by_leverage_diagonal` closes the diagonal.
Section 6 closes the measure.  The graphic point closes them TOGETHER, because it
carries a constant diagonal AND a constant weight on sixteen triples while its
verdicts differ.  So no certificate reading the leverage diagonal and the
determinantal measure jointly can decide domination either. -/

/-- Every leverage of the graphic point is one half, so the diagonal is constant
across all six labels and carries no information about any selection. -/
theorem kfourEdgeProjection_diag_const (labelA labelB : Fin 6) :
    kfourEdgeProjection labelA labelA = kfourEdgeProjection labelB labelB := by
  rw [kfourEdgeProjection_diag, kfourEdgeProjection_diag]

/-- **NEITHER COORDINATE SYSTEM DECIDES, AND NOR DO THE TWO TOGETHER.**  At the
graphic point of `K4` the six leverages are all `1/2` and two triples carry the
identical Plücker weight `1/16`, yet one dominates the uniform weight and the
other does not.  Any certificate whose input is the leverage diagonal together
with the determinantal measure is therefore blind to the objective.

This strictly strengthens both `Gtz.margin_not_determined_by_leverage_diagonal`
and `Gtz.margin_not_determined_by_pluckerWeight`: those refute each reading
separately, this refutes their conjunction at a single configuration. -/
theorem margin_not_determined_by_diagonal_and_pluckerWeight :
    (∀ labelA labelB : Fin 6,
        kfourEdgeProjection labelA labelA = kfourEdgeProjection labelB labelB)
      ∧ principalMinorThree kfourEdgeProjection 0 1 2
          = principalMinorThree kfourEdgeProjection 0 1 4
      ∧ 0 < principalMinorThree kfourShift 0 1 2
      ∧ principalMinorThree kfourShift 0 1 4 < 0 := by
  refine ⟨kfourEdgeProjection_diag_const, ?_, ?_, ?_⟩
  · rw [principalMinorThree_kfourEdgeProjection_zeroOneTwo,
      principalMinorThree_kfourEdgeProjection_zeroOneFour]
  · rw [principalMinorThree_kfourShift_zeroOneTwo]; norm_num
  · rw [principalMinorThree_kfourShift_zeroOneFour]; norm_num

/-- **THE SEPARATOR IS THE THRESHOLD.**  What the two blind readings miss is
exactly `Gtz.tripleThreshold`, which differs at the two triples by `9/864` while
every other landed reading of them agrees.  So the campaign's remaining content
is a statement about the threshold and not about the measure. -/
theorem tripleThreshold_separates :
    tripleThreshold kfourEdgeProjection (fun _ => (1:ℝ) / 6) 0 1 4
        - tripleThreshold kfourEdgeProjection (fun _ => (1:ℝ) / 6) 0 1 2
      = 9 / 864 := by
  rw [tripleThreshold_kfourEdgeProjection_zeroOneFour,
    tripleThreshold_kfourEdgeProjection_zeroOneTwo]
  norm_num

/-! ## 15. The support cut reaches the registry

The objective quantifies over all twenty triples of every primitive design.  The
support cut says every dominator lies in the support of the determinantal
measure, so the quantifier may be narrowed to the bases of the underlying matroid
WITHOUT weakening the statement.  That narrowing composes to all five on-path
obligations through the landed `Gtz.allFiveOnPath_of_projectionBlockSelects`. -/

/-- The block determinant read along the order embedding is the Sarrus form at
the three sorted labels. -/
theorem det_submatrix_orderEmbOfFin_eq_principalMinorThree {n : ℕ}
    (form : Matrix (Fin n) (Fin n) ℝ) (labels : Finset (Fin n)) (hcard : labels.card = 3) :
    (form.submatrix (labels.orderEmbOfFin hcard) (labels.orderEmbOfFin hcard)).det
      = principalMinorThree form (labels.orderEmbOfFin hcard 0) (labels.orderEmbOfFin hcard 1)
          (labels.orderEmbOfFin hcard 2) := by
  rw [Matrix.det_fin_three]
  rfl

/-- The Plücker weight of a three-element set is its order-embedded block
determinant.  The two index conventions of the corpus agree. -/
theorem pluckerWeight_eq_det_submatrix_orderEmbOfFin {m k : ℕ} (D : WeightedDesign m k)
    (labels : Finset (Fin m)) (hcard : labels.card = 3) :
    pluckerWeight D labels
      = ((projectionOfDesign D).submatrix (labels.orderEmbOfFin hcard)
          (labels.orderEmbOfFin hcard)).det := by
  rw [pluckerWeight, det_submatrix_val_eq_principalMinorThree _ labels hcard,
    det_submatrix_orderEmbOfFin_eq_principalMinorThree]
  rfl

/-- **THE SUPPORT CUT AT THE OBJECTIVE'S OWN INDEXING.**  A selection whose block
gap is positive definite carries a strictly positive Plücker weight. -/
theorem pluckerWeight_pos_of_posDef_projectionBlockGap (D : WeightedDesign 6 3)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hpd : (projectionBlockGap D selected hcard).PosDef) :
    0 < pluckerWeight D selected := by
  rw [pluckerWeight_eq_det_submatrix_orderEmbOfFin D selected hcard]
  exact det_projectionBlock_pos_of_posDef D (selected.orderEmbOfFin hcard) hpd

/-- **THE OBJECTIVE, RESTRICTED TO THE SUPPORT.**  The same statement as
`Gtz.ProjectionBlockSelects` with the search confined to selections of strictly
positive determinantal weight. -/
def ProjectionBlockSelectsOnSupport : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
      0 < pluckerWeight design selected ∧ (projectionBlockGap design selected hcard).PosDef

/-- **THE NARROWING IS FREE.**  The objective and its restriction to the support
of the determinantal measure are the SAME statement.  The forward direction is
the support cut, the backward direction drops a conjunct.

At the graphic point of `K4` this drops four of the twenty candidates, and in
general it drops every circuit of the underlying matroid. -/
theorem projectionBlockSelects_iff_onSupport :
    ProjectionBlockSelects ↔ ProjectionBlockSelectsOnSupport := by
  constructor
  · intro hsel design hprimitive
    obtain ⟨selected, hcard, hpd⟩ := hsel design hprimitive
    exact ⟨selected, hcard,
      pluckerWeight_pos_of_posDef_projectionBlockGap design selected hcard hpd, hpd⟩
  · intro hsupp design hprimitive
    obtain ⟨selected, hcard, -, hpd⟩ := hsupp design hprimitive
    exact ⟨selected, hcard, hpd⟩

/-- **THE SUPPORT-RESTRICTED OBJECTIVE RETIRES ALL FIVE ON-PATH OBLIGATIONS.**
Composing the free narrowing with the landed
`Gtz.allFiveOnPath_of_projectionBlockSelects`.  So a proof that searches only the
bases of the matroid is enough, and it is enough for every one of the five. -/
theorem allFiveOnPath_of_projectionBlockSelectsOnSupport
    (hsupp : ProjectionBlockSelectsOnSupport) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal ∧
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines ∧
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  allFiveOnPath_of_projectionBlockSelects (projectionBlockSelects_iff_onSupport.mpr hsupp)

/-- The consolidated design statement follows from the support-restricted form
too, through the landed restatement. -/
theorem consolidatedStrictTripleDesign_of_projectionBlockSelectsOnSupport
    (hsupp : ProjectionBlockSelectsOnSupport) : ConsolidatedStrictTripleDesign :=
  consolidatedStrictTripleDesign_iff_projectionBlockSelects.mpr
    (projectionBlockSelects_iff_onSupport.mpr hsupp)

/-- And so does the chart form, through the landed gauge equivalence. -/
theorem consolidatedStrictTriple_of_projectionBlockSelectsOnSupport
    (hsupp : ProjectionBlockSelectsOnSupport) : ConsolidatedStrictTriple :=
  consolidatedStrictTriple_of_projectionBlockSelects
    (projectionBlockSelects_iff_onSupport.mpr hsupp)

/-- **THE SUPPORT IS NEVER EMPTY, AND IT CARRIES MASS.**  Some selection of every
`(6,3)` design has Plücker weight at least one twentieth, so the narrowed search
space of `Gtz.ProjectionBlockSelectsOnSupport` is nonempty at every design and
contains a selection of at least the average weight. -/
theorem exists_support_member (D : WeightedDesign 6 3) :
    ∃ selected : Finset (Fin 6), ∃ _hcard : selected.card = 3,
      (1:ℝ) / 20 ≤ pluckerWeight D selected := by
  obtain ⟨labels, hmem, hge⟩ := exists_pluckerWeight_ge_one_twentieth D
  exact ⟨labels, (Finset.mem_powersetCard.mp hmem).2, hge⟩

end Gtz
