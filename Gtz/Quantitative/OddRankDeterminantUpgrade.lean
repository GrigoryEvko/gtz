/-
# The odd-rank value at zero, quantitatively

`Gtz.mixedCharPoly_eval_zero_nonpos_of_odd` says the volume-sampling mixed
characteristic polynomial is nonpositive at zero whenever the rank is odd, and
`Gtz.mixedCharPoly_eval_zero_neg_of_odd` upgrades that to strict negativity ONCE A
NONSINGULAR `rank`-subset has been exhibited.  This file replaces both by a floor
carrying a constant:

    q(0)  ≤  −1 / e_rank(t) ,       e_rank(t)  =  ∑_{|C| = rank} ∏_{c ∈ C} t_c ,

which is `mixedCharPoly_eval_zero_le_neg_inv_weightElementary_of_odd`, at every real
weighted design of odd rank and with no side condition whatsoever.  At uniform
weights `e_rank(t) = C(size, rank)/size^rank`
(`Gtz.weightElementary_of_uniformWeight`), so the constant is `−54/5 = −10.8` at
`(6,3)` and `−49/5 = −9.8` at `(7,3)`; both are recorded below against the
repository's two rank-three witnesses.

The upgrade is STRICT at every design.  `e_rank(t) > 0` is
`Gtz.weightElementary_pos`, so the right-hand side is strictly negative
(`neg_inv_weightElementary_lt_zero`) and the shipped nonpositivity is recovered as a
corollary, `mixedCharPoly_eval_zero_nonpos_of_odd_from_upgrade`.  The shipped theorem
itself is untouched.  The nonsingular witness that
`Gtz.mixedCharPoly_eval_zero_neg_of_odd` consumes also disappears:
`mixedCharPoly_eval_zero_lt_zero_of_odd` needs the parity and nothing else.

## The derivation, in the order the file mechanizes it

Two shipped identities and one classical inequality.  No new analysis enters.

1.  **(I1), the enumeration-free evaluation.**
    `Gtz.shadowDeterminant_eq_weightProduct_mul_detSubsetSum` reads each
    volume-sampling mass as `det P_C = (∏_{c ∈ C} t_c) · det S_C`.  Dividing its
    square by the weight product turns the shipped coefficient
    `Gtz.expectedElementary D rank = ∑_C (det P_C)² / ∏_{c ∈ C} t_c` into
    `∑_C (∏_{c ∈ C} t_c)(det S_C)²`, which is the summand of
    `Gtz.sum_weightProduct_mul_detSubsetSum_sq_nonneg`
    (`expectedElementary_rank_eq_sum_weightProduct_mul_detSubsetSum_sq`), and equally
    into `∑_C det P_C · det S_C`, which is the volume-sampling average of the subset
    determinant (`expectedElementary_rank_eq_volumeSamplingAverage_detSubsetSum`).
    Composing with `Gtz.mixedCharPoly_eval_zero` gives the parity-free identity
    `q(0) = (−1)^rank · E_π[det S_C]`.
2.  **Cauchy–Schwarz in Engel form** — `Finset.sq_sum_div_le_sum_sq_div`, Mathlib's
    Sedrakyan lemma — with `f_C = det P_C` and `g_C = ∏_{c ∈ C} t_c`, whose weight
    products are positive.  Its numerator is
    `(∑_{|C| = level} det P_C)² = C(rank, level)²` by
    `Gtz.sum_shadowDeterminant_eq_choose`, so
    `C(rank, level)² / e_level(t) ≤ c_level`.  At `level = rank` Cauchy–Binet makes
    the numerator `1` and the bound reads `E_π[det S_C] ≥ 1/e_rank(t)`.
3.  The parity sign, which is where the rank being odd is spent and the only place
    it is spent.

The level-parametric form `sq_choose_div_weightElementary_le_expectedElementary` is
stated because it is free, not because anything below consumes it.  Its level-ONE
instance is, after `weightElementary_one` and `C(rank,1) = rank`, literally the
shipped `Gtz.sq_rank_le_expectedElementary_one`; that theorem is therefore NOT
restated here and a reader wanting it should go there.

## Sharpness, and where the floor has slack

**ATTAINED at the regular tetrahedron, exactly.**  `e_3(t) = 1/16` is
`Gtz.tetraDesign_weightElementary_three` and `Gtz.mixedCharPoly_tetraDesign` gives
`q = (X − 1)(X − 4)²`, so `q(0) = −16 = −1/e_3(t)` on the nose:
`tetraDesign_attains_neg_inv_weightElementary_floor`.  The mechanism is visible in
step 2 — Engel is an equality exactly when `det P_C / ∏ t_c = det S_C` is constant
over the family, and `Gtz.tetraDesign_detSubsetSum_eq` says it is constantly `16`.
So the inequality is an EQUALITY at the known extremal design, and no strengthening
of the Cauchy–Schwarz step could lower the right-hand side without failing there.
That says nothing about designs where `det S_C` varies over the family, and the two
witnesses below are exactly such designs.

**NOT attained at either rank-three witness.**  MEASURED, not mechanized, and quoted
from the ledger of `Gtz.Reduction.MixedCharPolynomial`, which states both numbers as
measured: `rootKillDesign` has `q(0) = −27/2 = −13.5` against the floor
`−54/5 = −10.8`, and `axisKillDesign` has `q(0) = −3773/256 = −14.73828125` against
`−49/5 = −9.8`.  Only the floors are proved here; neither true value is.

## What this does NOT do

* **It closes no covering class and decides no open cell.**  The sign of `q(0)` at
  odd rank was already decided, by parity, in the shipped theorem; what is added is
  a CONSTANT.  `Gtz.HasMixedRootAtLeastOne 6 3` and `… 7 3` remain refuted
  (`Gtz.not_mixedRootAtLeastOne_sixThree`,
  `Gtz.not_mixedRootAtLeastOne_sevenThree`), the interlacing route remains dead at
  rank three, and nothing here revives it.  `GtzWeighted 6 3` and `GtzWeighted 7 3`
  are exactly as open after this file as before it.
* **It bounds no ROOT.**  A value at a point is not a root location, and the
  refutations above turn on the value at `1`, which this file does not touch.
* **It exhibits no subset.**  The shipped `Gtz.exists_detSubsetSum_ge_inv_weightElementary`
  produces ONE `rank`-subset with `det S_C ≥ 1/e_rank(t)`, by a maximum argument.
  The floor here is on the π-AVERAGE of the same quantity, which is the SMALLER of
  the two — an average never exceeds a maximum — so the shipped existential follows
  from it and is deliberately NOT re-derived here.  What the average form buys is
  that `q(0)` IS that average up to the parity sign; the maximum form does not
  transfer to `q(0)` at all.  Both carry the same constant because both are attained
  at the tetrahedron, where `det S_C` is constant over the family and the average and
  the maximum coincide.  A floor on an average still exhibits nothing: it names no
  subset, and this file names none.
-/
import Mathlib
import Gtz.Quantitative.ExpectedCharPolynomial
import Gtz.Quantitative.ProjectionOnePointMarginal
import Gtz.Quantitative.VolumeAverageLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The rank-level coefficient is the average of the subset determinant

`Gtz.expectedElementary` divides the squared mass by the weight product.  At the
level equal to the rank, (I1) makes one of the two masses cancel against that
divisor, and the coefficient becomes the volume-sampling average of `det S_C` — the
same sum that `Gtz.mixedCharPoly_eval_zero` produces, read two ways. -/

/-- **The coefficient at the rank is `E_π[det S_C]`.**  By (I1) the summand
`(det P_C)²/∏_{c ∈ C} t_c` is `det P_C · det S_C`, and the masses are the
volume-sampling measure. -/
theorem expectedElementary_rank_eq_volumeSamplingAverage_detSubsetSum
    (design : WeightedDesign size rank) :
    expectedElementary design rank
      = volumeSamplingAverage design fun selected => (subsetSum design selected).det := by
  rw [expectedElementary, volumeSamplingAverage]
  refine Finset.sum_congr rfl fun selected hmem => ?_
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum design
      (Finset.mem_powersetCard.mp hmem).2,
    div_eq_iff (subsetWeightProduct_pos design selected).ne']
  ring

/-- **The coefficient at the rank in the form the value at zero produces it**:
`∑_C (∏_{c ∈ C} t_c)(det S_C)²`, the summand of
`Gtz.sum_weightProduct_mul_detSubsetSum_sq_nonneg`. -/
theorem expectedElementary_rank_eq_sum_weightProduct_mul_detSubsetSum_sq
    (design : WeightedDesign size rank) :
    expectedElementary design rank
      = ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard rank,
          (∏ atomIndex ∈ selected, design.weight atomIndex)
            * (subsetSum design selected).det ^ 2 := by
  rw [expectedElementary]
  refine Finset.sum_congr rfl fun selected hmem => ?_
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum design
      (Finset.mem_powersetCard.mp hmem).2,
    div_eq_iff (subsetWeightProduct_pos design selected).ne']
  ring

/-- **The parity-free identity**: `q(0) = (−1)^rank · E_π[det S_C]`.  This is
`Gtz.mixedCharPoly_eval_zero` with its sum named. -/
theorem mixedCharPoly_eval_zero_eq_neg_one_pow_mul_expectedElementary
    (design : WeightedDesign size rank) :
    (mixedCharPoly design).eval 0 = (-1 : ℝ) ^ rank * expectedElementary design rank := by
  rw [mixedCharPoly_eval_zero, expectedElementary_rank_eq_sum_weightProduct_mul_detSubsetSum_sq]

/-! ## The Cauchy–Schwarz floor on the coefficient

Engel's form of Cauchy–Schwarz against the two shipped aggregates: the masses at a
level sum to `C(rank, level)`, and the weight products at that level sum to
`e_level(t)`. -/

/-- The elementary symmetric polynomial of the weights at level one is the total
weight, which is one.  Recorded so the level-one instance of the bound below can be
checked to be the shipped `Gtz.sq_rank_le_expectedElementary_one` rather than
something new. -/
theorem weightElementary_one (design : WeightedDesign size rank) :
    weightElementary design 1 = 1 := by
  classical
  rw [weightElementary, Finset.powersetCard_one, Finset.sum_map]
  refine Eq.trans (Finset.sum_congr rfl fun atomIndex _ => ?_) design.weight_sum_one
  have hsingleton : (⟨singleton, Finset.singleton_injective⟩ :
      Fin size ↪ Finset (Fin size)) atomIndex = {atomIndex} := rfl
  rw [hsingleton, Finset.prod_singleton]

/-- **The Engel bound at every level**: `C(rank, level)² / e_level(t) ≤ c_level`.
Sedrakyan's lemma on the volume-sampling masses against their weight products, whose
numerator is `Gtz.sum_shadowDeterminant_eq_choose`.  No hypothesis on the level: past
the size both sides are zero, and the positivity Engel wants is vacuous on an empty
family. -/
theorem sq_choose_div_weightElementary_le_expectedElementary
    (design : WeightedDesign size rank) (level : ℕ) :
    ((rank.choose level : ℕ) : ℝ) ^ 2 / weightElementary design level
      ≤ expectedElementary design level := by
  have hengel := Finset.sq_sum_div_le_sum_sq_div
    ((Finset.univ : Finset (Fin size)).powersetCard level)
    (fun selected => shadowDeterminant design selected)
    (fun selected _ => subsetWeightProduct_pos design selected)
  have hweightSum : ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      ∏ atomIndex ∈ selected, design.weight atomIndex = weightElementary design level := rfl
  have hcoefficient : ∑ selected ∈ (Finset.univ : Finset (Fin size)).powersetCard level,
      shadowDeterminant design selected ^ 2 / ∏ atomIndex ∈ selected, design.weight atomIndex
        = expectedElementary design level := rfl
  rwa [sum_shadowDeterminant_eq_choose design level, hweightSum, hcoefficient] at hengel

/-- **THE SECOND-MOMENT FLOOR**: `c_rank ≥ 1/e_rank(t)`.  The level-rank instance of
the Engel bound, where Cauchy–Binet makes the numerator `C(rank, rank)² = 1`. -/
theorem inv_weightElementary_le_expectedElementary_rank (design : WeightedDesign size rank) :
    (weightElementary design rank)⁻¹ ≤ expectedElementary design rank := by
  have hbound := sq_choose_div_weightElementary_le_expectedElementary design rank
  rwa [Nat.choose_self, Nat.cast_one, one_pow, one_div] at hbound

/-- The same floor in its probabilistic reading: the volume-sampling average of the
subset determinant is at least `1/e_rank(t)`. -/
theorem inv_weightElementary_le_volumeSamplingAverage_detSubsetSum
    (design : WeightedDesign size rank) :
    (weightElementary design rank)⁻¹
      ≤ volumeSamplingAverage design fun selected => (subsetSum design selected).det := by
  rw [← expectedElementary_rank_eq_volumeSamplingAverage_detSubsetSum]
  exact inv_weightElementary_le_expectedElementary_rank design

/-! ## The upgrade

The floor on the coefficient, carried through the parity sign. -/

/-- The floor's right-hand side is strictly negative at every design, because
`Gtz.weightElementary_pos` puts `e_rank(t)` strictly above zero.  This is what makes
the upgrade below a STRICT strengthening of the shipped nonpositivity rather than a
restatement of it. -/
theorem neg_inv_weightElementary_lt_zero (design : WeightedDesign size rank) :
    -(weightElementary design rank)⁻¹ < 0 :=
  neg_lt_zero.mpr (inv_pos.mpr (weightElementary_pos design))

/-- **THE ODD-RANK UPGRADE.**  At odd rank the mixture's value at zero is at most
`−1/e_rank(t)`, for every real weighted design and with no side condition.  This
strictly strengthens `Gtz.mixedCharPoly_eval_zero_nonpos_of_odd`, which is recovered
below; the shipped theorem is not modified. -/
theorem mixedCharPoly_eval_zero_le_neg_inv_weightElementary_of_odd
    (design : WeightedDesign size rank) (hodd : Odd rank) :
    (mixedCharPoly design).eval 0 ≤ -(weightElementary design rank)⁻¹ := by
  rw [mixedCharPoly_eval_zero_eq_neg_one_pow_mul_expectedElementary, hodd.neg_one_pow,
    neg_one_mul, neg_le_neg_iff]
  exact inv_weightElementary_le_expectedElementary_rank design

/-- **The shipped statement follows.**  `Gtz.mixedCharPoly_eval_zero_nonpos_of_odd`
is the upgrade composed with the strict negativity of its right-hand side.  Recorded
so that the strengthening is checkable in one step rather than asserted. -/
theorem mixedCharPoly_eval_zero_nonpos_of_odd_from_upgrade
    (design : WeightedDesign size rank) (hodd : Odd rank) :
    (mixedCharPoly design).eval 0 ≤ 0 :=
  le_trans (mixedCharPoly_eval_zero_le_neg_inv_weightElementary_of_odd design hodd)
    (neg_inv_weightElementary_lt_zero design).le

/-- **Strict negativity with no witness.**  `Gtz.mixedCharPoly_eval_zero_neg_of_odd`
gets the same conclusion but consumes a `rank`-subset with nonvanishing determinant;
the upgrade needs the parity alone. -/
theorem mixedCharPoly_eval_zero_lt_zero_of_odd
    (design : WeightedDesign size rank) (hodd : Odd rank) :
    (mixedCharPoly design).eval 0 < 0 :=
  lt_of_le_of_lt (mixedCharPoly_eval_zero_le_neg_inv_weightElementary_of_odd design hodd)
    (neg_inv_weightElementary_lt_zero design)

/-- **The even-rank companion**, for completeness of the parity split: at even rank
the same two steps put the value at zero ABOVE `1/e_rank(t)`, in particular strictly
above zero.  Nothing in this development consumes it. -/
theorem inv_weightElementary_le_mixedCharPoly_eval_zero_of_even
    (design : WeightedDesign size rank) (heven : Even rank) :
    (weightElementary design rank)⁻¹ ≤ (mixedCharPoly design).eval 0 := by
  rw [mixedCharPoly_eval_zero_eq_neg_one_pow_mul_expectedElementary, heven.neg_one_pow,
    one_mul]
  exact inv_weightElementary_le_expectedElementary_rank design

/-! ## The floor is attained at the regular tetrahedron

Equality in Engel's form needs `det P_C / ∏_{c ∈ C} t_c = det S_C` constant over the
family, which `Gtz.tetraDesign_detSubsetSum_eq` supplies.  So the constant
`1/e_rank(t)` cannot be improved by this argument. -/

/-- **THE FLOOR IS TIGHT.**  At the regular tetrahedron `q(0) = −16` — read off the
shipped `Gtz.mixedCharPoly_tetraDesign` — and `e_3(t) = 1/16`, so the upgrade holds
with equality at the known extremal design. -/
theorem tetraDesign_attains_neg_inv_weightElementary_floor :
    (mixedCharPoly tetraDesign).eval 0 = -(weightElementary tetraDesign 3)⁻¹ := by
  rw [mixedCharPoly_tetraDesign, tetraDesign_weightElementary_three]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  norm_num

/-! ## The two rank-three witnesses

Both are uniformly weighted, so `Gtz.weightElementary_of_uniformWeight` evaluates
`e_3(t)` exactly and the floor becomes an explicit rational.  Neither design's true
value at zero is proved here or anywhere in the repository. -/

/-- `e_3(t) = C(6,3)/6³ = 5/54` at the `D₃` root witness. -/
theorem rootKillDesign_weightElementary_three : weightElementary rootKillDesign 3 = 5 / 54 := by
  rw [weightElementary_of_uniformWeight rootKillDesign 3 (uniform := (1 : ℝ) / 6) fun _ => rfl,
    show Nat.choose 6 3 = 20 from rfl]
  norm_num

/-- The floor at `(6,3)` and uniform weights: `q(0) ≤ −54/5`.  The witness's measured
value is `−27/2`, so the floor has slack `2.7` there; that value is not proved. -/
theorem mixedCharPoly_rootKillDesign_eval_zero_le :
    (mixedCharPoly rootKillDesign).eval 0 ≤ -(54 / 5) := by
  have hbound := mixedCharPoly_eval_zero_le_neg_inv_weightElementary_of_odd rootKillDesign
    ⟨1, by norm_num⟩
  have hinverse : ((5 : ℝ) / 54)⁻¹ = 54 / 5 := by norm_num
  rwa [rootKillDesign_weightElementary_three, hinverse] at hbound

/-- `e_3(t) = C(7,3)/7³ = 5/49` at the doubled-axis witness. -/
theorem axisKillDesign_weightElementary_three : weightElementary axisKillDesign 3 = 5 / 49 := by
  rw [weightElementary_of_uniformWeight axisKillDesign 3 (uniform := (1 : ℝ) / 7) fun _ => rfl,
    show Nat.choose 7 3 = 35 from rfl]
  norm_num

/-- The floor at `(7,3)` and uniform weights: `q(0) ≤ −49/5`.  The witness's measured
value is `−3773/256`, so the floor has slack about `4.9` there; that value is not
proved. -/
theorem mixedCharPoly_axisKillDesign_eval_zero_le :
    (mixedCharPoly axisKillDesign).eval 0 ≤ -(49 / 5) := by
  have hbound := mixedCharPoly_eval_zero_le_neg_inv_weightElementary_of_odd axisKillDesign
    ⟨1, by norm_num⟩
  have hinverse : ((5 : ℝ) / 49)⁻¹ = 49 / 5 := by norm_num
  rwa [axisKillDesign_weightElementary_three, hinverse] at hbound

end Gtz
