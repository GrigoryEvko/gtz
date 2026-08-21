/-
# The volume floor, and where the number six enters

The weighted squared volumes of the `k`-subsets of an `(m,3)` design total one
(`Gtz.volume_budget_sixThree`, `Gtz.volume_budget_fiveThree`).  A design of size
`m` has `C(m,3)` of them, so one of them is at least `1/C(m,3)`.  Each weight
product obeys `t_a·t_b·t_c ≤ 1/27` by the arithmetic-geometric mean inequality on
three weights whose sum is at most one.  Dividing:

  **`Gtz.exists_sq_tripleBracket_ge_sixThree`:  every `(6,3)` design carries a
  triple with `[g_a, g_b, g_c]² ≥ 27/20`** ,

  **`Gtz.exists_sq_tripleBracket_ge_fiveThree`:  every `(5,3)` design carries a
  triple with `[g_a, g_b, g_c]² ≥ 27/10`** .

## Where the number six enters

The bound is `27 / C(m,3)`, and it EXCEEDS ONE exactly when `C(m,3) < 27`, that
is exactly when `m ≤ 6`:

  `C(4,3) = 4`,  `C(5,3) = 10`,  `C(6,3) = 20`,  `C(7,3) = 35` .

At `m = 7` the bound reads `27/35 < 1` and the argument is silent.  The three
arithmetic facts are recorded as `Gtz.one_lt_twentySeven_div_twenty`,
`Gtz.one_lt_twentySeven_div_ten` and `Gtz.twentySeven_div_thirtyFive_lt_one` so
that the size dependence is machine-checked rather than asserted.  The survey
demands exactly this: an argument that does not use the number six is impossible
at `(6,3)`, because sizes four and five carry configurations that six must
exclude.  This is the first instrument in the campaign whose SIZE THRESHOLD is
`m ≤ 6` on the nose.

## What the volume buys

A weak dominator has `S_C ⪰ 1`, hence a positive semidefinite Gram gap, hence
three nonnegative gap invariants.  Writing `L` for the triple's leverage sum, `W`
for its squared-area sum and `V` for its squared volume, those invariants are

  `e₁ = L − 3` ,  `e₂ = W − 2L + 3` ,  `e₃ = V − W + L − 1` ,

so `V = 1 + e₁ + e₂ + e₃`, and a weak dominator obeys all three
(`Gtz.dominates_triple_leverage_sum_ge`,
`Gtz.dominates_triple_areaSum_ge`, `Gtz.dominates_triple_volume_ge`).  Hence

  **`Gtz.exists_positive_gapInvariantSum_sixThree`:  every `(6,3)` design carries
  a triple whose three gap invariants have STRICTLY POSITIVE SUM** .

That is one of the three Sylvester conditions summed, not all three separately,
so it does not close `GtzWeighted 6 3` on its own.  It does say that the failure
of domination at a `(6,3)` design is never a failure of the total: some triple
always overshoots, and the obstruction is the SPLIT of the overshoot among the
three invariants.

[MEASURED, exact rational arithmetic on the `(5,3)` diamond (`K4 − e`,
conductances `(2,3,3,3,3)`, uniform weight `1/5`).  Its ten squared volumes are
`12.5` four times, `18.75` four times and `0` twice.  The bound `27/10 = 2.7` is
satisfied with room, and the exact floor `1/e₃(t)` — with
`e₃(t) = 10/125 = 2/25` at uniform weight — reads `12.5`, which is ATTAINED at
four of the ten triples.  So the crude constant `27/C(m,3)` is not sharp but the
budget argument behind it is: at uniform weight the floor `1/e₃(t)` is exactly
the smallest positive volume of the diamond.]
-/
import Gtz.Wave.TripleInvariantChart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Three weights never multiply to more than one twenty-seventh -/

/-- The arithmetic-geometric mean inequality at three nonnegative reals, in its
polynomial form. -/
theorem twentySeven_mul_tripleWeight_prod_le_cube (first second third : ℝ) (hfirst : 0 ≤ first)
    (hsecond : 0 ≤ second) (hthird : 0 ≤ third) :
    27 * (first * second * third) ≤ (first + second + third) ^ 3 := by
  nlinarith [sq_nonneg (first - second), sq_nonneg (second - third), sq_nonneg (first - third),
    sq_nonneg (first + second - 2 * third), sq_nonneg (second + third - 2 * first),
    sq_nonneg (first + third - 2 * second), mul_nonneg hfirst hsecond,
    mul_nonneg hsecond hthird, mul_nonneg hfirst hthird,
    mul_nonneg (mul_nonneg hfirst hsecond) hthird, sq_nonneg (first + second + third)]

/-- Three distinct weights of a design total at most one. -/
theorem three_weight_sum_le_one (D : WeightedDesign m 3) {first second third : Fin m}
    (hfs : first ≠ second) (hft : first ≠ third) (hst : second ≠ third) :
    D.weight first + D.weight second + D.weight third ≤ 1 := by
  classical
  have hpair : ∑ c ∈ ({first, second, third} : Finset (Fin m)), D.weight c
      = D.weight first + D.weight second + D.weight third := by
    rw [Finset.sum_insert (by simp [hfs, hft]), Finset.sum_insert (by simp [hst]),
      Finset.sum_singleton]
    ring
  have hsub : ∑ c ∈ ({first, second, third} : Finset (Fin m)), D.weight c ≤ ∑ c, D.weight c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ => (D.weight_pos c).le)
  rw [D.weight_sum_one, hpair] at hsub
  exact hsub

/-- **THE WEIGHT PRODUCT CAP.**  Any three distinct weights of a design multiply
to at most one twenty-seventh. -/
theorem weight_prod_le_one_div_twentySeven (D : WeightedDesign m 3)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) :
    D.weight first * D.weight second * D.weight third ≤ 1 / 27 := by
  have hsum := three_weight_sum_le_one D hfs hft hst
  have hamgm := twentySeven_mul_tripleWeight_prod_le_cube (D.weight first) (D.weight second)
    (D.weight third) (D.weight_pos first).le (D.weight_pos second).le (D.weight_pos third).le
  have hcube : (D.weight first + D.weight second + D.weight third) ^ 3 ≤ 1 := by
    have hnonneg : 0 ≤ D.weight first + D.weight second + D.weight third := by
      linarith [(D.weight_pos first).le, (D.weight_pos second).le, (D.weight_pos third).le]
    exact pow_le_one₀ hnonneg hsum
  linarith

/-- A small squared volume makes a small weighted volume. -/
theorem weighted_volume_lt_of_sq_tripleBracket_lt (D : WeightedDesign m 3)
    {first second third : Fin m} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) {ceiling floor : ℝ} (hceiling : 0 < ceiling)
    (hproduct : ceiling / 27 = floor)
    (hsmall : tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 < ceiling) :
    D.weight first * D.weight second * D.weight third
      * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 < floor := by
  have hcap := weight_prod_le_one_div_twentySeven D hfs hft hst
  have hprodPos : 0 < D.weight first * D.weight second * D.weight third :=
    mul_pos (mul_pos (D.weight_pos first) (D.weight_pos second)) (D.weight_pos third)
  have hsq : 0 ≤ tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2 :=
    sq_nonneg _
  rw [← hproduct]
  nlinarith [hcap, hprodPos, hsq, hsmall, hceiling]

/-! ## 2. The size arithmetic, machine-checked -/

/-- At size six the volume floor exceeds one: `C(6,3) = 20 < 27`. -/
theorem one_lt_twentySeven_div_twenty : (1 : ℝ) < 27 / 20 := by norm_num

/-- At size five the volume floor exceeds one: `C(5,3) = 10 < 27`. -/
theorem one_lt_twentySeven_div_ten : (1 : ℝ) < 27 / 10 := by norm_num

/-- At size SEVEN the volume floor falls below one: `C(7,3) = 35 > 27`, and the
argument is silent.  This is the exact size threshold of the instrument. -/
theorem twentySeven_div_thirtyFive_lt_one : (27 : ℝ) / 35 < 1 := by norm_num

/-! ## 3. The volume floor at size six -/

/-- **THE TWENTY VOLUMES CANNOT ALL BE SMALL.**  They total one, so one of them
is at least a twentieth. -/
theorem not_forall_weighted_volume_lt_sixThree (D : WeightedDesign 6 3)
    (hall : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      D.weight a * D.weight b * D.weight c
        * tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 < 1 / 20) :
    False := by
  have hbudget := volume_budget_sixThree D
  linarith [hall 0 1 2 (by decide) (by decide) (by decide),
    hall 0 1 3 (by decide) (by decide) (by decide),
    hall 0 1 4 (by decide) (by decide) (by decide),
    hall 0 1 5 (by decide) (by decide) (by decide),
    hall 0 2 3 (by decide) (by decide) (by decide),
    hall 0 2 4 (by decide) (by decide) (by decide),
    hall 0 2 5 (by decide) (by decide) (by decide),
    hall 0 3 4 (by decide) (by decide) (by decide),
    hall 0 3 5 (by decide) (by decide) (by decide),
    hall 0 4 5 (by decide) (by decide) (by decide),
    hall 1 2 3 (by decide) (by decide) (by decide),
    hall 1 2 4 (by decide) (by decide) (by decide),
    hall 1 2 5 (by decide) (by decide) (by decide),
    hall 1 3 4 (by decide) (by decide) (by decide),
    hall 1 3 5 (by decide) (by decide) (by decide),
    hall 1 4 5 (by decide) (by decide) (by decide),
    hall 2 3 4 (by decide) (by decide) (by decide),
    hall 2 3 5 (by decide) (by decide) (by decide),
    hall 2 4 5 (by decide) (by decide) (by decide),
    hall 3 4 5 (by decide) (by decide) (by decide)]

/-- **THE VOLUME FLOOR AT SIZE SIX.**  Every `(6,3)` design carries a triple whose
squared volume is at least `27/20`, which exceeds one.  Twenty volumes total one,
so one is at least a twentieth, and its weight product is at most a
twenty-seventh. -/
theorem exists_sq_tripleBracket_ge_sixThree (D : WeightedDesign 6 3) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ 27 / 20 ≤ tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 := by
  by_contra hcon
  push Not at hcon
  refine not_forall_weighted_volume_lt_sixThree D fun a b c hab hac hbc => ?_
  exact weighted_volume_lt_of_sq_tripleBracket_lt D hab hac hbc (by norm_num) (by norm_num)
    (hcon a b c hab hac hbc)

/-! ## 4. The volume floor at size five -/

/-- **THE TEN VOLUMES CANNOT ALL BE SMALL.** -/
theorem not_forall_weighted_volume_lt_fiveThree (D : WeightedDesign 5 3)
    (hall : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      D.weight a * D.weight b * D.weight c
        * tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 < 1 / 10) :
    False := by
  have hbudget := volume_budget_fiveThree D
  linarith [hall 0 1 2 (by decide) (by decide) (by decide),
    hall 0 1 3 (by decide) (by decide) (by decide),
    hall 0 1 4 (by decide) (by decide) (by decide),
    hall 0 2 3 (by decide) (by decide) (by decide),
    hall 0 2 4 (by decide) (by decide) (by decide),
    hall 0 3 4 (by decide) (by decide) (by decide),
    hall 1 2 3 (by decide) (by decide) (by decide),
    hall 1 2 4 (by decide) (by decide) (by decide),
    hall 1 3 4 (by decide) (by decide) (by decide),
    hall 2 3 4 (by decide) (by decide) (by decide)]

/-- **THE VOLUME FLOOR AT SIZE FIVE.**  Every `(5,3)` design carries a triple whose
squared volume is at least `27/10`. -/
theorem exists_sq_tripleBracket_ge_fiveThree (D : WeightedDesign 5 3) :
    ∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ 27 / 10 ≤ tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 := by
  by_contra hcon
  push Not at hcon
  refine not_forall_weighted_volume_lt_fiveThree D fun a b c hab hac hbc => ?_
  exact weighted_volume_lt_of_sq_tripleBracket_lt D hab hac hbc (by norm_num) (by norm_num)
    (hcon a b c hab hac hbc)

/-! ## 5. The three gap invariants of a weak dominator -/

/-- **EVERY MEMBER OF A WEAK DOMINATOR IS HEAVY.**  The Gram gap of a weak
dominator is positive semidefinite, so its diagonal is nonnegative. -/
theorem one_le_leverage_of_dominates_triple (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    1 ≤ leverageOf (D.atom x) := by
  have hpsd := (dominates_triple_iff_tripleGram_posSemidef D x y z hxy hxz hyz).mp hdom
  have hdiag := posSemidef_diag_nonneg hpsd 0
  rw [gap_zero_zero] at hdiag
  linarith

/-- **THE FIRST GAP INVARIANT.**  A weak dominator has leverage sum at least
three. -/
theorem dominates_triple_leverage_sum_ge (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    3 ≤ leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) := by
  have hpsd := (dominates_triple_iff_tripleGram_posSemidef D x y z hxy hxz hyz).mp hdom
  have h0 := posSemidef_diag_nonneg hpsd 0
  have h1 := posSemidef_diag_nonneg hpsd 1
  have h2 := posSemidef_diag_nonneg hpsd 2
  rw [gap_zero_zero] at h0
  rw [gap_one_one] at h1
  rw [gap_two_two] at h2
  linarith

/-- **THE SECOND GAP INVARIANT.**  A weak dominator has squared-area sum at least
twice its leverage sum less three: each of its three pair minors is
nonnegative. -/
theorem dominates_triple_areaSum_ge (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    2 * (leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z)) - 3
      ≤ crossNormSq (D.atom x) (D.atom y) + crossNormSq (D.atom x) (D.atom z)
        + crossNormSq (D.atom y) (D.atom z) := by
  have hxy' := pairGapMinor_nonneg_of_dominates_triple D x y z hxy hxz hyz hdom
  have hxz' : 0 ≤ pairGapMinor (D.atom x) (D.atom z) := by
    have hrot : Dominates D ({x, z, y} : Finset (Fin m)) := by
      have hset : ({x, z, y} : Finset (Fin m)) = {x, y, z} := by
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      rwa [hset]
    exact pairGapMinor_nonneg_of_dominates_triple D x z y hxz hxy hyz.symm hrot
  have hyz' : 0 ≤ pairGapMinor (D.atom y) (D.atom z) := by
    have hrot : Dominates D ({y, z, x} : Finset (Fin m)) := by
      have hset : ({y, z, x} : Finset (Fin m)) = {x, y, z} := by
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      rwa [hset]
    exact pairGapMinor_nonneg_of_dominates_triple D y z x hyz hxy.symm hxz.symm hrot
  rw [pairGapMinor_eq_crossNormSq] at hxy' hxz' hyz'
  linarith

/-- **THE THIRD GAP INVARIANT.**  A weak dominator has squared volume at least its
squared-area sum less its leverage sum plus one: the gap determinant of a
positive semidefinite matrix is nonnegative. -/
theorem dominates_triple_volume_ge (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    (crossNormSq (D.atom x) (D.atom y) + crossNormSq (D.atom x) (D.atom z)
        + crossNormSq (D.atom y) (D.atom z))
      - (leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z)) + 1
      ≤ tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
  have hpsd := (dominates_triple_iff_tripleGram_posSemidef D x y z hxy hxz hyz).mp hdom
  have hdet := hpsd.det_nonneg
  have hthird := tripleGapDet_eq_thirdInvariant (D.atom x) (D.atom y) (D.atom z)
  have hgapdet : tripleGapDet (D.atom x) (D.atom y) (D.atom z)
      = (tripleGram (D.atom x) (D.atom y) (D.atom z) - 1).det := by
    rw [tripleGapDet, Matrix.det_fin_three]
    simp only [gap_zero_zero, gap_one_one, gap_two_two, gap_zero_one, gap_zero_two,
      gap_one_two, gap_one_zero, gap_two_zero, gap_two_one]
    ring
  rw [hgapdet] at hthird
  rw [triplePairAreaSum, tripleLeverageSum] at hthird
  linarith

/-! ## 6. The size-six producer -/

/-- **EVERY `(6,3)` DESIGN OVERSHOOTS SOMEWHERE.**  Some triple has squared volume
strictly above one, hence the sum of its three gap invariants is strictly
positive.  The obstruction to `GtzWeighted 6 3` is therefore never the TOTAL of
the three Sylvester quantities at every triple — it is their SPLIT. -/
theorem exists_positive_gapInvariantSum_sixThree (D : WeightedDesign 6 3) :
    ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c
      ∧ 0 < (leverageOf (D.atom a) + leverageOf (D.atom b) + leverageOf (D.atom c) - 3)
        + ((crossNormSq (D.atom a) (D.atom b) + crossNormSq (D.atom a) (D.atom c)
            + crossNormSq (D.atom b) (D.atom c))
          - 2 * (leverageOf (D.atom a) + leverageOf (D.atom b) + leverageOf (D.atom c)) + 3)
        + tripleGapDet (D.atom a) (D.atom b) (D.atom c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hvolume⟩ := exists_sq_tripleBracket_ge_sixThree D
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  have hthird := tripleGapDet_eq_thirdInvariant (D.atom a) (D.atom b) (D.atom c)
  rw [triplePairAreaSum, tripleLeverageSum] at hthird
  linarith

/-- **A SMALL SQUARED VOLUME EXCLUDES DOMINATION.**  The contrapositive of the
landed volume floor: a triple whose squared volume falls below one is not even a
weak dominator. -/
theorem not_dominates_of_sq_tripleBracket_lt_one (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsmall : tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 < 1) :
    ¬ Dominates D ({x, y, z} : Finset (Fin m)) := by
  intro hdom
  exact absurd (one_le_sq_tripleBracket_of_dominates D x y z hxy hxz hyz hdom)
    (not_le.mpr hsmall)

/-! ## 7. The exact floor

The constant `27/C(m,3)` throws away the weights.  Keeping them gives the exact
statement: a ceiling on every squared volume is a ceiling on the whole budget,
so `1 ≤ bound · e₃(t)` with `e₃(t)` the third elementary symmetric function of
the weights.  At uniform weight and `m = 5` that reads `bound ≥ 12.5`, which the
diamond ATTAINS at four of its ten triples, so this form is sharp where the
crude constant is not. -/

/-- **THE EXACT VOLUME FLOOR AT `(6,3)`.**  A common ceiling on the twenty squared
volumes forces `1 ≤ bound · e₃(t)`, where `e₃(t)` is the third elementary
symmetric function of the six weights. -/
theorem one_le_bound_mul_weightTripleSum_sixThree (D : WeightedDesign 6 3) {bound : ℝ}
    (hall : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 ≤ bound) :
    1 ≤ bound * (D.weight 0 * D.weight 1 * D.weight 2 + D.weight 0 * D.weight 1 * D.weight 3
      + D.weight 0 * D.weight 1 * D.weight 4 + D.weight 0 * D.weight 1 * D.weight 5
      + D.weight 0 * D.weight 2 * D.weight 3 + D.weight 0 * D.weight 2 * D.weight 4
      + D.weight 0 * D.weight 2 * D.weight 5 + D.weight 0 * D.weight 3 * D.weight 4
      + D.weight 0 * D.weight 3 * D.weight 5 + D.weight 0 * D.weight 4 * D.weight 5
      + D.weight 1 * D.weight 2 * D.weight 3 + D.weight 1 * D.weight 2 * D.weight 4
      + D.weight 1 * D.weight 2 * D.weight 5 + D.weight 1 * D.weight 3 * D.weight 4
      + D.weight 1 * D.weight 3 * D.weight 5 + D.weight 1 * D.weight 4 * D.weight 5
      + D.weight 2 * D.weight 3 * D.weight 4 + D.weight 2 * D.weight 3 * D.weight 5
      + D.weight 2 * D.weight 4 * D.weight 5 + D.weight 3 * D.weight 4 * D.weight 5) := by
  have hstep : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      D.weight a * D.weight b * D.weight c
        * tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2
      ≤ D.weight a * D.weight b * D.weight c * bound := by
    intro a b c hab hac hbc
    exact mul_le_mul_of_nonneg_left (hall a b c hab hac hbc)
      (mul_pos (mul_pos (D.weight_pos a) (D.weight_pos b)) (D.weight_pos c)).le
  have hbudget := volume_budget_sixThree D
  linarith [hstep 0 1 2 (by decide) (by decide) (by decide),
    hstep 0 1 3 (by decide) (by decide) (by decide),
    hstep 0 1 4 (by decide) (by decide) (by decide),
    hstep 0 1 5 (by decide) (by decide) (by decide),
    hstep 0 2 3 (by decide) (by decide) (by decide),
    hstep 0 2 4 (by decide) (by decide) (by decide),
    hstep 0 2 5 (by decide) (by decide) (by decide),
    hstep 0 3 4 (by decide) (by decide) (by decide),
    hstep 0 3 5 (by decide) (by decide) (by decide),
    hstep 0 4 5 (by decide) (by decide) (by decide),
    hstep 1 2 3 (by decide) (by decide) (by decide),
    hstep 1 2 4 (by decide) (by decide) (by decide),
    hstep 1 2 5 (by decide) (by decide) (by decide),
    hstep 1 3 4 (by decide) (by decide) (by decide),
    hstep 1 3 5 (by decide) (by decide) (by decide),
    hstep 1 4 5 (by decide) (by decide) (by decide),
    hstep 2 3 4 (by decide) (by decide) (by decide),
    hstep 2 3 5 (by decide) (by decide) (by decide),
    hstep 2 4 5 (by decide) (by decide) (by decide),
    hstep 3 4 5 (by decide) (by decide) (by decide)]

/-- **THE EXACT VOLUME FLOOR AT `(5,3)`.** -/
theorem one_le_bound_mul_weightTripleSum_fiveThree (D : WeightedDesign 5 3) {bound : ℝ}
    (hall : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2 ≤ bound) :
    1 ≤ bound * (D.weight 0 * D.weight 1 * D.weight 2 + D.weight 0 * D.weight 1 * D.weight 3
      + D.weight 0 * D.weight 1 * D.weight 4 + D.weight 0 * D.weight 2 * D.weight 3
      + D.weight 0 * D.weight 2 * D.weight 4 + D.weight 0 * D.weight 3 * D.weight 4
      + D.weight 1 * D.weight 2 * D.weight 3 + D.weight 1 * D.weight 2 * D.weight 4
      + D.weight 1 * D.weight 3 * D.weight 4 + D.weight 2 * D.weight 3 * D.weight 4) := by
  have hstep : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      D.weight a * D.weight b * D.weight c
        * tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2
      ≤ D.weight a * D.weight b * D.weight c * bound := by
    intro a b c hab hac hbc
    exact mul_le_mul_of_nonneg_left (hall a b c hab hac hbc)
      (mul_pos (mul_pos (D.weight_pos a) (D.weight_pos b)) (D.weight_pos c)).le
  have hbudget := volume_budget_fiveThree D
  linarith [hstep 0 1 2 (by decide) (by decide) (by decide),
    hstep 0 1 3 (by decide) (by decide) (by decide),
    hstep 0 1 4 (by decide) (by decide) (by decide),
    hstep 0 2 3 (by decide) (by decide) (by decide),
    hstep 0 2 4 (by decide) (by decide) (by decide),
    hstep 0 3 4 (by decide) (by decide) (by decide),
    hstep 1 2 3 (by decide) (by decide) (by decide),
    hstep 1 2 4 (by decide) (by decide) (by decide),
    hstep 1 3 4 (by decide) (by decide) (by decide),
    hstep 2 3 4 (by decide) (by decide) (by decide)]

end Gtz
