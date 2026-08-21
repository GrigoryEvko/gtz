/-
# The resolvent chart has its own Sylvester chain, and its first step is a count

`Gtz/Wave/ResolventBlockCriterion.lean` proves that a selection dominates exactly
when the principal block of the resolvent readings on its complement sits below
the identity.  Sylvester then decides that block by three signs, exactly as the
design chart is decided by heaviness, the pair minor and the gap determinant.
This module supplies the resolvent chart's three currencies and their budgets,
and proves the FIRST of the three signs outright by counting.

## The three signs

Write `rho_c = Pi c c` for the co-Parseval pivot and `Pi a b` for the readings.
Domination of `Cᶜ` asks `1 - Pi[C,C] ⪰ 0`, whose principal minors are

  1. `1 - rho_a ≥ 0`                                   -- one label
  2. `(1 - rho_a)(1 - rho_b) - (Pi a b)² ≥ 0`          -- one pair
  3. `det (1 - Pi[C,C]) ≥ 0`                           -- the triple

`Gtz.resolventPairMinor` is the second.  The three are the resolvent chart's
analogue of heaviness, the admissible pair and the gap determinant, and
`Gtz.pivot_le_one_of_dominates_compl` and
`Gtz.resolventPairMinor_nonneg_of_dominates_compl` show the first two are
NECESSARY, being principal minors of a positive semidefinite block.

## The budgets

Three exact totals, each hypothesis-free at every size and rank.  The first is
landed (`Gtz.descent_identity`); the other two are new and both come from the
projection law by one contraction:

  **`Σ_c (1 - t_c)·rho_c = k`**
  **`Σ_{a,b} (1 - t_a)(1 - t_b)·(Pi a b)² = k`**   (`Gtz.sum_coWeight_sq_resolventReading`)
  **`Σ_{a,b} (1 - t_a)(1 - t_b)·pairMinor a b = (m - 1 - k)² - k`**

The second is the projection law read at a single label: summing
`Σ_b (1-t_b)·Pi a b·Pi b a` against the co-weights collapses to the trace.  The
third follows because the co-weights total `m - 1`.  At `(6,3)` the last constant
is `(5 - 3)² - 3 = 1`, the same constant the design chart's pair minors carry.

## The first sign is free, and it explains the window floor `m ≥ 2k`

`Gtz.card_pivot_gt_one_le_rank`: **at most `k` labels have `rho_c > 1`.**  The
proof is a count and nothing else.  Each label contributes
`(1 - t_c)·rho_c + t_c ≥ 0`, the total is `k + 1` by the descent identity and the
weight sum, and `rho_c > 1` says exactly that a label's contribution exceeds one.
More than `k` such labels would overspend the total.

Hence at least `m - k` labels have `rho_c ≤ 1`, and a selection of `k` of them
exists exactly when `m - k ≥ k` (`Gtz.exists_card_pivot_le_one`).  **That is the
campaign's window floor, recovered from the first Sylvester sign of the resolvent
chart.**  At `(6,3)` the count is `3` against a needed `3`: exactly enough, with
nothing to spare, which is why six is the first size where the search can even
begin, and why five is not.

[MEASURED before proving.  The harness reproduces the `(5,3)` diamond exactly --
pivots `(1/2, 13/16, 13/16, 13/16, 13/16)`, co-weighted total `3`, eight of ten
dominating triples in the block form.  The count `#{rho_c ≤ 1} ≥ m - k` was then
checked on random designs and is ATTAINED with equality at `(6,3)`, `(5,3)`,
`(7,3)`, `(6,4)` and `(5,2)`: the minimum observed count equals `m - k` exactly
at each.  The squared-reading budget holds to `1e-14` throughout.]
-/
import Gtz.Wave.ResolventBlockCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The squared-reading budget

The projection law contracted once at a single label. -/

/-- **THE SQUARED READING BUDGET.**  The co-weighted squares of all readings
total the rank.  One contraction of the projection law: summing
`(1 - t_b)·Pi a b·Pi b a` over `b` returns the diagonal reading at `a`, and the
descent identity totals those. -/
theorem sum_coWeight_sq_resolventReading (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ a, ∑ b, (1 - D.weight a) * (1 - D.weight b) * (resolventReading D a b) ^ 2
      = (k : ℝ) := by
  have hrow : ∀ a : Fin m,
      (∑ b, (1 - D.weight a) * (1 - D.weight b) * (resolventReading D a b) ^ 2)
        = (1 - D.weight a) * resolventReading D a a := by
    intro a
    have hlaw := sum_coWeight_mul_resolventReading_mul D hm a a
    have hstep : ∀ b : Fin m,
        (1 - D.weight a) * (1 - D.weight b) * (resolventReading D a b) ^ 2
          = (1 - D.weight a)
              * ((1 - D.weight b) * resolventReading D a b * resolventReading D b a) := by
      intro b; rw [resolventReading_symm D hm b a]; ring
    rw [Finset.sum_congr rfl fun b _ => hstep b, ← Finset.mul_sum, hlaw]
  rw [Finset.sum_congr rfl fun a _ => hrow a]
  exact sum_coWeight_mul_resolventReading_diag D hm

/-! ## 3. The pair currency of the resolvent chart -/

/-- **THE RESOLVENT PAIR MINOR.**  The second Sylvester minor of `1 - Pi` at a
pair of labels: the product of the two pivot deficits less the squared reading
across the pair.  It is the resolvent chart's analogue of
`Gtz.pairGapMinor`. -/
noncomputable def resolventPairMinor (D : WeightedDesign m k) (a b : Fin m) : ℝ :=
  (1 - resolventReading D a a) * (1 - resolventReading D b b)
    - (resolventReading D a b) ^ 2

theorem resolventPairMinor_comm (D : WeightedDesign m k) (hm : 2 ≤ m) (a b : Fin m) :
    resolventPairMinor D a b = resolventPairMinor D b a := by
  rw [resolventPairMinor, resolventPairMinor, resolventReading_symm D hm a b]
  ring

/-- **THE PAIR MINOR BUDGET OF THE RESOLVENT CHART.**  The co-weighted resolvent
pair minors total `(m - 1 - k)² - k`.  The product term factors through the
co-weighted pivot total, which is the rank, and the squared term is the budget
above.  At `(6,3)` the constant is `(5 - 3)² - 3 = 1`. -/
theorem sum_coWeight_resolventPairMinor (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ a, ∑ b, (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b
      = ((m : ℝ) - 1 - k) ^ 2 - k := by
  have hdeficit : ∑ a, (1 - D.weight a) * (1 - resolventReading D a a)
      = (m : ℝ) - 1 - k := by
    have hsplit : ∀ a : Fin m, (1 - D.weight a) * (1 - resolventReading D a a)
        = (1 - D.weight a) - (1 - D.weight a) * resolventReading D a a := fun a => by ring
    have hpiv : ∑ a, (1 - D.weight a) * resolventReading D a a = (k : ℝ) := by
      rw [Finset.sum_congr rfl fun a _ => by rw [resolventReading_diag]]
      exact descent_identity D hm
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sub_distrib,
      sum_one_sub_weight D, hpiv]
  have hrow : ∀ a : Fin m,
      (∑ b, (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b)
        = ((1 - D.weight a) * (1 - resolventReading D a a))
            * (∑ b, (1 - D.weight b) * (1 - resolventReading D b b))
          - ∑ b, (1 - D.weight a) * (1 - D.weight b) * (resolventReading D a b) ^ 2 := by
    intro a
    have hterm : ∀ b : Fin m,
        (1 - D.weight a) * (1 - D.weight b) * resolventPairMinor D a b
          = ((1 - D.weight a) * (1 - resolventReading D a a))
              * ((1 - D.weight b) * (1 - resolventReading D b b))
            - (1 - D.weight a) * (1 - D.weight b) * (resolventReading D a b) ^ 2 := by
      intro b; rw [resolventPairMinor]; ring
    rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hdeficit, sum_coWeight_sq_resolventReading D hm]
  ring

/-! ## 4. The first Sylvester sign is a count

Nothing analytic enters: the pivot deficits are paid for by one exact total. -/

/-- The contribution of a label to the descent budget: its co-weighted pivot plus
its own weight.  These are nonnegative and total `k + 1`. -/
theorem sum_pivotContribution (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, ((1 - D.weight c) * pivot D Finset.univ c + D.weight c) = (k : ℝ) + 1 := by
  rw [Finset.sum_add_distrib, descent_identity D hm, D.weight_sum_one]

/-- A label overspends its share of the budget exactly when its pivot passes
one. -/
theorem one_lt_pivotContribution_iff (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    1 < (1 - D.weight c) * pivot D Finset.univ c + D.weight c
      ↔ 1 < pivot D Finset.univ c := by
  have hw : 0 < 1 - D.weight c := by
    have := weight_lt_one D hm c; linarith
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    nlinarith [hw, hle]
  · intro h
    nlinarith [hw, h]

/-- **THE COUNT.**  At most `k` labels of a design have co-Parseval pivot above
one.  Each label's contribution to the descent budget is nonnegative, the total
is `k + 1`, and a pivot above one is exactly a contribution above one, so `k + 1`
such labels would overspend the whole budget. -/
theorem card_pivot_gt_one_le_rank (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (Finset.univ.filter fun c => 1 < pivot D Finset.univ c).card ≤ k := by
  classical
  set contribution : Fin m → ℝ :=
    fun c => (1 - D.weight c) * pivot D Finset.univ c + D.weight c with hcontrib
  set B := Finset.univ.filter fun c => 1 < pivot D Finset.univ c with hB
  have hnonneg : ∀ c : Fin m, 0 ≤ contribution c := by
    intro c
    have hw : 0 < 1 - D.weight c := by have := weight_lt_one D hm c; linarith
    have := pivot_univ_nonneg D hm c
    have := (D.weight_pos c).le
    positivity
  have hbig : ∀ c ∈ B, (1 : ℝ) < contribution c := by
    intro c hc
    rw [hB, Finset.mem_filter] at hc
    exact (one_lt_pivotContribution_iff D hm c).mpr hc.2
  by_contra hcon
  push_neg at hcon
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : ((B.card : ℝ)) < ∑ c ∈ B, contribution c := by
    have := Finset.sum_lt_sum_of_nonempty hne hbig
    simpa using this
  have hle : ∑ c ∈ B, contribution c ≤ (k : ℝ) + 1 := by
    rw [← sum_pivotContribution D hm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      fun c _ _ => hnonneg c
  have hcard : ((k : ℝ) + 1) ≤ (B.card : ℝ) := by
    have : (k : ℝ) + 1 ≤ (B.card : ℝ) := by exact_mod_cast hcon
    exact this
  linarith

/-- **AT LEAST `m - k` LABELS CLEAR THE FIRST SIGN.** -/
theorem rank_le_card_pivot_le_one (D : WeightedDesign m k) (hm : 2 ≤ m) :
    m - k ≤ (Finset.univ.filter fun c => pivot D Finset.univ c ≤ 1).card := by
  classical
  have hcompl : (Finset.univ.filter fun c => pivot D Finset.univ c ≤ 1)
      = (Finset.univ.filter fun c => 1 < pivot D Finset.univ c)ᶜ := by
    ext c; simp [not_lt]
  have hcard : (Finset.univ.filter fun c => pivot D Finset.univ c ≤ 1).card
      = m - (Finset.univ.filter fun c => 1 < pivot D Finset.univ c).card := by
    rw [hcompl, Finset.card_compl, Fintype.card_fin]
  have := card_pivot_gt_one_le_rank D hm
  omega

/-- **THE WINDOW FLOOR, FROM THE FIRST SIGN.**  When the size is at least twice
the rank the labels clearing the first Sylvester sign already fill a selection.
At `(6,3)` the count is three against a needed three -- exactly enough, and at
`(5,3)` it is two, which is not. -/
theorem exists_card_pivot_le_one (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hwindow : 2 * k ≤ m) :
    ∃ T : Finset (Fin m), T.card = k ∧ ∀ c ∈ T, pivot D Finset.univ c ≤ 1 := by
  classical
  have hcount := rank_le_card_pivot_le_one D hm
  obtain ⟨T, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ.filter fun c => pivot D Finset.univ c ≤ 1)
      (n := k) (by omega)
  refine ⟨T, hcard, fun c hc => ?_⟩
  have := hsub hc
  rw [Finset.mem_filter] at this
  exact this.2

/-! ## 5. The first two signs are necessary -/

/-- A principal one-by-one minor of the block: domination of a complement caps
each pivot of the selected labels at one. -/
theorem pivot_le_one_of_dominates_compl (D : WeightedDesign m k) (hm : 2 ≤ m)
    {S : Finset (Fin m)} (hdom : Dominates D Sᶜ) {a : Fin m} (ha : a ∈ S) :
    pivot D Finset.univ a ≤ 1 := by
  classical
  have hblock := (dominates_compl_iff_resolventForm_le D hm S).mp hdom
  have hone := hblock (fun c => if c = a then 1 else 0)
  have hleft : (∑ x ∈ S, ∑ b ∈ S,
      (if x = a then (1:ℝ) else 0) * (if b = a then (1:ℝ) else 0) * resolventReading D x b)
      = resolventReading D a a := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [hb]
      · intro hc; exact absurd ha hc
    · intro x _ hx; simp [hx]
    · intro hc; exact absurd ha hc
  have hright : (∑ x ∈ S, (if x = a then (1:ℝ) else 0) ^ 2) = 1 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro x _ hx; simp [hx]
    · intro hc; exact absurd ha hc
  rw [hleft, hright] at hone
  rwa [resolventReading_diag] at hone

/-- A probe supported on two labels reads a sum by those two terms alone. -/
theorem sum_two_point_probe {S : Finset (Fin m)} {a b : Fin m} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (alpha beta : ℝ) (f : Fin m → ℝ) :
    ∑ c ∈ S, (if c = a then alpha else if c = b then beta else 0) * f c
      = alpha * f a + beta * f b := by
  classical
  have hsub : ({a, b} : Finset (Fin m)) ⊆ S := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ha
    · rw [Finset.mem_singleton] at hc; subst hc; exact hb
  rw [← Finset.sum_subset hsub (fun c _ hc => ?_)]
  · rw [Finset.sum_pair hab]
    simp [hab, Ne.symm hab]
  · have hca : c ≠ a := fun h => hc (by simp [h])
    have hcb : c ≠ b := fun h => hc (by simp [h])
    simp [hca, hcb]

/-- **THE BINARY FORM OF A BLOCK.**  Domination of a complement makes the block's
quadratic form nonnegative at every probe supported on two of the selected
labels. -/
theorem block_binary_form_le (D : WeightedDesign m k) (hm : 2 ≤ m)
    {S : Finset (Fin m)} (hdom : Dominates D Sᶜ) {a b : Fin m}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (alpha beta : ℝ) :
    alpha ^ 2 * resolventReading D a a
        + 2 * alpha * beta * resolventReading D a b
        + beta ^ 2 * resolventReading D b b
      ≤ alpha ^ 2 + beta ^ 2 := by
  classical
  have hblock := (dominates_compl_iff_resolventForm_le D hm S).mp hdom
  have hy := hblock (fun c => if c = a then alpha else if c = b then beta else 0)
  set Y : Fin m → ℝ := fun c => if c = a then alpha else if c = b then beta else 0 with hY
  have hinner : ∀ x ∈ S, (∑ c ∈ S, Y x * Y c * resolventReading D x c)
      = Y x * (alpha * resolventReading D x a + beta * resolventReading D x b) := by
    intro x _
    have hassoc : ∀ c : Fin m, Y x * Y c * resolventReading D x c
        = Y x * (Y c * resolventReading D x c) := fun c => by ring
    rw [Finset.sum_congr rfl fun c _ => hassoc c, ← Finset.mul_sum,
      sum_two_point_probe ha hb hab alpha beta (fun c => resolventReading D x c)]
  rw [Finset.sum_congr rfl hinner,
    sum_two_point_probe ha hb hab alpha beta
      (fun x => alpha * resolventReading D x a + beta * resolventReading D x b)] at hy
  have hrhs : (∑ x ∈ S, (Y x) ^ 2) = alpha ^ 2 + beta ^ 2 := by
    have hsq : ∀ x : Fin m, (Y x) ^ 2 = Y x * Y x := fun x => by ring
    rw [Finset.sum_congr rfl fun x _ => hsq x,
      sum_two_point_probe ha hb hab alpha beta Y]
    simp [hY, Ne.symm hab]; ring
  rw [hrhs] at hy
  rw [resolventReading_symm D hm b a] at hy
  nlinarith [hy]

/-- **A PRINCIPAL TWO-BY-TWO MINOR OF THE BLOCK.**  Domination of a complement
makes every resolvent pair minor inside the selection nonnegative.  This is the
resolvent chart's counterpart of `Gtz.pairGapMinor_nonneg_of_dominates`, and it
is the second Sylvester sign. -/
theorem resolventPairMinor_nonneg_of_dominates_compl (D : WeightedDesign m k)
    (hm : 2 ≤ m) {S : Finset (Fin m)} (hdom : Dominates D Sᶜ) {a b : Fin m}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    0 ≤ resolventPairMinor D a b := by
  have hleading : 0 ≤ 1 - resolventReading D b b := by
    have := pivot_le_one_of_dominates_compl D hm hdom hb
    rw [resolventReading_diag]; linarith
  have hdisc := discriminant_le_of_quadratic_nonneg (leading := 1 - resolventReading D b b)
    (crossTerm := -resolventReading D a b) (constantTerm := 1 - resolventReading D a a)
    hleading (fun coordinate => by
      have := block_binary_form_le D hm hdom ha hb hab 1 coordinate
      nlinarith [this])
  rw [resolventPairMinor]
  nlinarith [hdisc]

/-! ## 6. The `(6,3)` reading -/

/-- **THE SEARCH AT `(6,3)` STARTS ALREADY INSIDE THE FIRST SIGN.**  Every design
of six labels and rank three carries a triple all of whose pivots are at most
one, and by `Gtz.card_pivot_gt_one_le_rank` at most three labels fail that test,
so the count is exact.  The remaining content of `GtzWeighted 6 3` is the second
and third Sylvester signs on such a triple. -/
theorem exists_triple_pivot_le_one_six_three (D : WeightedDesign 6 3) :
    ∃ T : Finset (Fin 6), T.card = 3 ∧ ∀ c ∈ T, pivot D Finset.univ c ≤ 1 :=
  exists_card_pivot_le_one D (by norm_num) (by norm_num)

/-- **THE `(6,3)` FRONTIER, WITH THE FIRST SIGN DISCHARGED.**  Weighted GTZ at
six labels and rank three holds if and only if every design carries a triple
which clears the first Sylvester sign of the resolvent chart AND whose whole
reading block sits below the identity.  The first conjunct is free by
`Gtz.exists_triple_pivot_le_one_six_three`; it is recorded here so that a
producer may assume it. -/
theorem gtzWeighted_six_three_iff_pivotSmall_resolventBlock :
    GtzWeighted 6 3
      ↔ ∀ D : WeightedDesign 6 3, ∃ S : Finset (Fin 6), S.card = 3 ∧
          (∀ c ∈ S, pivot D Finset.univ c ≤ 1) ∧
          ∀ y : Fin 6 → ℝ,
            (∑ a ∈ S, ∑ b ∈ S, y a * y b * resolventReading D a b)
              ≤ ∑ a ∈ S, (y a) ^ 2 := by
  rw [gtzWeighted_six_three_iff_resolventBlock]
  refine forall_congr' fun D => ⟨?_, ?_⟩
  · rintro ⟨S, hcard, hS⟩
    refine ⟨S, hcard, fun c hc => ?_, hS⟩
    exact pivot_le_one_of_dominates_compl D (by norm_num)
      ((dominates_compl_iff_resolventForm_le D (by norm_num) S).mpr hS) hc
  · rintro ⟨S, hcard, -, hS⟩
    exact ⟨S, hcard, hS⟩

end Gtz
