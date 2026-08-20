/-
# The two-zero stratum at the erase anchor: the reading box of a `(5,3)` tie

The two-zero stratum (`K2`) of the corank-one arm has an inside atom equal to
`±w` at leverage one.  Erasing it leaves a strictly dominating complement
`F = univ ∖ x` with anchor `A = S_F − 1 ≻ 0` — with NO tie hypothesis
(`Gtz.complement_erase_posDef_of_leverage_le_one`).  At `(5,3)` the four
removals of `F` are EXACTLY the four triples of the stratum's avoiding-refusal
budget, so a tie pushes every removal reading to one and the whole stratum
onto a reading box.

## The box

At a `(5,3)` tie in the two-zero stratum:

* `Gtz.k2_fiveThree_removal_readings_ge_one` — all four erase readings satisfy
  `r_a = g_aᵀA⁻¹g_a ≥ 1`;
* `Gtz.k2_fiveThree_nullReading_ge_one` — the NULL DIRECTION reads at least
  one: `wᵀA⁻¹w ≥ 1`.  The coweighted budget
  `Σ_F (1−t_a) r_a − t_x·(g_xᵀA⁻¹g_x) = 3`
  (`Gtz.anchor_budget_identity` at `F = univ ∖ x`) has coefficient total
  `Σ_F (1−t_a) = 3 + t_x`, so the four readings at the floor force the `x`
  term up, and `g_x = ±w`;
* `Gtz.k2_fiveThree_traceInv_ge_one` — `tr A⁻¹ ≥ 1`, from the unweighted sum
  `Σ_F r_a = 3 + tr A⁻¹` (`Gtz.fourSet_reading_sum`).

## The kill target this box isolates

[MEASURED, `scratchpad/corank1/k2core.jl`: at every interior weight profile
the shape-minimizer of the max avoiding margin EQUALIZES all four removals
strictly dominating, with readings `0.95–0.997` and `wᵀA⁻¹w ∈ [0.20, 0.75]`.]
The box says a tie needs `wᵀA⁻¹w ≥ 1`; the measured stratum keeps it below
one.  The remaining kill is therefore ONE inequality — the null-reading
ceiling `wᵀA⁻¹w < 1` on the stratum — and by the rank-one Schur criterion it
is the positive definiteness of `S_univ − 1 − 2wwᵀ`, the full moment minus a
DOUBLED null atom.  The `(5,3)` case tree for that ceiling consumes the
`{y,z,d}` refusals through the `u`-split criterion and is the next brick; the
box below is its consumer.
-/
import Gtz.Wave.CorankOneGramMirror
import Gtz.Wave.AdjacentDominatorStress
import Gtz.Wave.FiveSetPairFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The erase anchor of the stratum -/

/-- **The two-zero stratum owns a strictly dominating erase complement.**  The
unit atom leaves `A = S_{univ∖x} − 1 ≻ 0`, with no tie hypothesis: the
stratum's leverage-one detector feeds the landed erase criterion. -/
theorem k2_erase_anchor_posDef (D : WeightedDesign m 3) (hm : 3 ≤ m)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    (subsetSum D ((Finset.univ : Finset (Fin m)).erase x) - 1).PosDef := by
  obtain ⟨hlev, -⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdominates hnull hunit hy hz
  have hlev' : D.atom x ⬝ᵥ D.atom x ≤ 1 := by
    rw [← leverageOf_eq_dotProduct, hlev]
  exact complement_erase_posDef_of_leverage_le_one D hm hlev'

/-! ## 2. The reading box at `(5,3)` -/

/-- **All four removal readings reach one.**  At a `(5,3)` tie in the two-zero
stratum, the four triples avoiding `x` are the four removals of the erase
four-set, and each refusal prices its atom's reading at one or more in the
anchor metric. -/
theorem k2_fiveThree_removal_readings_ge_one (D : WeightedDesign 5 3)
    (htie : IsTie D) {x y z : Fin 5} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 5)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 5)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    {a : Fin 5} (ha : a ∈ (Finset.univ : Finset (Fin 5)).erase x) :
    1 ≤ D.atom a ⬝ᵥ
      ((subsetSum D ((Finset.univ : Finset (Fin 5)).erase x) - 1)⁻¹ *ᵥ D.atom a) := by
  have hPD := k2_erase_anchor_posDef D (by norm_num) hxy hxz hyz hdominates
    hnull hunit hy hz
  have hcard : ((Finset.univ : Finset (Fin 5)).erase x).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  exact one_le_removal_reading_of_isTie D htie hcard hPD ha

/-- **The null direction reads at least one.**  The coweighted budget of the
erase anchor has coefficient total `3 + t_x` over the four removals, so four
readings at the floor push the `x` term to its own floor — and the `x` atom IS
the null direction up to sign. -/
theorem k2_fiveThree_nullReading_ge_one (D : WeightedDesign 5 3)
    (htie : IsTie D) {x y z : Fin 5} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 5)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 5)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    1 ≤ nullDir ⬝ᵥ
      ((subsetSum D ((Finset.univ : Finset (Fin 5)).erase x) - 1)⁻¹ *ᵥ nullDir) := by
  classical
  obtain ⟨-, hxw⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdominates hnull hunit hy hz
  have hPD := k2_erase_anchor_posDef D (by norm_num) hxy hxz hyz hdominates
    hnull hunit hy hz
  set F : Finset (Fin 5) := (Finset.univ : Finset (Fin 5)).erase x with hF
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  have hbudget := anchor_budget_identity D hPD
  have hcompl : Fᶜ = ({x} : Finset (Fin 5)) := by
    rw [hF]
    ext a
    simp [Finset.mem_compl, Finset.mem_erase]
  rw [hcompl, Finset.sum_singleton] at hbudget
  have hreadings : ∀ a ∈ F, 1 ≤ D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a) := fun a ha =>
    k2_fiveThree_removal_readings_ge_one D htie hxy hxz hyz hdominates hnull
      hunit hy hz ha
  have hcoeff : ∀ a ∈ F, (0 : ℝ) ≤ 1 - D.weight a := by
    intro a _
    have := weight_lt_one D (by norm_num : 2 ≤ 5) a
    linarith
  have hfloor : ∑ a ∈ F, (1 - D.weight a)
      ≤ ∑ a ∈ F, (1 - D.weight a) * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a)) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have h1 := hreadings a ha
    have h2 := hcoeff a ha
    nlinarith
  have hcardF : F.card = 4 := by
    rw [hF, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  have hsumt : ∑ a ∈ F, D.weight a = 1 - D.weight x := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 5)) D.weight
      (Finset.mem_univ x)
    rw [D.weight_sum_one] at hsplit
    rw [hF]
    linarith
  have hcoefftotal : ∑ a ∈ F, (1 - D.weight a) = 3 + D.weight x := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcardF, hsumt]
    ring
  have hxread : D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom x)
      = nullDir ⬝ᵥ (A⁻¹ *ᵥ nullDir) := by
    rcases hxw with hxw | hxw
    · rw [hxw]
    · rw [hxw]
      simp only [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  have htx := D.weight_pos x
  rw [hxread] at hbudget
  by_contra hcon
  push Not at hcon
  nlinarith [hbudget, hfloor, hcoefftotal]

/-- **The inverse-anchor trace reaches one.**  The unweighted reading sum of
the erase four-set is `3 + tr A⁻¹`, and four readings at the floor push the
trace to one. -/
theorem k2_fiveThree_traceInv_ge_one (D : WeightedDesign 5 3)
    (htie : IsTie D) {x y z : Fin 5} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 5)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 5)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    1 ≤ Matrix.trace (subsetSum D ((Finset.univ : Finset (Fin 5)).erase x) - 1)⁻¹ := by
  classical
  have hPD := k2_erase_anchor_posDef D (by norm_num) hxy hxz hyz hdominates
    hnull hunit hy hz
  set F : Finset (Fin 5) := (Finset.univ : Finset (Fin 5)).erase x with hF
  have hsum := fourSet_reading_sum D hPD
  have hreadings : ∀ a ∈ F, 1 ≤ D.atom a ⬝ᵥ
      ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a) := fun a ha =>
    k2_fiveThree_removal_readings_ge_one D htie hxy hxz hyz hdominates hnull
      hunit hy hz ha
  have hcardF : F.card = 4 := by
    rw [hF, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  have hfloor : (4 : ℝ) ≤ ∑ a ∈ F, D.atom a ⬝ᵥ
      ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a) := by
    calc (4 : ℝ) = ∑ _a ∈ F, (1 : ℝ) := by rw [Finset.sum_const, hcardF]; norm_num
      _ ≤ _ := Finset.sum_le_sum hreadings
  linarith [hsum ▸ hfloor]

/-- **THE KILL TARGET, isolated.**  If the null direction reads BELOW one in
the erase anchor of the two-zero stratum, the design is not a `(5,3)` tie.
The stratum's emptiness at `(5,3)` is exactly the ceiling `wᵀA⁻¹w < 1`, which
by the rank-one Schur criterion is the positive definiteness of the full
moment minus a doubled null atom. -/
theorem k2_fiveThree_not_isTie_of_nullReading_lt_one (D : WeightedDesign 5 3)
    {x y z : Fin 5} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 5)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 5)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    (hceiling : nullDir ⬝ᵥ
      ((subsetSum D ((Finset.univ : Finset (Fin 5)).erase x) - 1)⁻¹ *ᵥ nullDir) < 1) :
    ¬ IsTie D := by
  intro htie
  exact absurd (k2_fiveThree_nullReading_ge_one D htie hxy hxz hyz hdominates
    hnull hunit hy hz) (not_le.mpr hceiling)

/-! ## 3. The level-two ceiling and the balanced-weight `w`-mass floor -/

/-- **The level-two reading ceiling.**  A positive definite matrix that stays
above the identity reads every unit vector below one in its inverse:
`wᵀA⁻¹w = vᵀAv` at `v = A⁻¹w`, and `wᵀw − wᵀA⁻¹w = |Bv|² + vᵀBv > 0` with
`B = A − 1 ≻ 0`.  Spectral-free. -/
theorem reading_lt_one_of_posDef_sub_one {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef) (hsymm : Aᵀ = A)
    (hAI : (A - 1).PosDef) {w : Fin k → ℝ} (hunit : w ⬝ᵥ w = 1) :
    w ⬝ᵥ (A⁻¹ *ᵥ w) < 1 := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  set v : Fin k → ℝ := A⁻¹ *ᵥ w with hv
  have hAv : A *ᵥ v = w := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hAv
    rw [← hAv] at hunit
    simp at hunit
  set B : Matrix (Fin k) (Fin k) ℝ := A - 1 with hB
  have hBsymm : Bᵀ = B := by
    rw [hB, Matrix.transpose_sub, hsymm, Matrix.transpose_one]
  -- w ⬝ᵥ A⁻¹ w = v ⬝ᵥ A v  and  w ⬝ᵥ w = v ⬝ᵥ A² v
  have hcancel : A⁻¹ *ᵥ (A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hread : w ⬝ᵥ (A⁻¹ *ᵥ w) = v ⬝ᵥ (A *ᵥ v) := by
    conv_lhs => rw [← hAv, hcancel]
    exact dotProduct_comm _ _
  have hww : w ⬝ᵥ w = v ⬝ᵥ ((A * A) *ᵥ v) := by
    conv_lhs => rw [← hAv]
    rw [Matrix.dotProduct_mulVec (A *ᵥ v) A v,
      show (A *ᵥ v) ᵥ* A = A *ᵥ (A *ᵥ v) from by
        rw [← Matrix.mulVec_transpose, hsymm],
      Matrix.mulVec_mulVec]
    exact dotProduct_comm _ _
  have hsplit : A * A - A = B * B + B := by
    rw [hB]
    noncomm_ring
  have hgap : w ⬝ᵥ w - w ⬝ᵥ (A⁻¹ *ᵥ w)
      = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) + v ⬝ᵥ (B *ᵥ v) := by
    rw [hww, hread]
    have h1 : v ⬝ᵥ ((A * A) *ᵥ v) - v ⬝ᵥ (A *ᵥ v)
        = v ⬝ᵥ ((A * A - A) *ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    rw [h1, hsplit, Matrix.add_mulVec, dotProduct_add]
    congr 1
    rw [← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec v B (B *ᵥ v),
      show v ᵥ* B = B *ᵥ v from by rw [← Matrix.mulVec_transpose, hBsymm]]
  have hBv : 0 ≤ (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := dotProduct_self_nonneg _
  have hvBv : 0 < v ⬝ᵥ (B *ᵥ v) := by
    have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hAI).2 hvne
    rwa [star_trivial] at h
  have := hgap
  rw [hunit] at this
  linarith

/-- **The level-two erase dominator kills the stratum.**  If the erase four-set
of a `(5,3)` two-zero configuration dominates at level TWO — its gap stays
above the identity — the null reading stays below one and the design is not a
tie.  This closes Case I of the stratum; the measured chart never leaves it
(`scratchpad/corank1/k2case2.jl`: the level-two margin is positive at every
minimizer, and forcing it to zero blows the avoiding margins to `0.9`). -/
theorem k2_fiveThree_not_isTie_of_erase_levelTwo (D : WeightedDesign 5 3)
    {x y z : Fin 5} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 5)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 5)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    (hlevelTwo : ((subsetSum D ((Finset.univ : Finset (Fin 5)).erase x) - 1) - 1).PosDef) :
    ¬ IsTie D := by
  have hPD := k2_erase_anchor_posDef D (by norm_num) hxy hxz hyz hdominates
    hnull hunit hy hz
  refine k2_fiveThree_not_isTie_of_nullReading_lt_one D hxy hxz hyz hdominates
    hnull hunit hy hz ?_
  exact reading_lt_one_of_posDef_sub_one hPD
    (transpose_subsetSum_sub_one D _) hlevelTwo hunit

/-- **The balanced-weight `w`-mass floor.**  In the two-zero stratum at `(5,3)`
the unweighted outside null mass exceeds two whenever neither outside weight
dominates the other three non-`x` weights: `σ_w ≤ 2` forces
`t_d ≥ t_y + t_z + t_{d'}` for one of the two outside atoms.  Pure Parseval
and excess arithmetic — no refusals. -/
theorem k2_fiveThree_wMass_gt_two_of_balanced (D : WeightedDesign 5 3)
    {x y z : Fin 5} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 5)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 5)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    {d e : Fin 5} (hde : d ≠ e)
    (hdmem : d ∈ ({x, y, z} : Finset (Fin 5))ᶜ) (hemem : e ∈ ({x, y, z} : Finset (Fin 5))ᶜ)
    (hbal_d : D.weight d < D.weight y + D.weight z + D.weight e)
    (hbal_e : D.weight e < D.weight y + D.weight z + D.weight d) :
    2 < (D.atom d ⬝ᵥ nullDir) ^ 2 + (D.atom e ⬝ᵥ nullDir) ^ 2 := by
  classical
  -- the excess identity over the two-atom complement
  have hcompl : ({x, y, z} : Finset (Fin 5))ᶜ = {d, e} := by
    have hcard : (({x, y, z} : Finset (Fin 5))ᶜ).card = 2 := by
      rw [Finset.card_compl, Fintype.card_fin]
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    have hsub : ({d, e} : Finset (Fin 5)) ⊆ ({x, y, z} : Finset (Fin 5))ᶜ := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact hdmem
      · rw [Finset.mem_singleton.mp ha']
        exact hemem
    have hcard2 : ({d, e} : Finset (Fin 5)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])).symm
  have hexcess := k2_outside_excess_total D hxy hxz hyz hdominates hnull hunit hy hz
  rw [hcompl, Finset.sum_insert (by simp [hde]), Finset.sum_singleton] at hexcess
  set ed : ℝ := (D.atom d ⬝ᵥ nullDir) ^ 2 - 1 with hed
  set ee : ℝ := (D.atom e ⬝ᵥ nullDir) ^ 2 - 1 with hee
  have hedge : ed ≥ -1 := by rw [hed]; nlinarith [sq_nonneg (D.atom d ⬝ᵥ nullDir)]
  have heege : ee ≥ -1 := by rw [hee]; nlinarith [sq_nonneg (D.atom e ⬝ᵥ nullDir)]
  have hsum : D.weight d * ed + D.weight e * ee = D.weight y + D.weight z := by
    rw [hed, hee]
    linarith [hexcess]
  by_contra hcon
  push Not at hcon
  have hsig : ed + ee ≤ 0 := by rw [hed, hee]; linarith
  have hty := D.weight_pos y
  have htz := D.weight_pos z
  have htd := D.weight_pos d
  have hte := D.weight_pos e
  -- one excess is positive, the other bounded by it; the weight balance fails
  rcases le_or_gt ed 0 with hed0 | hed0
  · -- then ee carries the excess: t_e·ee ≥ t_y+t_z − t_d·ed ≥ t_y+t_z + t_d·(−ed)
    have heepos : 0 < ee := by nlinarith
    have hchain : D.weight e * (ed + ee) + (D.weight e - D.weight d) * (-ed)
        = D.weight y + D.weight z := by ring_nf; nlinarith [hsum]
    nlinarith [hchain, hsig, mul_nonneg (le_of_lt hte) (neg_nonneg.mpr hed0)]
  · have hee0 : ee ≤ 0 := by nlinarith
    have hchain : D.weight d * (ed + ee) + (D.weight d - D.weight e) * (-ee)
        = D.weight y + D.weight z := by ring_nf; nlinarith [hsum]
    nlinarith [hchain, hsig, mul_nonneg (le_of_lt htd) (neg_nonneg.mpr hee0)]

/-! ## 4. The `w`-parallel corner of the stratum -/

/-- **A `w`-parallel outside atom above the null budget kills the stratum.**
If some atom is a multiple `c·w` of the null direction with `c² > 1`, the
triple of the two silenced atoms and that atom dominates STRICTLY: the
`w`-component pays `c² − 1 > 0` and the silenced pair pays the plane strictly,
by corank one.  This is the exact-parallel slice of Case II [MEASURED,
`scratchpad/corank1/k2case2.jl`: forcing `λmin(S_F)` toward `2` collapses an
outside atom onto the `w`-line and this triple's margin blows to `+0.98`].
The conclusion refutes the TIE, not the design: the corner is a legal design
with a parallel pair `(x, d)`. -/
theorem k2_not_isTie_of_outside_parallel_nullDir (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0)
    {d : Fin m} (hdy : y ≠ d) (hdz : z ≠ d)
    {c : ℝ} (hpar : D.atom d = c • nullDir) (hc : 1 < c ^ 2) :
    ¬ IsTie D := by
  classical
  obtain ⟨-, hxw⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdominates hline.2.1 hunit hy hz
  intro htie
  have hcard : ({y, z, d} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hyz, hdy]),
      Finset.card_insert_of_notMem (by simp [hdz]), Finset.card_singleton]
  refine htie.2 ({y, z, d} : Finset (Fin m)) hcard ?_
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _),
      fun ξ hξ => ?_⟩
  rw [star_trivial, dominationGap_form,
    sum_over_triple (fun a => (D.atom a ⬝ᵥ ξ) ^ 2) hyz hdy hdz]
  set γ : ℝ := nullDir ⬝ᵥ ξ with hγ
  set ξb : Fin 3 → ℝ := ξ - γ • nullDir with hξb
  have hwperp : nullDir ⬝ᵥ ξb = 0 := by
    rw [hξb, dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit, mul_one, hγ]
    ring
  have hyread : D.atom y ⬝ᵥ ξ = D.atom y ⬝ᵥ ξb := by
    rw [hξb, dotProduct_sub, dotProduct_smul, smul_eq_mul, hy, mul_zero, sub_zero]
  have hzread : D.atom z ⬝ᵥ ξ = D.atom z ⬝ᵥ ξb := by
    rw [hξb, dotProduct_sub, dotProduct_smul, smul_eq_mul, hz, mul_zero, sub_zero]
  have hdread : D.atom d ⬝ᵥ ξ = c * γ := by
    rw [hpar, smul_dotProduct, smul_eq_mul, hγ]
  have hnorm : ξb ⬝ᵥ ξb = ξ ⬝ᵥ ξ - γ ^ 2 := by
    rw [hξb]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hunit]
    rw [dotProduct_comm ξ nullDir]
    ring
  by_cases hb : ξb = 0
  · have hxiw : ξ = γ • nullDir := by
      have := hξb ▸ hb
      rwa [sub_eq_zero] at this
    have hγne : γ ≠ 0 := by
      intro h0
      exact hξ (by rw [hxiw, h0, zero_smul])
    have hyz0 : D.atom y ⬝ᵥ ξ = 0 := by rw [hyread, hb, dotProduct_zero]
    have hzz0 : D.atom z ⬝ᵥ ξ = 0 := by rw [hzread, hb, dotProduct_zero]
    have hnn : ξ ⬝ᵥ ξ = γ ^ 2 := by
      have := hnorm
      rw [hb] at this
      simp only [dotProduct_zero, zero_dotProduct] at this
      linarith [this]
    rw [hyz0, hzz0, hdread, hnn]
    have hγsq : 0 < γ ^ 2 := by positivity
    nlinarith [hc, hγsq]
  · have hoff : ∀ s : ℝ, ξb ≠ s • nullDir := by
      intro s hs
      have hdot := congrArg (fun v => nullDir ⬝ᵥ v) hs
      simp only [dotProduct_smul, smul_eq_mul, hunit, mul_one] at hdot
      rw [hwperp] at hdot
      rw [hs, ← hdot, zero_smul] at hb
      exact hb rfl
    have hgap := gapForm_pos_of_gapNullLine D ({x, y, z} : Finset (Fin m))
      hline hdominates hoff
    rw [dominationGap_form,
      sum_over_triple (fun a => (D.atom a ⬝ᵥ ξb) ^ 2) hxy hxz hyz] at hgap
    have hxb : D.atom x ⬝ᵥ ξb = 0 := by
      rcases hxw with hxw | hxw <;> rw [hxw]
      · exact hwperp
      · rw [neg_dotProduct, hwperp, neg_zero]
    rw [hxb] at hgap
    rw [hyread, hzread, hdread]
    have hplane : 0 < (D.atom y ⬝ᵥ ξb) ^ 2 + (D.atom z ⬝ᵥ ξb) ^ 2 - ξb ⬝ᵥ ξb := by
      nlinarith [hgap]
    nlinarith [hplane, hnorm, sq_nonneg γ, hc, sq_nonneg (c * γ),
      mul_nonneg (le_of_lt (lt_trans one_pos hc)) (sq_nonneg γ)]

end Gtz
