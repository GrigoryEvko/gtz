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

end Gtz
